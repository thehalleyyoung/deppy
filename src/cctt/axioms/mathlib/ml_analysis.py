"""Mathlib: Analysis — auto-generated from Mathlib4.

Contains 400 rewrite rules derived from Mathlib theorems.
Plus 2888 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_analysis"
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

def _r0000_unique(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: HasDerivAt.unique
    # f₀' = f₁'
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_0_prime")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f_1_prime")
            results.append((rhs, "Mathlib: HasDerivAt_unique"))
    except Exception:
        pass
    return results


def _r0001_inner_fourier_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Lp.inner_fourier_eq
    # ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("f", (args[2],))
            results.append((rhs, "Mathlib: MeasureTheory_Lp_inner_fourier_eq"))
        except Exception:
            pass
    return results


def _r0002_zero_mlconvolution(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.zero_mlconvolution
    # 0 ⋆ₘₗ[μ] f = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_zero_mlconvolution"))
        except Exception:
            pass
    return results


def _r0003_mlconvolution_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.mlconvolution_zero
    # f ⋆ₘₗ[μ] 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_mlconvolution_zero"))
        except Exception:
            pass
    return results


def _r0004_expSeries_apply_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NormedSpace.expSeries_apply_eq
    # (expSeries 𝕂 𝔸 n fun _ => x) = (n !⁻¹ : 𝕂) • x ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "expSeries", 7)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("n_banginv_colon", (args[4], args[6],)), args[2]))
            results.append((rhs, "Mathlib: NormedSpace_expSeries_apply_eq"))
        except Exception:
            pass
    return results


def _r0005_coe_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NormedAddGroupHom.coe_mk
    # ⇑(⟨f, h₁, h₂, h₃⟩ : NormedAddGroupHom V₁ V₂) = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_h_1_h_2_h_3_colon_NormedAddGroupHom_V_1_V_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: NormedAddGroupHom_coe_mk"))
    except Exception:
        pass
    return results


def _r0006_add_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NormedAddGroupHom.add_apply
    # (f + g) v = f v + g v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_plus_g", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("f", (args[0],)), OOp("g", (args[0],))))
            results.append((rhs, "Mathlib: NormedAddGroupHom_add_apply"))
        except Exception:
            pass
    return results


def _r0007_zero_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NormedAddGroupHom.zero_apply
    # (0 : NormedAddGroupHom V₁ V₂) v = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_NormedAddGroupHom_V_1_V_2", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: NormedAddGroupHom_zero_apply"))
        except Exception:
            pass
    return results


def _r0008_neg_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NormedAddGroupHom.neg_apply
    # (-f : NormedAddGroupHom V₁ V₂) v = -f v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minus_f_colon_NormedAddGroupHom_V_1_V_2", 1)
    if args is not None:
        try:
            rhs = OOp("minus_f", (args[0],))
            results.append((rhs, "Mathlib: NormedAddGroupHom_neg_apply"))
        except Exception:
            pass
    return results


def _r0009_sub_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NormedAddGroupHom.sub_apply
    # (f - g : NormedAddGroupHom V₁ V₂) v = f v - g v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_minus_g_colon_NormedAddGroupHom_V_1_V_2", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("f", (args[0],)), OOp("g", (args[0],))))
            results.append((rhs, "Mathlib: NormedAddGroupHom_sub_apply"))
        except Exception:
            pass
    return results


def _r0010_smul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NormedAddGroupHom.smul_apply
    # (r • f) v = r • f v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "r_f", 1)
    if args is not None:
        try:
            rhs = OOp("r", (OVar("_unknown"), OVar("f"), args[0],))
            results.append((rhs, "Mathlib: NormedAddGroupHom_smul_apply"))
        except Exception:
            pass
    return results


def _r0011_completion_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NormedAddGroupHom.completion_coe
    # f.completion g = f g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_completion", 1)
    if args is not None:
        try:
            rhs = OOp("f", (args[0],))
            results.append((rhs, "Mathlib: NormedAddGroupHom_completion_coe"))
        except Exception:
            pass
    return results


def _r0012_norm_completion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NormedAddGroupHom.norm_completion
    # ‖f.completion‖ = ‖f‖
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_completion")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: NormedAddGroupHom_norm_completion"))
    except Exception:
        pass
    return results


def _r0013_inclusionInDoubleDual_norm_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NormedSpace.inclusionInDoubleDual_norm_eq
    # ‖inclusionInDoubleDual 𝕜 E‖ = ‖ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 E)‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inclusionInDoubleDual", 2)
    if args is not None:
        try:
            rhs = OOp("ContinuousLinearMap_id", (args[0], OVar("StrongDual_E"),))
            results.append((rhs, "Mathlib: NormedSpace_inclusionInDoubleDual_norm_eq"))
        except Exception:
            pass
    return results


def _r0014_normalize_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NormedSpace.normalize_eq_zero_iff
    # normalize x = 0 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "normalize", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: NormedSpace_normalize_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0015_norm_smul_normalize(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NormedSpace.norm_smul_normalize
    # ‖x‖ • normalize x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: NormedSpace_norm_smul_normalize"))
        except Exception:
            pass
    return results


def _r0016_norm_normalize_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NormedSpace.norm_normalize_eq_one_iff
    # ‖normalize x‖ = 1 ↔ x ≠ 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "normalize", 1)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("iff", (OLit(1), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: NormedSpace_norm_normalize_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0017_normalize_smul_of_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NormedSpace.normalize_smul_of_pos
    # normalize (r • x) = normalize x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "normalize", 1)
    if args is not None:
        try:
            rhs = OOp("normalize", (OVar("x"),))
            results.append((rhs, "Mathlib: NormedSpace_normalize_smul_of_pos"))
        except Exception:
            pass
    return results


def _r0018_enorm_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.enorm_eq
    # ‖(x : ℝ)‖ₑ = x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x")
            results.append((rhs, "Mathlib: NNReal_enorm_eq"))
    except Exception:
        pass
    return results


def _r0019_agmSequences_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.agmSequences_succ
    # agmSequences x y (n + 1) = agmSequences (sqrt (x * y)) ((x + y) / 2) n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "agmSequences", 3)
    if args is not None:
        try:
            rhs = OOp("agmSequences", (OOp("sqrt", (OOp("*", (args[0], args[1])),)), OOp("//", (OOp("+", (args[0], args[1])), OLit(2))), OVar("n"),))
            results.append((rhs, "Mathlib: NNReal_agmSequences_succ"))
        except Exception:
            pass
    return results


def _r0020_log_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.log_one
    # log 1 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ENNReal_log_one"))
        except Exception:
            pass
    return results


def _r0021_log_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.log_top
    # log ⊤ = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ENNReal_log_top"))
        except Exception:
            pass
    return results


def _r0022_log_ofReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.log_ofReal
    # log (ENNReal.ofReal x) = if x ≤ 0 then ⊥ else ↑(Real.log x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 1)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("if", (OVar("x"),)), OOp("_0", (OVar("then"), OVar("bot"), OVar("else"), OVar("Real_log_x"),))))
            results.append((rhs, "Mathlib: ENNReal_log_ofReal"))
        except Exception:
            pass
    return results


def _r0023_logOrderIso_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.logOrderIso_symm
    # logOrderIso.symm = expOrderIso
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("logOrderIso_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("expOrderIso")
            results.append((rhs, "Mathlib: ENNReal_logOrderIso_symm"))
    except Exception:
        pass
    return results


def _r0024_expOrderIso_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: EReal.expOrderIso_symm
    # expOrderIso.symm = logOrderIso
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("expOrderIso_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("logOrderIso")
            results.append((rhs, "Mathlib: EReal_expOrderIso_symm"))
    except Exception:
        pass
    return results


def _r0025_coe_rpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.coe_rpow
    # ((x ^ y : ℝ≥0) : ℝ) = (x : ℝ) ^ y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_pow_y_colon_ge_0", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("x", (args[0], args[1],)), OVar("y")))
            results.append((rhs, "Mathlib: NNReal_coe_rpow"))
        except Exception:
            pass
    return results


def _r0026_rpow_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.rpow_zero
    # x ^ (0 : ℝ) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: NNReal_rpow_zero"))
        except Exception:
            pass
    return results


def _r0027_zero_rpow_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.zero_rpow_def
    # (0 : ℝ≥0) ^ y = if y = 0 then 1 else 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (args[1],)), OOp("_0", (OVar("then"), OLit(1), OVar("else"), OLit(0),))))
            results.append((rhs, "Mathlib: NNReal_zero_rpow_def"))
        except Exception:
            pass
    return results


def _r0028_rpow_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.rpow_neg
    # x ^ (-y) = (x ^ y)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("x_pow_y_inv")
            results.append((rhs, "Mathlib: NNReal_rpow_neg"))
        except Exception:
            pass
    return results


def _r0029_rpow_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.rpow_intCast
    # x ^ (n : ℝ) = x ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], OVar("n")))
            results.append((rhs, "Mathlib: NNReal_rpow_intCast"))
        except Exception:
            pass
    return results


def _r0030_rpow_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.rpow_add
    # x ^ (y + z) = x ^ y * x ^ z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (args[0], OVar("y"))), OOp("**", (args[0], OVar("z")))))
            results.append((rhs, "Mathlib: NNReal_rpow_add"))
        except Exception:
            pass
    return results


def _r0031_rpow_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.rpow_zero
    # x ^ (0 : ℝ) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ENNReal_rpow_zero"))
        except Exception:
            pass
    return results


def _r0032_top_rpow_of_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.top_rpow_of_neg
    # (⊤ : ℝ≥0∞) ^ y = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ENNReal_top_rpow_of_neg"))
        except Exception:
            pass
    return results


def _r0033_zero_rpow_of_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.zero_rpow_of_pos
    # (0 : ℝ≥0∞) ^ y = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ENNReal_zero_rpow_of_pos"))
        except Exception:
            pass
    return results


def _r0034_rpow_inv_rpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.rpow_inv_rpow
    # (x ^ y⁻¹) ^ y = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: ENNReal_rpow_inv_rpow"))
        except Exception:
            pass
    return results


def _r0035_rpow_rpow_inv_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.rpow_rpow_inv_eq_iff
    # (x ^ y) ^ y⁻¹ = x ↔ y ≠ 0 ∨ x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("!=", (OOp("iff", (OVar("x"), OVar("y"))), OOp("or", (OLit(0), OVar("x"))))), OLit(1)))
            results.append((rhs, "Mathlib: ENNReal_rpow_rpow_inv_eq_iff"))
        except Exception:
            pass
    return results


def _r0036_rpow_inv_rpow_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.rpow_inv_rpow_eq_iff
    # (x ^ y⁻¹) ^ y = x ↔ y ≠ 0 ∨ x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("!=", (OOp("iff", (OVar("x"), args[1])), OOp("or", (OLit(0), OVar("x"))))), OLit(1)))
            results.append((rhs, "Mathlib: ENNReal_rpow_inv_rpow_eq_iff"))
        except Exception:
            pass
    return results


def _r0037_pow_rpow_inv_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.pow_rpow_inv_natCast
    # (x ^ n) ^ (n⁻¹ : ℝ) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: ENNReal_pow_rpow_inv_natCast"))
        except Exception:
            pass
    return results


def _r0038_some_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.some_eq_coe
    # (Option.some a : ℝ≥0∞) = (↑a : ℝ≥0∞)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "some", 3)
    if args is not None:
        try:
            rhs = OOp("a", (args[1], args[2],))
            results.append((rhs, "Mathlib: ENNReal_some_eq_coe"))
        except Exception:
            pass
    return results


def _r0039_coe_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_inj
    # (p : ℝ≥0∞) = q ↔ p = q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("q"), OVar("p"))), OVar("q")))
            results.append((rhs, "Mathlib: ENNReal_coe_inj"))
        except Exception:
            pass
    return results


def _r0040_coe_toNNReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_toNNReal
    # ∀ {a : ℝ≥0∞}, a ≠ ∞ → ↑a.toNNReal = a   | ofNNReal _, _ => rfl   | ⊤, h => (h rfl).elim  @[simp] theorem coe_comp_toNNRe
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("x_colon_ge_0inf_comp_ENNReal_toNNReal_comp_f_eq_f"),))
            results.append((rhs, "Mathlib: ENNReal_coe_toNNReal"))
        except Exception:
            pass
    return results


def _r0041_toReal_ofReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.toReal_ofReal
    # (ENNReal.ofReal r).toReal = r
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ENNReal_ofReal_r_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("r")
            results.append((rhs, "Mathlib: ENNReal_toReal_ofReal"))
    except Exception:
        pass
    return results


def _r0042_coe_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_zero
    # ↑(0 : ℝ≥0) = (0 : ℝ≥0∞)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_ge_0")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_0", (OVar("colon"), OVar("ge_0inf"),))
            results.append((rhs, "Mathlib: ENNReal_coe_zero"))
    except Exception:
        pass
    return results


def _r0043_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_one
    # ↑(1 : ℝ≥0) = (1 : ℝ≥0∞)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_ge_0")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_1", (OVar("colon"), OVar("ge_0inf"),))
            results.append((rhs, "Mathlib: ENNReal_coe_one"))
    except Exception:
        pass
    return results


def _r0044_coe_toNNReal_eq_toReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_toNNReal_eq_toReal
    # (z.toNNReal : ℝ) = z.toReal
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "z_toNNReal", 2)
    if args is not None:
        try:
            rhs = OVar("z_toReal")
            results.append((rhs, "Mathlib: ENNReal_coe_toNNReal_eq_toReal"))
        except Exception:
            pass
    return results


def _r0045_toNNReal_toReal_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.toNNReal_toReal_eq
    # z.toReal.toNNReal = z.toNNReal
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z_toReal_toNNReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("z_toNNReal")
            results.append((rhs, "Mathlib: ENNReal_toNNReal_toReal_eq"))
    except Exception:
        pass
    return results


def _r0046_toNNReal_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.toNNReal_top
    # ∞.toNNReal = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("inf_toNNReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ENNReal_toNNReal_top"))
    except Exception:
        pass
    return results


def _r0047_toReal_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.toReal_top
    # ∞.toReal = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("inf_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ENNReal_toReal_top"))
    except Exception:
        pass
    return results


def _r0048_toReal_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.toReal_one
    # (1 : ℝ≥0∞).toReal = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_ge_0inf_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ENNReal_toReal_one"))
    except Exception:
        pass
    return results


def _r0049_toNNReal_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.toNNReal_one
    # (1 : ℝ≥0∞).toNNReal = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_ge_0inf_toNNReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ENNReal_toNNReal_one"))
    except Exception:
        pass
    return results


def _r0050_coe_toReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_toReal
    # (r : ℝ≥0∞).toReal = r
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r_colon_ge_0inf_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("r")
            results.append((rhs, "Mathlib: ENNReal_coe_toReal"))
    except Exception:
        pass
    return results


def _r0051_toNNReal_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.toNNReal_zero
    # (0 : ℝ≥0∞).toNNReal = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_ge_0inf_toNNReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ENNReal_toNNReal_zero"))
    except Exception:
        pass
    return results


def _r0052_toReal_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.toReal_zero
    # (0 : ℝ≥0∞).toReal = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_ge_0inf_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ENNReal_toReal_zero"))
    except Exception:
        pass
    return results


def _r0053_ofReal_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofReal_zero
    # ENNReal.ofReal (0 : ℝ) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ENNReal_ofReal", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ENNReal_ofReal_zero"))
        except Exception:
            pass
    return results


def _r0054_ofReal_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofReal_one
    # ENNReal.ofReal (1 : ℝ) = (1 : ℝ≥0∞)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ENNReal_ofReal", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("colon"), OVar("ge_0inf"),))
            results.append((rhs, "Mathlib: ENNReal_ofReal_one"))
        except Exception:
            pass
    return results


def _r0055_ofReal_toReal_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofReal_toReal_eq_iff
    # ENNReal.ofReal a.toReal = a ↔ a ≠ ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ENNReal_ofReal", 1)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("iff", (OVar("a"), OVar("a"))), OVar("top")))
            results.append((rhs, "Mathlib: ENNReal_ofReal_toReal_eq_iff"))
        except Exception:
            pass
    return results


def _r0056_zero_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.zero_eq_coe
    # 0 = (↑r : ℝ≥0∞) ↔ 0 = r
    results: List[Tuple[OTerm, str]] = []
    if _is_lit(term, 0):
        try:
            rhs = OOp("==", (OOp("iff", (OOp("r", (OVar("colon"), OVar("ge_0inf"),)), OLit(0))), OVar("r")))
            results.append((rhs, "Mathlib: ENNReal_zero_eq_coe"))
        except Exception:
            pass
    return results


def _r0057_coe_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_eq_one
    # (↑r : ℝ≥0∞) = 1 ↔ r = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "r", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), OVar("r"))), OLit(1)))
            results.append((rhs, "Mathlib: ENNReal_coe_eq_one"))
        except Exception:
            pass
    return results


def _r0058_one_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.one_eq_coe
    # 1 = (↑r : ℝ≥0∞) ↔ 1 = r
    results: List[Tuple[OTerm, str]] = []
    if _is_lit(term, 1):
        try:
            rhs = OOp("==", (OOp("iff", (OOp("r", (OVar("colon"), OVar("ge_0inf"),)), OLit(1))), OVar("r")))
            results.append((rhs, "Mathlib: ENNReal_one_eq_coe"))
        except Exception:
            pass
    return results


def _r0059_coe_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_mul
    # (↑(x * y) : ℝ≥0∞) = x * y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_star_y", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("x"), OVar("y")))
            results.append((rhs, "Mathlib: ENNReal_coe_mul"))
        except Exception:
            pass
    return results


def _r0060_coe_nsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_nsmul
    # (↑(n • x) : ℝ≥0∞) = n • x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n_x", 2)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("_unknown"), OVar("x"),))
            results.append((rhs, "Mathlib: ENNReal_coe_nsmul"))
        except Exception:
            pass
    return results


def _r0061_coe_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_pow
    # (↑(x ^ n) : ℝ≥0∞) = x ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_pow_n", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("x"), OVar("n")))
            results.append((rhs, "Mathlib: ENNReal_coe_pow"))
        except Exception:
            pass
    return results


def _r0062_coe_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_ofNat
    # ((ofNat(n) : ℝ≥0) : ℝ≥0∞) = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofNat_n_colon_ge_0", 2)
    if args is not None:
        try:
            rhs = OVar("ofNat_n")
            results.append((rhs, "Mathlib: ENNReal_coe_ofNat"))
        except Exception:
            pass
    return results


def _r0063_bot_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.bot_eq_zero
    # (⊥ : ℝ≥0∞) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bot", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ENNReal_bot_eq_zero"))
        except Exception:
            pass
    return results


def _r0064_coe_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_natCast
    # ((n : ℝ≥0) : ℝ≥0∞) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n_colon_ge_0", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: ENNReal_coe_natCast"))
        except Exception:
            pass
    return results


def _r0065_ofReal_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofReal_natCast
    # ENNReal.ofReal n = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ENNReal_ofReal", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ENNReal_ofReal_natCast"))
        except Exception:
            pass
    return results


def _r0066_ofReal_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofReal_ofNat
    # ENNReal.ofReal ofNat(n) = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ENNReal_ofReal", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ENNReal_ofReal_ofNat"))
        except Exception:
            pass
    return results


def _r0067_ofNNReal_add_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofNNReal_add_natCast
    # ofNNReal (r + n) = r + n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofNNReal", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("r"), OVar("n")))
            results.append((rhs, "Mathlib: ENNReal_ofNNReal_add_natCast"))
        except Exception:
            pass
    return results


def _r0068_ofNNReal_natCast_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofNNReal_natCast_add
    # ofNNReal (n + r) = n + r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofNNReal", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("n"), OVar("r")))
            results.append((rhs, "Mathlib: ENNReal_ofNNReal_natCast_add"))
        except Exception:
            pass
    return results


def _r0069_ofNNReal_sub_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofNNReal_sub_natCast
    # ofNNReal (r - n) = r - n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofNNReal", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OVar("r"), OVar("n")))
            results.append((rhs, "Mathlib: ENNReal_ofNNReal_sub_natCast"))
        except Exception:
            pass
    return results


def _r0070_ofNNReal_natCast_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofNNReal_natCast_sub
    # ofNNReal (n - r) = n - r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofNNReal", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OVar("n"), OVar("r")))
            results.append((rhs, "Mathlib: ENNReal_ofNNReal_natCast_sub"))
        except Exception:
            pass
    return results


def _r0071_toNNReal_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.toNNReal_natCast
    # (n : ℝ≥0∞).toNNReal = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_colon_ge_0inf_toNNReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: ENNReal_toNNReal_natCast"))
    except Exception:
        pass
    return results


def _r0072_toNNReal_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.toNNReal_ofNat
    # ENNReal.toNNReal ofNat(n) = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ENNReal_toNNReal", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ENNReal_toNNReal_ofNat"))
        except Exception:
            pass
    return results


def _r0073_toReal_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.toReal_ofNat
    # ENNReal.toReal ofNat(n) = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ENNReal_toReal", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ENNReal_toReal_ofNat"))
        except Exception:
            pass
    return results


def _r0074_toNNReal_natCast_eq_toNNReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.toNNReal_natCast_eq_toNNReal
    # (n : ℝ≥0∞).toNNReal = (n : ℝ).toNNReal
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_colon_ge_0inf_toNNReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n_colon_toNNReal")
            results.append((rhs, "Mathlib: ENNReal_toNNReal_natCast_eq_toNNReal"))
    except Exception:
        pass
    return results


def _r0075_min_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.min_eq_zero_iff
    # min a b = 0 ↔ a = 0 ∨ b = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "min", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OOp("==", (OOp("or", (OLit(0), args[1])), OLit(0)))))
            results.append((rhs, "Mathlib: ENNReal_min_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0076_max_zero_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.max_zero_left
    # max 0 a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "max", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: ENNReal_max_zero_left"))
        except Exception:
            pass
    return results


def _r0077_iUnion_Ioo_coe_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.iUnion_Ioo_coe_nat
    # ⋃ n : ℕ, Ioo a n = Ioi a \\ {∞}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 6)
    if args is not None:
        try:
            rhs = OOp("Ioi", (args[4], OVar("bsl"), OVar("inf"),))
            results.append((rhs, "Mathlib: ENNReal_iUnion_Ioo_coe_nat"))
        except Exception:
            pass
    return results


def _r0078_iUnion_Icc_coe_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.iUnion_Icc_coe_nat
    # ⋃ n : ℕ, Icc a n = Ici a \\ {∞}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 6)
    if args is not None:
        try:
            rhs = OOp("Ici", (args[4], OVar("bsl"), OVar("inf"),))
            results.append((rhs, "Mathlib: ENNReal_iUnion_Icc_coe_nat"))
        except Exception:
            pass
    return results


def _r0079_iUnion_Ico_coe_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.iUnion_Ico_coe_nat
    # ⋃ n : ℕ, Ico a n = Ici a \\ {∞}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 6)
    if args is not None:
        try:
            rhs = OOp("Ici", (args[4], OVar("bsl"), OVar("inf"),))
            results.append((rhs, "Mathlib: ENNReal_iUnion_Ico_coe_nat"))
        except Exception:
            pass
    return results


def _r0080_iInter_Ici_coe_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.iInter_Ici_coe_nat
    # ⋂ n : ℕ, Ici (n : ℝ≥0∞) = {∞}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 5)
    if args is not None:
        try:
            rhs = OVar("inf")
            results.append((rhs, "Mathlib: ENNReal_iInter_Ici_coe_nat"))
        except Exception:
            pass
    return results


def _r0081_iInter_Ioi_coe_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.iInter_Ioi_coe_nat
    # ⋂ n : ℕ, Ioi (n : ℝ≥0∞) = {∞}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 5)
    if args is not None:
        try:
            rhs = OVar("inf")
            results.append((rhs, "Mathlib: ENNReal_iInter_Ioi_coe_nat"))
        except Exception:
            pass
    return results


def _r0082_coe_min(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_min
    # ((min r p : ℝ≥0) : ℝ≥0∞) = min (r : ℝ≥0∞) p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "min_r_p_colon_ge_0", 2)
    if args is not None:
        try:
            rhs = OOp("min", (OOp("r", (args[0], args[1],)), OVar("p"),))
            results.append((rhs, "Mathlib: ENNReal_coe_min"))
        except Exception:
            pass
    return results


def _r0083_coe_max(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_max
    # ((max r p : ℝ≥0) : ℝ≥0∞) = max (r : ℝ≥0∞) p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "max_r_p_colon_ge_0", 2)
    if args is not None:
        try:
            rhs = OOp("max", (OOp("r", (args[0], args[1],)), OVar("p"),))
            results.append((rhs, "Mathlib: ENNReal_coe_max"))
        except Exception:
            pass
    return results


def _r0084_coe_finset_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_finset_prod
    # ↑(∏ a ∈ s, f a) = ∏ a ∈ s, (f a : ℝ≥0∞)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_in_s_f_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("a"),)), OOp("s", (OOp("f", (OVar("a"), OVar("colon"), OVar("ge_0inf"),)),))))
            results.append((rhs, "Mathlib: ENNReal_coe_finset_prod"))
    except Exception:
        pass
    return results


def _r0085_toNNReal_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.toNNReal_prod
    # (∏ i ∈ s, f i).toNNReal = ∏ i ∈ s, (f i).toNNReal
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("i_in_s_f_i_toNNReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("f_i_toNNReal"),))))
            results.append((rhs, "Mathlib: ENNReal_toNNReal_prod"))
    except Exception:
        pass
    return results


def _r0086_inv_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.inv_top
    # ∞⁻¹ = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("infinv")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ENNReal_inv_top"))
    except Exception:
        pass
    return results


def _r0087_coe_inv_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_inv_two
    # ((2⁻¹ : ℝ≥0) : ℝ≥0∞) = 2⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_2inv_colon_ge_0", 2)
    if args is not None:
        try:
            rhs = OVar("_2inv")
            results.append((rhs, "Mathlib: ENNReal_coe_inv_two"))
        except Exception:
            pass
    return results


def _r0088_inv_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.inv_eq_top
    # a⁻¹ = ∞ ↔ a = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ainv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("inf"), OVar("a"))), OLit(0)))
            results.append((rhs, "Mathlib: ENNReal_inv_eq_top"))
    except Exception:
        pass
    return results


def _r0089_top_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.top_div
    # ∞ / a = if a = ∞ then 0 else ∞
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (args[1],)), OOp("inf", (OVar("then"), OLit(0), OVar("else"), args[0],))))
            results.append((rhs, "Mathlib: ENNReal_top_div"))
        except Exception:
            pass
    return results


def _r0090_top_div_of_ne_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.top_div_of_ne_top
    # ∞ / a = ∞
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ENNReal_top_div_of_ne_top"))
        except Exception:
            pass
    return results


def _r0091_top_div_of_lt_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.top_div_of_lt_top
    # ∞ / a = ∞
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ENNReal_top_div_of_lt_top"))
        except Exception:
            pass
    return results


def _r0092_zero_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.zero_div
    # 0 / a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ENNReal_zero_div"))
        except Exception:
            pass
    return results


def _r0093_div_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.div_eq_top
    # a / b = ∞ ↔ a ≠ 0 ∧ b = 0 ∨ a = ∞ ∧ b ≠ ∞
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("!=", (OOp("iff", (OVar("inf"), args[0])), OOp("and", (OLit(0), args[1])))), OOp("==", (OOp("or", (OLit(0), args[0])), OOp("!=", (OOp("and", (OVar("inf"), args[1])), OVar("inf")))))))
            results.append((rhs, "Mathlib: ENNReal_div_eq_top"))
        except Exception:
            pass
    return results


def _r0094_add_thirds(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.add_thirds
    # a / 3 + a / 3 + a / 3 = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: ENNReal_add_thirds"))
        except Exception:
            pass
    return results


def _r0095_div_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.div_eq_zero_iff
    # a / b = 0 ↔ a = 0 ∨ b = ∞
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OOp("==", (OOp("or", (OLit(0), args[1])), OVar("inf")))))
            results.append((rhs, "Mathlib: ENNReal_div_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0096_toReal_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.toReal_inv
    # a⁻¹.toReal = a.toReal⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ainv_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a_toRealinv")
            results.append((rhs, "Mathlib: ENNReal_toReal_inv"))
    except Exception:
        pass
    return results


def _r0097_toReal_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.toReal_div
    # (a / b).toReal = a.toReal / b.toReal
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_slash_b_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("//", (OVar("a_toReal"), OVar("b_toReal")))
            results.append((rhs, "Mathlib: ENNReal_toReal_div"))
    except Exception:
        pass
    return results


def _r0098_ofReal_min(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofReal_min
    # ENNReal.ofReal (min x y) = min (.ofReal x) (.ofReal y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ENNReal_ofReal", 1)
    if args is not None:
        try:
            rhs = OOp("min", (OOp("ofReal", (OVar("x"),)), OOp("ofReal", (OVar("y"),)),))
            results.append((rhs, "Mathlib: ENNReal_ofReal_min"))
        except Exception:
            pass
    return results


def _r0099_ofReal_max(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofReal_max
    # ENNReal.ofReal (max x y) = max (.ofReal x) (.ofReal y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ENNReal_ofReal", 1)
    if args is not None:
        try:
            rhs = OOp("max", (OOp("ofReal", (OVar("x"),)), OOp("ofReal", (OVar("y"),)),))
            results.append((rhs, "Mathlib: ENNReal_ofReal_max"))
        except Exception:
            pass
    return results


def _r0100_ofReal_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofReal_eq_one
    # ENNReal.ofReal r = 1 ↔ r = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ENNReal_ofReal", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[0])), OLit(1)))
            results.append((rhs, "Mathlib: ENNReal_ofReal_eq_one"))
        except Exception:
            pass
    return results


def _r0101_ofReal_eq_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofReal_eq_ofNat
    # ENNReal.ofReal r = ofNat(n) ↔ r = OfNat.ofNat n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ENNReal_ofReal", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("ofNat_n"), args[0])), OOp("OfNat_ofNat", (OVar("n"),))))
            results.append((rhs, "Mathlib: ENNReal_ofReal_eq_ofNat"))
        except Exception:
            pass
    return results


def _r0102_toNNReal_mul_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.toNNReal_mul_top
    # ENNReal.toNNReal (a * ∞) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ENNReal_toNNReal", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ENNReal_toNNReal_mul_top"))
        except Exception:
            pass
    return results


def _r0103_toReal_nsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.toReal_nsmul
    # (n • a).toReal = n • a.toReal
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_a_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("n", (OVar("_unknown"), OVar("a_toReal"),))
            results.append((rhs, "Mathlib: ENNReal_toReal_nsmul"))
    except Exception:
        pass
    return results


def _r0104_toReal_ofReal_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.toReal_ofReal_mul
    # ENNReal.toReal (ENNReal.ofReal c * a) = c * ENNReal.toReal a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ENNReal_toReal", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("c"), OOp("ENNReal_toReal", (OVar("a"),))))
            results.append((rhs, "Mathlib: ENNReal_toReal_ofReal_mul"))
        except Exception:
            pass
    return results


def _r0105_coe_expect(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.coe_expect
    # 𝔼 i ∈ s, f i = 𝔼 i ∈ s, (f i : ℝ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OOp("f", (OVar("i"), OVar("colon"), OVar("_unknown"),)),))))
            results.append((rhs, "Mathlib: NNReal_coe_expect"))
        except Exception:
            pass
    return results


def _r0106_toNNReal_sum_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.toNNReal_sum_of_nonneg
    # Real.toNNReal (∑ a ∈ s, f a) = ∑ a ∈ s, Real.toNNReal (f a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Real_toNNReal", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("a"),)), OOp("s", (OVar("Real_toNNReal"), OOp("f", (OVar("a"),)),))))
            results.append((rhs, "Mathlib: Real_toNNReal_sum_of_nonneg"))
        except Exception:
            pass
    return results


def _r0107_toNNReal_prod_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.toNNReal_prod_of_nonneg
    # Real.toNNReal (∏ a ∈ s, f a) = ∏ a ∈ s, Real.toNNReal (f a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Real_toNNReal", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("a"),)), OOp("s", (OVar("Real_toNNReal"), OOp("f", (OVar("a"),)),))))
            results.append((rhs, "Mathlib: Real_toNNReal_prod_of_nonneg"))
        except Exception:
            pass
    return results


def _r0108_sqrt_sq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.sqrt_sq
    # sqrt (x ^ 2) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sqrt", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: NNReal_sqrt_sq"))
        except Exception:
            pass
    return results


def _r0109_mul_self_sqrt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.mul_self_sqrt
    # sqrt x * sqrt x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: NNReal_mul_self_sqrt"))
        except Exception:
            pass
    return results


def _r0110_sqrt_mul_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.sqrt_mul_self
    # sqrt (x * x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sqrt", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: NNReal_sqrt_mul_self"))
        except Exception:
            pass
    return results


def _r0111_sqrt_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.sqrt_eq_one
    # sqrt x = 1 ↔ x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sqrt", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[0])), OLit(1)))
            results.append((rhs, "Mathlib: NNReal_sqrt_eq_one"))
        except Exception:
            pass
    return results


def _r0112_sqrt_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.sqrt_zero
    # sqrt 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sqrt", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: NNReal_sqrt_zero"))
        except Exception:
            pass
    return results


def _r0113_sqrt_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.sqrt_one
    # sqrt 1 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sqrt", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: NNReal_sqrt_one"))
        except Exception:
            pass
    return results


def _r0114_group_smul_toList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: HNNExtension.NormalWord.group_smul_toList
    # (g • w).toList = w.toList
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("g_w_toList")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("w_toList")
            results.append((rhs, "Mathlib: HNNExtension_NormalWord_group_smul_toList"))
    except Exception:
        pass
    return results


def _r0115_prod_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: HNNExtension.NormalWord.prod_smul
    # (g • w).prod φ = g * w.prod φ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_w_prod", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("g"), OOp("w_prod", (args[0],))))
            results.append((rhs, "Mathlib: HNNExtension_NormalWord_prod_smul"))
        except Exception:
            pass
    return results


def _r0116_toSphere_eq_zero_iff_finrank(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.toSphere_eq_zero_iff_finrank
    # μ.toSphere = 0 ↔ dim E = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mu_toSphere")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(0), OOp("dim", (OVar("E"),)))), OLit(0)))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_toSphere_eq_zero_iff_finrank"))
    except Exception:
        pass
    return results


def _r0117_piPremeasure_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.piPremeasure_pi
    # piPremeasure m (pi univ s) = ∏ i, m i (s i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "piPremeasure", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), args[0], OVar("i"), OOp("s", (OVar("i"),)),))
            results.append((rhs, "Mathlib: MeasureTheory_piPremeasure_pi"))
        except Exception:
            pass
    return results


def _r0118_tprod_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.tprod_cons
    # Measure.tprod (i :: l) μ = (μ i).prod (Measure.tprod l μ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Measure_tprod", 2)
    if args is not None:
        try:
            rhs = OOp("mu_i_prod", (OOp("Measure_tprod", (OVar("l"), args[1],)),))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_tprod_cons"))
        except Exception:
            pass
    return results


def _r0119_condLExp_congr_ae_trim(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.condLExp_congr_ae_trim
    # P⁻[X|mΩ] =ᵐ[P.trim hm] P⁻[Y|mΩ]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Pinv_Xpipe_mOmega")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("P_trim_hm", (OVar("Pinv_Ypipe_mOmega"),))
            results.append((rhs, "Mathlib: MeasureTheory_condLExp_congr_ae_trim"))
    except Exception:
        pass
    return results


def _r0120_essSup_const_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.essSup_const_mul
    # essSup (fun x : α => a * f x) μ = a * essSup f μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "essSup", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("a"), OOp("essSup", (OVar("f"), args[1],))))
            results.append((rhs, "Mathlib: ENNReal_essSup_const_mul"))
        except Exception:
            pass
    return results


def _r0121_lpNorm_of_not_memLp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.lpNorm_of_not_memLp
    # lpNorm f p μ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lpNorm", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_lpNorm_of_not_memLp"))
        except Exception:
            pass
    return results


def _r0122_lpNorm_eq_integral_norm_rpow_toReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
    # lpNorm f p μ = (∫ x, ‖f x‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lpNorm", 3)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("**", (OOp("_unknown", (OVar("x"), args[0], OVar("x"),)), OOp("p_toReal", (args[2],)))), OVar("p_toRealinv")))
            results.append((rhs, "Mathlib: MeasureTheory_lpNorm_eq_integral_norm_rpow_toReal"))
        except Exception:
            pass
    return results


def _r0123_lpNorm_measure_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.lpNorm_measure_zero
    # lpNorm f p (0 : Measure α) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lpNorm", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_lpNorm_measure_zero"))
        except Exception:
            pass
    return results


def _r0124_lpNorm_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.lpNorm_eq_zero
    # lpNorm f p μ = 0 ↔ f =ᵐ[μ] 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lpNorm", 3)
    if args is not None:
        try:
            rhs = OOp("iff", (OLit(0), OOp("f", (OVar("eq_mu"), OLit(0),))))
            results.append((rhs, "Mathlib: MeasureTheory_lpNorm_eq_zero"))
        except Exception:
            pass
    return results


def _r0125_lpNorm_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.lpNorm_neg
    # lpNorm (-f) p μ = lpNorm f p μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lpNorm", 3)
    if args is not None:
        try:
            rhs = OOp("lpNorm", (OVar("f"), args[1], args[2],))
            results.append((rhs, "Mathlib: MeasureTheory_lpNorm_neg"))
        except Exception:
            pass
    return results


def _r0126_lpNorm_sub_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.lpNorm_sub_comm
    # lpNorm (f - g) p μ = lpNorm (g - f) p μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lpNorm", 3)
    if args is not None:
        try:
            rhs = OOp("lpNorm", (OOp("-", (OVar("g"), OVar("f"))), args[1], args[2],))
            results.append((rhs, "Mathlib: MeasureTheory_lpNorm_sub_comm"))
        except Exception:
            pass
    return results


def _r0127_lpNorm_abs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.lpNorm_abs
    # lpNorm (|f|) p μ = lpNorm f p μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lpNorm", 3)
    if args is not None:
        try:
            rhs = OOp("lpNorm", (OVar("f"), args[1], args[2],))
            results.append((rhs, "Mathlib: MeasureTheory_lpNorm_abs"))
        except Exception:
            pass
    return results


def _r0128_lpNorm_fun_abs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.lpNorm_fun_abs
    # lpNorm (fun x ↦ |f x|) p μ = lpNorm f p μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lpNorm", 3)
    if args is not None:
        try:
            rhs = OOp("lpNorm", (OVar("f"), args[1], args[2],))
            results.append((rhs, "Mathlib: MeasureTheory_lpNorm_fun_abs"))
        except Exception:
            pass
    return results


def _r0129_lpNorm_const(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.lpNorm_const
    # lpNorm (fun _x ↦ c) p μ = ‖c‖ * μ.real .univ ^ p.toReal⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lpNorm", 3)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("c"), OOp("**", (OOp("mu_real", (OVar("univ"),)), OVar("p_toRealinv")))))
            results.append((rhs, "Mathlib: MeasureTheory_lpNorm_const"))
        except Exception:
            pass
    return results


def _r0130_toLp_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.MemLp.toLp_zero
    # h.toLp 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_toLp", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_MemLp_toLp_zero"))
        except Exception:
            pass
    return results


def _r0131_toLp_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.MemLp.toLp_add
    # (hf.add hg).toLp (f + g) = hf.toLp f + hg.toLp g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hf_add_hg_toLp", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("hf_toLp", (OVar("f"),)), OOp("hg_toLp", (OVar("g"),))))
            results.append((rhs, "Mathlib: MeasureTheory_MemLp_toLp_add"))
        except Exception:
            pass
    return results


def _r0132_enorm_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Lp.enorm_def
    # ‖f‖ₑ = eLpNorm f p μ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("eLpNorm", (OVar("f"), OVar("p"), OVar("mu"),))
            results.append((rhs, "Mathlib: MeasureTheory_Lp_enorm_def"))
    except Exception:
        pass
    return results


def _r0133_norm_toLp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Lp.norm_toLp
    # ‖hf.toLp f‖ = ENNReal.toReal (eLpNorm f p μ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hf_toLp", 1)
    if args is not None:
        try:
            rhs = OOp("ENNReal_toReal", (OOp("eLpNorm", (args[0], OVar("p"), OVar("mu"),)),))
            results.append((rhs, "Mathlib: MeasureTheory_Lp_norm_toLp"))
        except Exception:
            pass
    return results


def _r0134_nnnorm_toLp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Lp.nnnorm_toLp
    # ‖hf.toLp f‖₊ = ENNReal.toNNReal (eLpNorm f p μ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hf_toLp", 1)
    if args is not None:
        try:
            rhs = OOp("ENNReal_toNNReal", (OOp("eLpNorm", (args[0], OVar("p"), OVar("mu"),)),))
            results.append((rhs, "Mathlib: MeasureTheory_Lp_nnnorm_toLp"))
        except Exception:
            pass
    return results


def _r0135_nnnorm_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Lp.nnnorm_zero
    # ‖(0 : Lp E p μ)‖₊ = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_Lp_E_p_mu")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_Lp_nnnorm_zero"))
    except Exception:
        pass
    return results


def _r0136_norm_measure_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Lp.norm_measure_zero
    # ‖f‖ = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_Lp_norm_measure_zero"))
    except Exception:
        pass
    return results


def _r0137_eq_zero_iff_ae_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Lp.eq_zero_iff_ae_eq_zero
    # f = 0 ↔ f =ᵐ[μ] 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OLit(0), OOp("f", (OVar("eq_mu"), OLit(0),))))
            results.append((rhs, "Mathlib: MeasureTheory_Lp_eq_zero_iff_ae_eq_zero"))
    except Exception:
        pass
    return results


def _r0138_norm_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Lp.norm_neg
    # ‖-f‖ = ‖f‖
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: MeasureTheory_Lp_norm_neg"))
    except Exception:
        pass
    return results


def _r0139_apply_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.apply_mk
    # SimpleFunc.mk f h h' x = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "SimpleFunc_mk", 4)
    if args is not None:
        try:
            rhs = OOp("f", (args[3],))
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_apply_mk"))
        except Exception:
            pass
    return results


def _r0140_range_const(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.range_const
    # (const α b).range = {b}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("const_a_b_range")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("b")
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_range_const"))
    except Exception:
        pass
    return results


def _r0141_piecewise_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.piecewise_empty
    # piecewise ∅ MeasurableSet.empty f g = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "piecewise", 4)
    if args is not None:
        try:
            rhs = args[3]
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_piecewise_empty"))
        except Exception:
            pass
    return results


def _r0142_range_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.range_map
    # (f.map g).range = f.range.image g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_map_g_range")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_range_image", (OVar("g"),))
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_range_map"))
    except Exception:
        pass
    return results


def _r0143_map_const(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.map_const
    # (const α b).map g = const α (g b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "const_a_b_map", 1)
    if args is not None:
        try:
            rhs = OOp("const", (OVar("a"), OOp("g", (OVar("b"),)),))
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_map_const"))
        except Exception:
            pass
    return results


def _r0144_pair_preimage(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.pair_preimage
    # pair f g ⁻¹' s ×ˢ t = f ⁻¹' s ∩ g ⁻¹' t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 6)
    if args is not None:
        try:
            rhs = OOp("inter", (OOp("f", (args[2], args[3],)), OOp("g", (args[2], args[5],))))
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_pair_preimage"))
        except Exception:
            pass
    return results


def _r0145_map_snd_pair(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.map_snd_pair
    # (f.pair g).map Prod.snd = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_pair_g_map", 1)
    if args is not None:
        try:
            rhs = OVar("g")
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_map_snd_pair"))
        except Exception:
            pass
    return results


def _r0146_bind_const(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.bind_const
    # f.bind (const α) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_bind", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_bind_const"))
        except Exception:
            pass
    return results


def _r0147_coe_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.coe_mul
    # ⇑(f * g) = ⇑f * ⇑g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_star_g")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("f"), OVar("g")))
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_coe_mul"))
    except Exception:
        pass
    return results


def _r0148_coe_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.coe_inv
    # ⇑(f⁻¹) = (⇑f)⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("finv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f_inv")
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_coe_inv"))
    except Exception:
        pass
    return results


def _r0149_coe_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.coe_div
    # ⇑(f / g) = ⇑f / ⇑g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_slash_g")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("//", (OVar("f"), OVar("g")))
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_coe_div"))
    except Exception:
        pass
    return results


def _r0150_coe_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.coe_sup
    # ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f", (OVar("_unknown"), OVar("g"),))
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_coe_sup"))
    except Exception:
        pass
    return results


def _r0151_coe_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.coe_inf
    # ⇑(f ⊓ g) = ⇑f ⊓ ⇑g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f", (OVar("_unknown"), OVar("g"),))
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_coe_inf"))
    except Exception:
        pass
    return results


def _r0152_mul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.mul_apply
    # (f * g) a = f a * g a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_star_g", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("f", (args[0],)), OOp("g", (args[0],))))
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_mul_apply"))
        except Exception:
            pass
    return results


def _r0153_range_eq_empty_of_isEmpty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.range_eq_empty_of_isEmpty
    # f.range = ∅
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_range")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_range_eq_empty_of_isEmpty"))
    except Exception:
        pass
    return results


def _r0154_smul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.smul_apply
    # (k • f) a = k • f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "k_f", 1)
    if args is not None:
        try:
            rhs = OOp("k", (OVar("_unknown"), OVar("f"), args[0],))
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_smul_apply"))
        except Exception:
            pass
    return results


def _r0155_pow_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.pow_apply
    # (f ^ n) a = f a ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_pow_n", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("f", (args[0],)), OVar("n")))
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_pow_apply"))
        except Exception:
            pass
    return results


def _r0156_zpow_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.zpow_apply
    # (f ^ z) a = f a ^ z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_pow_z", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("f", (args[0],)), OVar("z")))
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_zpow_apply"))
        except Exception:
            pass
    return results


def _r0157_nearestPt_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.nearestPt_zero
    # nearestPt e 0 = const α (e 0)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nearestPt", 2)
    if args is not None:
        try:
            rhs = OOp("const", (OVar("a"), OOp("e", (OLit(0),)),))
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_nearestPt_zero"))
        except Exception:
            pass
    return results


def _r0158_nearestPtInd_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.nearestPtInd_succ
    # nearestPtInd e (N + 1) x =       if ∀ k ≤ N, edist (e (N + 1)) x < edist (e k) x then N + 1 else nearestPtInd e N x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nearestPtInd", 3)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("if", (OVar("forall"), OVar("k"),)), OOp("<", (OOp("N", (OVar("edist"), OOp("e", (OOp("+", (OVar("N"), OLit(1))),)), args[2],)), OOp("+", (OOp("edist", (OOp("e", (OVar("k"),)), args[2], OVar("then"), OVar("N"),)), OOp("_1", (OVar("else"), OVar("nearestPtInd"), args[0], OVar("N"), args[2],))))))))
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_nearestPtInd_succ"))
        except Exception:
            pass
    return results


def _r0159_dirac_one_mconv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.dirac_one_mconv
    # (dirac 1) ∗ₘ μ = μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dirac_1", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: MeasureTheory_Measure_dirac_one_mconv"))
        except Exception:
            pass
    return results


def _r0160_mconv_dirac_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.mconv_dirac_one
    # μ ∗ₘ (dirac 1) = μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu", 2)
    if args is not None:
        try:
            rhs = OVar("mu")
            results.append((rhs, "Mathlib: MeasureTheory_Measure_mconv_dirac_one"))
        except Exception:
            pass
    return results


def _r0161_sdiff_fundamentalFrontier(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.sdiff_fundamentalFrontier
    # s \\ fundamentalFrontier G s = fundamentalInterior G s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 4)
    if args is not None:
        try:
            rhs = OOp("fundamentalInterior", (args[2], args[3],))
            results.append((rhs, "Mathlib: MeasureTheory_sdiff_fundamentalFrontier"))
        except Exception:
            pass
    return results


def _r0162_fundamentalFrontier_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.fundamentalFrontier_smul
    # fundamentalFrontier G (g • s) = g • fundamentalFrontier G s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fundamentalFrontier", 2)
    if args is not None:
        try:
            rhs = OOp("g", (OVar("_unknown"), OVar("fundamentalFrontier"), args[0], OVar("s"),))
            results.append((rhs, "Mathlib: MeasureTheory_fundamentalFrontier_smul"))
        except Exception:
            pass
    return results


def _r0163_laverage_zero_measure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.laverage_zero_measure
    # ⨍⁻ x, f x ∂(0 : Measure α) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inv", 4)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_laverage_zero_measure"))
        except Exception:
            pass
    return results


def _r0164_integral_indicator_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.integral_indicator₂
    # ∫ y, s.indicator (f · y) b ∂μ = s.indicator (fun x ↦ ∫ y, f x y ∂μ) b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 5)
    if args is not None:
        try:
            rhs = OOp("s_indicator", (OOp("fun", (OVar("x"), OVar("_unknown"), OVar("_unknown"), args[0], OVar("f"), OVar("x"), args[0], args[4],)), args[3],))
            results.append((rhs, "Mathlib: MeasureTheory_integral_indicator_2"))
        except Exception:
            pass
    return results


def _r0165_weightedSMul_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.weightedSMul_empty
    # weightedSMul μ ∅ = (0 : F →L[ℝ] F)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "weightedSMul", 2)
    if args is not None:
        try:
            rhs = OOp("_0", (OVar("colon"), OVar("F"), OVar("to_L"), OVar("F"),))
            results.append((rhs, "Mathlib: MeasureTheory_weightedSMul_empty"))
        except Exception:
            pass
    return results


def _r0166_addContent_sUnion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.addContent_sUnion
    # m (⋃₀ I) = ∑ u ∈ I, m u
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("u"),)), OOp("I", (OVar("m"), OVar("u"),))))
            results.append((rhs, "Mathlib: MeasureTheory_addContent_sUnion"))
        except Exception:
            pass
    return results


def _r0167_mk_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Content.mk_apply
    # mk toFun mono' sup_disjoint' sup_le' K = toFun K
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 5)
    if args is not None:
        try:
            rhs = OOp("toFun", (args[4],))
            results.append((rhs, "Mathlib: MeasureTheory_Content_mk_apply"))
        except Exception:
            pass
    return results


def _r0168_count_apply_finset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.count_apply_finset
    # count (↑s : Set α) = #s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "count", 1)
    if args is not None:
        try:
            rhs = OVar("hash_s")
            results.append((rhs, "Mathlib: MeasureTheory_Measure_count_apply_finset"))
        except Exception:
            pass
    return results


def _r0169_count_eq_dirac(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subsingleton.count_eq_dirac
    # count = dirac i
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("count")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("dirac", (OVar("i"),))
            results.append((rhs, "Mathlib: Subsingleton_count_eq_dirac"))
    except Exception:
        pass
    return results


def _r0170_dirac_apply_eq_zero_or_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.dirac_apply_eq_zero_or_one
    # dirac a s = 0 ∨ dirac a s = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dirac", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OLit(0), OOp("dirac", (args[0], args[1],)))), OLit(1)))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_dirac_apply_eq_zero_or_one"))
        except Exception:
            pass
    return results


def _r0171_ae_dirac_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.ae_dirac_eq
    # ae (dirac a) = pure a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ae", 1)
    if args is not None:
        try:
            rhs = OOp("pure", (OVar("a"),))
            results.append((rhs, "Mathlib: MeasureTheory_ae_dirac_eq"))
        except Exception:
            pass
    return results


def _r0172_diracProba_toMeasure_apply_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.diracProba_toMeasure_apply_of_mem
    # (diracProba x).toMeasure A = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "diracProba_x_toMeasure", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: MeasureTheory_diracProba_toMeasure_apply_of_mem"))
        except Exception:
            pass
    return results


def _r0173_diracProba_toMeasure_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.diracProba_toMeasure_apply
    # (diracProba x).toMeasure A = A.indicator 1 x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "diracProba_x_toMeasure", 1)
    if args is not None:
        try:
            rhs = OOp("A_indicator", (OLit(1), OVar("x"),))
            results.append((rhs, "Mathlib: MeasureTheory_diracProba_toMeasure_apply"))
        except Exception:
            pass
    return results


def _r0174_diracProbaInverse_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.diracProbaInverse_eq
    # diracProbaInverse μ = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "diracProbaInverse", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: MeasureTheory_diracProbaInverse_eq"))
        except Exception:
            pass
    return results


def _r0175_toMeasure_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.toMeasure_mk
    # FiniteMeasure.toMeasure (⟨μ, h⟩ : FiniteMeasure Ω) = μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "FiniteMeasure_toMeasure", 1)
    if args is not None:
        try:
            rhs = OVar("mu")
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_toMeasure_mk"))
        except Exception:
            pass
    return results


def _r0176_measureReal_eq_coe_coeFn(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.measureReal_eq_coe_coeFn
    # (μ : Measure Ω).real s = μ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_colon_Measure_Omega_real", 1)
    if args is not None:
        try:
            rhs = OOp("mu", (args[0],))
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_measureReal_eq_coe_coeFn"))
        except Exception:
            pass
    return results


def _r0177_ennreal_coeFn_eq_coeFn_toMeasure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure
    # (ν s : ℝ≥0∞) = (ν : Measure Ω) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nu", 3)
    if args is not None:
        try:
            rhs = OOp("nu_colon_Measure_Omega", (args[0],))
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_ennreal_coeFn_eq_coeFn_toMeasure"))
        except Exception:
            pass
    return results


def _r0178_ennreal_mass(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.ennreal_mass
    # (μ.mass : ℝ≥0∞) = (μ : Measure Ω) univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_mass", 2)
    if args is not None:
        try:
            rhs = OOp("mu_colon_Measure_Omega", (OVar("univ"),))
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_ennreal_mass"))
        except Exception:
            pass
    return results


def _r0179_zero_mass(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.zero_mass
    # (0 : FiniteMeasure Ω).mass = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_FiniteMeasure_Omega_mass")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_zero_mass"))
    except Exception:
        pass
    return results


def _r0180_mass_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.mass_zero_iff
    # μ.mass = 0 ↔ μ = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mu_mass")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("mu"))), OLit(0)))
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_mass_zero_iff"))
    except Exception:
        pass
    return results


def _r0181_toMeasure_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.toMeasure_add
    # ↑(μ + ν) = (↑μ + ↑ν : Measure Ω)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mu_plus_nu")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("mu"), OOp("nu", (OVar("colon"), OVar("Measure"), OVar("Omega"),))))
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_toMeasure_add"))
    except Exception:
        pass
    return results


def _r0182_toMeasure_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.toMeasure_smul
    # ↑(c • μ) = c • (μ : Measure Ω)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("c_mu")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("c", (OVar("_unknown"), OOp("mu", (OVar("colon"), OVar("Measure"), OVar("Omega"),)),))
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_toMeasure_smul"))
    except Exception:
        pass
    return results


def _r0183_restrict_apply_measure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.restrict_apply_measure
    # (μ.restrict A : Measure Ω) s = (μ : Measure Ω) (s ∩ A)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_restrict_A_colon_Measure_Omega", 1)
    if args is not None:
        try:
            rhs = OOp("mu_colon_Measure_Omega", (OOp("inter", (args[0], OVar("A"))),))
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_restrict_apply_measure"))
        except Exception:
            pass
    return results


def _r0184_restrict_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.restrict_univ
    # μ.restrict univ = μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_restrict", 1)
    if args is not None:
        try:
            rhs = OVar("mu")
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_restrict_univ"))
        except Exception:
            pass
    return results


def _r0185_restrict_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.restrict_union
    # μ.restrict (s ∪ t) = μ.restrict s + μ.restrict t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_restrict", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("mu_restrict", (OVar("s"),)), OOp("mu_restrict", (OVar("t"),))))
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_restrict_union"))
        except Exception:
            pass
    return results


def _r0186_testAgainstNN_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.testAgainstNN_one
    # μ.testAgainstNN 1 = μ.mass
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_testAgainstNN", 1)
    if args is not None:
        try:
            rhs = OVar("mu_mass")
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_testAgainstNN_one"))
        except Exception:
            pass
    return results


def _r0187_zero_testAgainstNN(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.zero_testAgainstNN
    # (0 : FiniteMeasure Ω).testAgainstNN = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_FiniteMeasure_Omega_testAgainstNN")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_zero_testAgainstNN"))
    except Exception:
        pass
    return results


def _r0188_toWeakDualBCNN_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.toWeakDualBCNN_apply
    # μ.toWeakDualBCNN f = (∫⁻ x, f x ∂(μ : Measure Ω)).toNNReal
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_toWeakDualBCNN", 1)
    if args is not None:
        try:
            rhs = OVar("inv_x_f_x_mu_colon_Measure_Omega_toNNReal")
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_toWeakDualBCNN_apply"))
        except Exception:
            pass
    return results


def _r0189_pi_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.pi_pi
    # (FiniteMeasure.pi μ) (Set.pi univ s) = ∏ i, μ i (s i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "FiniteMeasure_pi_mu", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), OVar("mu"), OVar("i"), OOp("s", (OVar("i"),)),))
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_pi_pi"))
        except Exception:
            pass
    return results


def _r0190_mass_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.mass_pi
    # (FiniteMeasure.pi μ).mass = ∏ i, (μ i).mass
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("FiniteMeasure_pi_mu_mass")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_unknown", (OVar("i"), OVar("mu_i_mass"),))
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_mass_pi"))
    except Exception:
        pass
    return results


def _r0191_pi_map_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.pi_map_pi
    # (FiniteMeasure.pi μ).map (fun x i ↦ (f i (x i))) =       FiniteMeasure.pi (fun i ↦ (μ i).map (f i))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "FiniteMeasure_pi_mu_map", 1)
    if args is not None:
        try:
            rhs = OOp("FiniteMeasure_pi", (OOp("fun", (OVar("i"), OVar("_unknown"), OVar("mu_i_map"), OOp("f", (OVar("i"),)),)),))
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_pi_map_pi"))
        except Exception:
            pass
    return results


def _r0192_pi_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.ProbabilityMeasure.pi_pi
    # ProbabilityMeasure.pi μ (Set.pi univ s) = ∏ i, μ i (s i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ProbabilityMeasure_pi", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), args[0], OVar("i"), OOp("s", (OVar("i"),)),))
            results.append((rhs, "Mathlib: MeasureTheory_ProbabilityMeasure_pi_pi"))
        except Exception:
            pass
    return results


def _r0193_prod_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.prod_apply
    # μ.prod ν s = ENNReal.toNNReal (∫⁻ x, ν.toMeasure (Prod.mk x ⁻¹' s) ∂μ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_prod", 2)
    if args is not None:
        try:
            rhs = OOp("ENNReal_toNNReal", (OOp("inv", (OVar("x"), OVar("nu_toMeasure"), OOp("pair", (OVar("x"), OVar("inv_prime"), args[1],)), OVar("mu"),)),))
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_prod_apply"))
        except Exception:
            pass
    return results


def _r0194_mass_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.mass_prod
    # (μ.prod ν).mass = μ.mass * ν.mass
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mu_prod_nu_mass")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("mu_mass"), OVar("nu_mass")))
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_mass_prod"))
    except Exception:
        pass
    return results


def _r0195_prod_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.prod_zero
    # μ.prod (0 : FiniteMeasure β) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_prod", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_prod_zero"))
        except Exception:
            pass
    return results


def _r0196_map_fst_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.map_fst_prod
    # (μ.prod ν).map Prod.fst = ν univ • μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_prod_nu_map", 1)
    if args is not None:
        try:
            rhs = OOp("nu", (OVar("univ"), OVar("_unknown"), OVar("mu"),))
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_map_fst_prod"))
        except Exception:
            pass
    return results


def _r0197_map_snd_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.map_snd_prod
    # (μ.prod ν).map Prod.snd = μ univ • ν
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_prod_nu_map", 1)
    if args is not None:
        try:
            rhs = OOp("mu", (OVar("univ"), OVar("_unknown"), OVar("nu"),))
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_map_snd_prod"))
        except Exception:
            pass
    return results


def _r0198_map_prod_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.map_prod_map
    # (μ.map f).prod (ν.map g) = (μ.prod ν).map (Prod.map f g)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_map_f_prod", 1)
    if args is not None:
        try:
            rhs = OOp("mu_prod_nu_map", (OOp("Prod_map", (OVar("f"), OVar("g"),)),))
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_map_prod_map"))
        except Exception:
            pass
    return results


def _r0199_bind_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.bind_apply
    # bind m f s = ∫⁻ a, f a s ∂m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "flat_map", 3)
    if args is not None:
        try:
            rhs = OOp("inv", (OVar("a"), args[1], OVar("a"), args[2], args[0],))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_bind_apply"))
        except Exception:
            pass
    return results


def _r0200_bind_dirac(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.bind_dirac
    # bind m dirac = m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "flat_map", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: MeasureTheory_Measure_bind_dirac"))
        except Exception:
            pass
    return results


def _r0201_levyProkhorovEDist_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.levyProkhorovEDist_self
    # levyProkhorovEDist μ μ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "levyProkhorovEDist", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_levyProkhorovEDist_self"))
        except Exception:
            pass
    return results


def _r0202_map_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.map_zero
    # (0 : Measure α).map f = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_Measure_a_map", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_Measure_map_zero"))
        except Exception:
            pass
    return results


def _r0203_map_of_not_aemeasurable(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.map_of_not_aemeasurable
    # μ.map f = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_map", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_Measure_map_of_not_aemeasurable"))
        except Exception:
            pass
    return results


def _r0204_map_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.map_apply
    # μ.map f s = μ (f ⁻¹' s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_map", 2)
    if args is not None:
        try:
            rhs = OOp("mu", (OOp("f", (OVar("inv_prime"), args[1],)),))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_map_apply"))
        except Exception:
            pass
    return results


def _r0205_map_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.mapₗ_eq_zero_iff
    # Measure.mapₗ f μ = 0 ↔ μ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Measure_map", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[1])), OLit(0)))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_map_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0206_measure_preimage_of_map_eq_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.measure_preimage_of_map_eq_self
    # μ (f ⁻¹' s) = μ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu", 1)
    if args is not None:
        try:
            rhs = OOp("mu", (OVar("s"),))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_measure_preimage_of_map_eq_self"))
        except Exception:
            pass
    return results


def _r0207_ae_eq_of_ae_subset_of_measure_ge(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.ae_eq_of_ae_subset_of_measure_ge
    # s =ᵐ[μ] t
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("mu", (OVar("t"),))
            results.append((rhs, "Mathlib: MeasureTheory_ae_eq_of_ae_subset_of_measure_ge"))
    except Exception:
        pass
    return results


def _r0208_toMeasure_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.OuterMeasure.toMeasure_zero
    # (0 : OuterMeasure α).toMeasure h = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_OuterMeasure_a_toMeasure", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_OuterMeasure_toMeasure_zero"))
        except Exception:
            pass
    return results


def _r0209_toOuterMeasure_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.toOuterMeasure_apply
    # μ.toOuterMeasure s = μ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_toOuterMeasure", 1)
    if args is not None:
        try:
            rhs = OOp("mu", (args[0],))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_toOuterMeasure_apply"))
        except Exception:
            pass
    return results


def _r0210_exists_measurable_superset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.exists_measurable_superset
    # ∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = μ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("mu", (OVar("s"),))
            results.append((rhs, "Mathlib: MeasureTheory_exists_measurable_superset"))
        except Exception:
            pass
    return results


def _r0211_measure_compl_nullSet(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.MutuallySingular.measure_compl_nullSet
    # ν h.nullSetᶜ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nu", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_Measure_MutuallySingular_measure_compl_nullSet"))
        except Exception:
            pass
    return results


def _r0212_val_eq_to_measure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.ProbabilityMeasure.val_eq_to_measure
    # ν.val = (ν : Measure Ω)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("nu_val")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("nu", (OVar("colon"), OVar("Measure"), OVar("Omega"),))
            results.append((rhs, "Mathlib: MeasureTheory_ProbabilityMeasure_val_eq_to_measure"))
    except Exception:
        pass
    return results


def _r0213_coeFn_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.ProbabilityMeasure.coeFn_univ
    # ν univ = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nu", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: MeasureTheory_ProbabilityMeasure_coeFn_univ"))
        except Exception:
            pass
    return results


def _r0214_coeFn_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.ProbabilityMeasure.coeFn_empty
    # ν ∅ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nu", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_ProbabilityMeasure_coeFn_empty"))
        except Exception:
            pass
    return results


def _r0215_toNNReal_measureReal_eq_coeFn(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.ProbabilityMeasure.toNNReal_measureReal_eq_coeFn
    # ((ν : Measure Ω).real s).toNNReal = ν s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("nu_colon_Measure_Omega_real_s_toNNReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("nu", (OVar("s"),))
            results.append((rhs, "Mathlib: MeasureTheory_ProbabilityMeasure_toNNReal_measureReal_eq_coeFn"))
    except Exception:
        pass
    return results


def _r0216_toFiniteMeasure_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.ProbabilityMeasure.toFiniteMeasure_apply
    # μ.toFiniteMeasure s = μ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_toFiniteMeasure", 1)
    if args is not None:
        try:
            rhs = OOp("mu", (args[0],))
            results.append((rhs, "Mathlib: MeasureTheory_ProbabilityMeasure_toFiniteMeasure_apply"))
        except Exception:
            pass
    return results


def _r0217_toFiniteMeasure_apply_eq_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.ProbabilityMeasure.toFiniteMeasure_apply_eq_apply
    # ν.toFiniteMeasure s = ν s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nu_toFiniteMeasure", 1)
    if args is not None:
        try:
            rhs = OOp("nu", (args[0],))
            results.append((rhs, "Mathlib: MeasureTheory_ProbabilityMeasure_toFiniteMeasure_apply_eq_apply"))
        except Exception:
            pass
    return results


def _r0218_ennreal_coeFn_eq_coeFn_toMeasure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure
    # (ν s : ℝ≥0∞) = (ν : Measure Ω) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nu", 3)
    if args is not None:
        try:
            rhs = OOp("nu_colon_Measure_Omega", (args[0],))
            results.append((rhs, "Mathlib: MeasureTheory_ProbabilityMeasure_ennreal_coeFn_eq_coeFn_toMeasure"))
        except Exception:
            pass
    return results


def _r0219_range_toFiniteMeasure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.ProbabilityMeasure.range_toFiniteMeasure
    # range toFiniteMeasure = {μ : FiniteMeasure Ω | μ.mass = 1}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OVar("mu_colon_FiniteMeasure_Omega_pipe_mu_mass_eq_1")
            results.append((rhs, "Mathlib: MeasureTheory_ProbabilityMeasure_range_toFiniteMeasure"))
        except Exception:
            pass
    return results


def _r0220_toWeakDualBCNN_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.ProbabilityMeasure.toWeakDualBCNN_apply
    # μ.toWeakDualBCNN f = (∫⁻ ω, f ω ∂(μ : Measure Ω)).toNNReal
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_toWeakDualBCNN", 1)
    if args is not None:
        try:
            rhs = OVar("inv_omega_f_omega_mu_colon_Measure_Omega_toNNReal")
            results.append((rhs, "Mathlib: MeasureTheory_ProbabilityMeasure_toWeakDualBCNN_apply"))
        except Exception:
            pass
    return results


def _r0221_map_prod_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.map_prod_map
    # (map f μa).prod (map g μc) = map (Prod.map f g) (μa.prod μc)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_f_mua_prod", 1)
    if args is not None:
        try:
            rhs = OOp("map", (OOp("Prod_map", (OVar("f"), OVar("g"),)), OOp("mua_prod", (OVar("muc"),)),))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_map_prod_map"))
        except Exception:
            pass
    return results


def _r0222_fst_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.fst_sum
    # (sum μ).fst = sum (fun n ↦ (μ n).fst)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sum_mu_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("sum", (OOp("fun", (OVar("n"), OVar("_unknown"), OVar("mu_n_fst"),)),))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_fst_sum"))
    except Exception:
        pass
    return results


def _r0223_snd_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.snd_sum
    # (sum μ).snd = sum (fun n ↦ (μ n).snd)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sum_mu_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("sum", (OOp("fun", (OVar("n"), OVar("_unknown"), OVar("mu_n_snd"),)),))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_snd_sum"))
    except Exception:
        pass
    return results


def _r0224_snd_map_swap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.snd_map_swap
    # (ρ.map Prod.swap).snd = ρ.fst
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("rho_map_Prod_swap_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("rho_fst")
            results.append((rhs, "Mathlib: MeasureTheory_Measure_snd_map_swap"))
    except Exception:
        pass
    return results


def _r0225_measureReal_zero_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.measureReal_zero_apply
    # (0 : Measure α).real s = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_Measure_a_real", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_measureReal_zero_apply"))
        except Exception:
            pass
    return results


def _r0226_measureReal_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.measureReal_empty
    # μ.real ∅ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_real", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_measureReal_empty"))
        except Exception:
            pass
    return results


def _r0227_measureReal_nnreal_smul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.measureReal_nnreal_smul_apply
    # (c • μ).real s = c * μ.real s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_mu_real", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("c"), OOp("mu_real", (args[0],))))
            results.append((rhs, "Mathlib: MeasureTheory_measureReal_nnreal_smul_apply"))
        except Exception:
            pass
    return results


def _r0228_map_measureReal_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.map_measureReal_apply
    # (μ.map f).real s = μ.real (f ⁻¹' s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_map_f_real", 1)
    if args is not None:
        try:
            rhs = OOp("mu_real", (OOp("f", (OVar("inv_prime"), args[0],)),))
            results.append((rhs, "Mathlib: MeasureTheory_map_measureReal_apply"))
        except Exception:
            pass
    return results


def _r0229_measureReal_mono_null(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.measureReal_mono_null
    # μ.real s₁ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_real", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_measureReal_mono_null"))
        except Exception:
            pass
    return results


def _r0230_restrict_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.restrict_smul
    # (c • μ).restrict s = c • μ.restrict s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_mu_restrict", 1)
    if args is not None:
        try:
            rhs = OOp("c", (OVar("_unknown"), OVar("mu_restrict"), args[0],))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_restrict_smul"))
        except Exception:
            pass
    return results


def _r0231_restrict_restrict_of_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.restrict_restrict_of_subset
    # (μ.restrict t).restrict s = μ.restrict s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_restrict_t_restrict", 1)
    if args is not None:
        try:
            rhs = OOp("mu_restrict", (args[0],))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_restrict_restrict_of_subset"))
        except Exception:
            pass
    return results


def _r0232_restrict_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.restrict_univ
    # μ.restrict univ = μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_restrict", 1)
    if args is not None:
        try:
            rhs = OVar("mu")
            results.append((rhs, "Mathlib: MeasureTheory_Measure_restrict_univ"))
        except Exception:
            pass
    return results


def _r0233_restrict_inter_add_diff_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.restrict_inter_add_diff₀
    # μ.restrict (s ∩ t) + μ.restrict (s \\ t) = μ.restrict s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("mu_restrict", (OVar("s"),))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_restrict_inter_add_diff_0"))
        except Exception:
            pass
    return results


def _r0234_zero_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.zero_sub
    # 0 - μ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_Measure_zero_sub"))
        except Exception:
            pass
    return results


def _r0235_sub_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.sub_self
    # μ - μ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_Measure_sub_self"))
        except Exception:
            pass
    return results


def _r0236_sub_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.sub_zero
    # μ - 0 = μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: MeasureTheory_Measure_sub_zero"))
        except Exception:
            pass
    return results


def _r0237_support_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.support_add
    # (μ + ν).support = μ.support ∪ ν.support
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mu_plus_nu_support")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("union", (OVar("mu_support"), OVar("nu_support")))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_support_add"))
    except Exception:
        pass
    return results


def _r0238_trim_measurableSet_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.trim_measurableSet_eq
    # μ.trim hm s = μ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_trim", 2)
    if args is not None:
        try:
            rhs = OOp("mu", (args[1],))
            results.append((rhs, "Mathlib: MeasureTheory_trim_measurableSet_eq"))
        except Exception:
            pass
    return results


def _r0239_measure_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Finite.measure_zero
    # μ s = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Set_Finite_measure_zero"))
        except Exception:
            pass
    return results


def _r0240_toFinite_apply_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.toFinite_apply_eq_zero_iff
    # μ.toFinite s = 0 ↔ μ s = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_toFinite", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OOp("mu", (args[0],)))), OLit(0)))
            results.append((rhs, "Mathlib: MeasureTheory_toFinite_apply_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0241_toFinite_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.toFinite_eq_zero_iff
    # μ.toFinite = 0 ↔ μ = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mu_toFinite")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("mu"))), OLit(0)))
            results.append((rhs, "Mathlib: MeasureTheory_toFinite_eq_zero_iff"))
    except Exception:
        pass
    return results


def _r0242_toFinite_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.toFinite_zero
    # Measure.toFinite (0 : Measure α) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Measure_toFinite", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_toFinite_zero"))
        except Exception:
            pass
    return results


def _r0243_toFinite_eq_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.toFinite_eq_self
    # μ.toFinite = μ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mu_toFinite")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("mu")
            results.append((rhs, "Mathlib: MeasureTheory_toFinite_eq_self"))
    except Exception:
        pass
    return results


def _r0244_ae_le_set(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.ae_le_set
    # s ≤ᵐ[μ] t ↔ μ (s \\ t) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_ae_le_set"))
        except Exception:
            pass
    return results


def _r0245_ae_eq_set_compl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.ae_eq_set_compl
    # sᶜ =ᵐ[μ] t ↔ s =ᵐ[μ] tᶜ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OOp("mu", (OVar("t"),)), OOp("s", (OVar("eq_mu"), OVar("t"),))))
            results.append((rhs, "Mathlib: MeasureTheory_ae_eq_set_compl"))
    except Exception:
        pass
    return results


def _r0246_measure_union_null(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.measure_union_null
    # μ (s ∪ t) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_measure_union_null"))
        except Exception:
            pass
    return results


def _r0247_top_caratheodory(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.top_caratheodory
    # (⊤ : OuterMeasure α).caratheodory = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("top_colon_OuterMeasure_a_caratheodory")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: MeasureTheory_top_caratheodory"))
    except Exception:
        pass
    return results


def _r0248_add_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.OuterMeasure.add_apply
    # (m₁ + m₂) s = m₁ s + m₂ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m_1_plus_m_2", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("m_1", (args[0],)), OOp("m_2", (args[0],))))
            results.append((rhs, "Mathlib: MeasureTheory_OuterMeasure_add_apply"))
        except Exception:
            pass
    return results


def _r0249_smul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.OuterMeasure.smul_apply
    # (c • m) s = c • m s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_m", 1)
    if args is not None:
        try:
            rhs = OOp("c", (OVar("_unknown"), OVar("m"), args[0],))
            results.append((rhs, "Mathlib: MeasureTheory_OuterMeasure_smul_apply"))
        except Exception:
            pass
    return results


def _r0250_coe_iSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.coe_iSup
    # ⇑(⨆ i, f i) = ⨆ i, ⇑(f i)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("i_f_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_unknown", (OVar("i"), OVar("f_i"),))
            results.append((rhs, "Mathlib: MeasureTheory_coe_iSup"))
    except Exception:
        pass
    return results


def _r0251_smul_iSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.smul_iSup
    # (c • ⨆ i, f i) = ⨆ i, c • f i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c", 5)
    if args is not None:
        try:
            rhs = OOp("_unknown", (args[4], OVar("c"), args[1], args[3], args[4],))
            results.append((rhs, "Mathlib: MeasureTheory_smul_iSup"))
        except Exception:
            pass
    return results


def _r0252_not_measurable(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.VectorMeasure.not_measurable
    # v i = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "v", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_VectorMeasure_not_measurable"))
        except Exception:
            pass
    return results


def _r0253_smul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.smul_apply
    # (r • v) i = r • v i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "r_v", 1)
    if args is not None:
        try:
            rhs = OOp("r", (OVar("_unknown"), OVar("v"), args[0],))
            results.append((rhs, "Mathlib: MeasureTheory_smul_apply"))
        except Exception:
            pass
    return results


def _r0254_toENNRealVectorMeasure_ennrealToMeasure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.toENNRealVectorMeasure_ennrealToMeasure
    # toENNRealVectorMeasure (ennrealToMeasure μ) = μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toENNRealVectorMeasure", 1)
    if args is not None:
        try:
            rhs = OVar("mu")
            results.append((rhs, "Mathlib: MeasureTheory_Measure_toENNRealVectorMeasure_ennrealToMeasure"))
        except Exception:
            pass
    return results


def _r0255_zero_negPart(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.JordanDecomposition.zero_negPart
    # (0 : JordanDecomposition α).negPart = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_JordanDecomposition_a_negPart")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_JordanDecomposition_zero_negPart"))
    except Exception:
        pass
    return results


def _r0256_neg_posPart(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.JordanDecomposition.neg_posPart
    # (-j).posPart = j.negPart
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_j_posPart")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("j_negPart")
            results.append((rhs, "Mathlib: MeasureTheory_JordanDecomposition_neg_posPart"))
    except Exception:
        pass
    return results


def _r0257_neg_negPart(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.JordanDecomposition.neg_negPart
    # (-j).negPart = j.posPart
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_j_negPart")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("j_posPart")
            results.append((rhs, "Mathlib: MeasureTheory_JordanDecomposition_neg_negPart"))
    except Exception:
        pass
    return results


def _r0258_smul_posPart(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.JordanDecomposition.smul_posPart
    # (r • j).posPart = r • j.posPart
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r_j_posPart")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("r", (OVar("_unknown"), OVar("j_posPart"),))
            results.append((rhs, "Mathlib: MeasureTheory_JordanDecomposition_smul_posPart"))
    except Exception:
        pass
    return results


def _r0259_smul_negPart(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.JordanDecomposition.smul_negPart
    # (r • j).negPart = r • j.negPart
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r_j_negPart")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("r", (OVar("_unknown"), OVar("j_negPart"),))
            results.append((rhs, "Mathlib: MeasureTheory_JordanDecomposition_smul_negPart"))
    except Exception:
        pass
    return results


def _r0260_real_smul_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.JordanDecomposition.real_smul_def
    # r • j = if 0 ≤ r then r.toNNReal • j else -((-r).toNNReal • j)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "r", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("if", (OLit(0),)), OOp("-", (OOp("r", (OVar("then"), OVar("r_toNNReal"), args[0], args[1], OVar("else"),)), OOp("minus_r_toNNReal", (args[0], args[1],))))))
            results.append((rhs, "Mathlib: MeasureTheory_JordanDecomposition_real_smul_def"))
        except Exception:
            pass
    return results


def _r0261_real_smul_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.JordanDecomposition.real_smul_nonneg
    # r • j = r.toNNReal • j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "r", 2)
    if args is not None:
        try:
            rhs = OOp("r_toNNReal", (args[0], args[1],))
            results.append((rhs, "Mathlib: MeasureTheory_JordanDecomposition_real_smul_nonneg"))
        except Exception:
            pass
    return results


def _r0262_ennrealVariation_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.VectorMeasure.ennrealVariation_apply
    # μ.ennrealVariation s = μ.variation s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_ennrealVariation", 1)
    if args is not None:
        try:
            rhs = OOp("mu_variation", (args[0],))
            results.append((rhs, "Mathlib: MeasureTheory_VectorMeasure_ennrealVariation_apply"))
        except Exception:
            pass
    return results


def _r0263_serreDerivative_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Derivative.serreDerivative_eq
    # serreDerivative k F = fun z ↦ D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "serreDerivative", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("-", (OOp("fun", (OVar("z"), OVar("_unknown"), OVar("D"), args[1], OVar("z"),)), args[0])), OOp("*", (OVar("_12inv"), OOp("*", (OOp("EisensteinSeries_E2", (OVar("z"),)), OOp("F", (OVar("z"),))))))))
            results.append((rhs, "Mathlib: Derivative_serreDerivative_eq"))
        except Exception:
            pass
    return results


def _r0264_limsup_of_not_isBoundedUnder(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.limsup_of_not_isBoundedUnder
    # limsup u f = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "limsup", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: NNReal_limsup_of_not_isBoundedUnder"))
        except Exception:
            pass
    return results


def _r0265_liminf_of_not_isCoboundedUnder(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.liminf_of_not_isCoboundedUnder
    # liminf u f = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "liminf", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: NNReal_liminf_of_not_isCoboundedUnder"))
        except Exception:
            pass
    return results


def _r0266_toReal_liminf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.toReal_liminf
    # liminf (fun i ↦ (u i : ℝ)) f = liminf u f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "liminf", 2)
    if args is not None:
        try:
            rhs = OOp("liminf", (OVar("u"), args[1],))
            results.append((rhs, "Mathlib: NNReal_toReal_liminf"))
        except Exception:
            pass
    return results


def _r0267_deterministic_comp_eq_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.deterministic_comp_eq_map
    # Kernel.deterministic f hf ∘ₘ μ = μ.map f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Kernel_deterministic", 4)
    if args is not None:
        try:
            rhs = OOp("mu_map", (args[0],))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_deterministic_comp_eq_map"))
        except Exception:
            pass
    return results


def _r0268_swap_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.swap_comp
    # (Kernel.swap α β) ∘ₘ μ = μ.map Prod.swap
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Kernel_swap_a_b", 2)
    if args is not None:
        try:
            rhs = OOp("mu_map", (OVar("Prod_swap"),))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_swap_comp"))
        except Exception:
            pass
    return results


def _r0269_map_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.map_comp
    # (κ ∘ₘ μ).map f = (κ.map f) ∘ₘ μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "k_comp_mu_map", 1)
    if args is not None:
        try:
            rhs = OOp("k_map_f", (OVar("comp"), OVar("mu"),))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_map_comp"))
        except Exception:
            pass
    return results


def _r0270_copy_comp_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.copy_comp_map
    # Kernel.copy β ∘ₘ (μ.map f) = μ.map (fun a ↦ (f a, f a))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Kernel_copy", 3)
    if args is not None:
        try:
            rhs = OOp("mu_map", (OOp("fun", (OVar("a"), OVar("_unknown"), OOp("f", (OVar("a"), OVar("f"), OVar("a"),)),)),))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_copy_comp_map"))
        except Exception:
            pass
    return results


def _r0271_compProd_apply_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.compProd_apply_prod
    # (μ ⊗ₘ κ) (s ×ˢ t) = ∫⁻ a in s, κ a t ∂μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_k", 1)
    if args is not None:
        try:
            rhs = OOp("inv", (OVar("a"), OVar("in"), OVar("s"), OVar("k"), OVar("a"), OVar("t"), OVar("mu"),))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_compProd_apply_prod"))
        except Exception:
            pass
    return results


def _r0272_compProd_zero_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.compProd_zero_right
    # μ ⊗ₘ (0 : Kernel α β) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MeasureTheory_Measure_compProd_zero_right"))
        except Exception:
            pass
    return results


def _r0273_compProd_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.compProd_eq_zero_iff
    # μ ⊗ₘ κ = 0 ↔ ∀ᵐ a ∂μ, κ a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OOp("forall", (OVar("a"), OVar("mu"), args[1], OVar("a"),)))), OLit(0)))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_compProd_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0274_stronglyAdapted_predictablePart(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.stronglyAdapted_predictablePart
    # StronglyAdapted ℱ fun n => predictablePart f ℱ μ (n + 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "StronglyAdapted", 3)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("predictablePart"), OVar("f"), args[0], OVar("mu"), OOp("+", (args[2], OLit(1))),))
            results.append((rhs, "Mathlib: MeasureTheory_stronglyAdapted_predictablePart"))
        except Exception:
            pass
    return results


def _r0275_lowerCrossingTime_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.lowerCrossingTime_zero
    # lowerCrossingTime a b f N 0 = hittingBtwn f (Set.Iic a) ⊥ N
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lowerCrossingTime", 5)
    if args is not None:
        try:
            rhs = OOp("hittingBtwn", (args[2], OOp("Set_Iic", (args[0],)), OVar("bot"), args[3],))
            results.append((rhs, "Mathlib: MeasureTheory_lowerCrossingTime_zero"))
        except Exception:
            pass
    return results


def _r0276_upperCrossingTime_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.upperCrossingTime_succ
    # upperCrossingTime a b f N (n + 1) ω =     hittingBtwn f (Set.Ici b)       (lowerCrossingTimeAux a f (upperCrossingTime a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "upperCrossingTime", 6)
    if args is not None:
        try:
            rhs = OOp("hittingBtwn", (args[2], OOp("Set_Ici", (args[1],)), OOp("lowerCrossingTimeAux", (args[0], args[2], OOp("upperCrossingTime", (args[0], args[1], args[2], args[3], OVar("n"), args[5],)), args[3], args[5],)), args[3], args[5],))
            results.append((rhs, "Mathlib: MeasureTheory_upperCrossingTime_succ"))
        except Exception:
            pass
    return results


def _r0277_hittingAfter_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.hittingAfter_empty
    # hittingAfter u ∅ n = fun _ ↦ ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hittingAfter", 3)
    if args is not None:
        try:
            rhs = OOp("fun", (OVar("_unknown"), OVar("_unknown"), OVar("top"),))
            results.append((rhs, "Mathlib: MeasureTheory_hittingAfter_empty"))
        except Exception:
            pass
    return results


def _r0278_hittingBtwn_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.hittingBtwn_univ
    # hittingBtwn u .univ n m = fun _ ↦ min n m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hittingBtwn", 4)
    if args is not None:
        try:
            rhs = OOp("fun", (OVar("_unknown"), OVar("_unknown"), OVar("min"), args[2], args[3],))
            results.append((rhs, "Mathlib: MeasureTheory_hittingBtwn_univ"))
        except Exception:
            pass
    return results


def _r0279_leibniz(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Derivation.leibniz
    # D (a * b) = a • D b + b • D a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "D", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("a", (OVar("_unknown"), OVar("D"), OVar("b"),)), OOp("b", (OVar("_unknown"), OVar("D"), OVar("a"),))))
            results.append((rhs, "Mathlib: Derivation_leibniz"))
        except Exception:
            pass
    return results


def _r0280_map_smul_of_tower(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Derivation.map_smul_of_tower
    # D (r • a) = r • D a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "D", 1)
    if args is not None:
        try:
            rhs = OOp("r", (OVar("_unknown"), OVar("D"), OVar("a"),))
            results.append((rhs, "Mathlib: Derivation_map_smul_of_tower"))
        except Exception:
            pass
    return results


def _r0281_map_algebraMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Derivation.map_algebraMap
    # D (algebraMap R A r) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "D", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Derivation_map_algebraMap"))
        except Exception:
            pass
    return results


def _r0282_map_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Derivation.map_natCast
    # D (n : A) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "D", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Derivation_map_natCast"))
        except Exception:
            pass
    return results


def _r0283_leibniz_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Derivation.leibniz_pow
    # D (a ^ n) = n • a ^ (n - 1) • D a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "D", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("n", (OVar("_unknown"), OVar("a"),)), OOp("n_minus_1", (OVar("_unknown"), OVar("D"), OVar("a"),))))
            results.append((rhs, "Mathlib: Derivation_leibniz_pow"))
        except Exception:
            pass
    return results


def _r0284_coe_zero_linearMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Derivation.coe_zero_linearMap
    # ↑(0 : Derivation R A M) = (0 : A →ₗ[R] M)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_Derivation_R_A_M")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_0", (OVar("colon"), OVar("A"), OVar("to_R"), OVar("M"),))
            results.append((rhs, "Mathlib: Derivation_coe_zero_linearMap"))
    except Exception:
        pass
    return results


def _r0285_zero_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Derivation.zero_apply
    # (0 : Derivation R A M) a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_Derivation_R_A_M", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Derivation_zero_apply"))
        except Exception:
            pass
    return results


def _r0286_coe_add_linearMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Derivation.coe_add_linearMap
    # ↑(D1 + D2) = (D1 + D2 : A →ₗ[R] M)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("D1_plus_D2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("D1"), OOp("D2", (OVar("colon"), OVar("A"), OVar("to_R"), OVar("M"),))))
            results.append((rhs, "Mathlib: Derivation_coe_add_linearMap"))
    except Exception:
        pass
    return results


def _r0287_add_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Derivation.add_apply
    # (D1 + D2) a = D1 a + D2 a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "D1_plus_D2", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("D1", (args[0],)), OOp("D2", (args[0],))))
            results.append((rhs, "Mathlib: Derivation_add_apply"))
        except Exception:
            pass
    return results


def _r0288_coe_smul_linearMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Derivation.coe_smul_linearMap
    # ↑(r • D) = r • (D : A →ₗ[R] M)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r_D")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("r", (OVar("_unknown"), OOp("D", (OVar("colon"), OVar("A"), OVar("to_R"), OVar("M"),)),))
            results.append((rhs, "Mathlib: Derivation_coe_smul_linearMap"))
    except Exception:
        pass
    return results


def _r0289_smul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Derivation.smul_apply
    # (r • D) a = r • D a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "r_D", 1)
    if args is not None:
        try:
            rhs = OOp("r", (OVar("_unknown"), OVar("D"), args[0],))
            results.append((rhs, "Mathlib: Derivation_smul_apply"))
        except Exception:
            pass
    return results


def _r0290_commutator_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Derivation.commutator_apply
    # ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "D1", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("D1", (OOp("D2", (args[1],)),)), OOp("D2", (OOp("D1", (args[1],)),))))
            results.append((rhs, "Mathlib: Derivation_commutator_apply"))
        except Exception:
            pass
    return results


def _r0291_mapCoeffs_monomial(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Derivation.mapCoeffs_monomial
    # d.mapCoeffs (monomial n x) = .single A n (d x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "d_mapCoeffs", 1)
    if args is not None:
        try:
            rhs = OOp("single", (OVar("A"), OVar("n"), OOp("d", (OVar("x"),)),))
            results.append((rhs, "Mathlib: Derivation_mapCoeffs_monomial"))
        except Exception:
            pass
    return results


def _r0292_mapCoeffs_C(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Derivation.mapCoeffs_C
    # d.mapCoeffs (C x) = .single A 0 (d x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "d_mapCoeffs", 1)
    if args is not None:
        try:
            rhs = OOp("single", (OVar("A"), OLit(0), OOp("d", (OVar("x"),)),))
            results.append((rhs, "Mathlib: Derivation_mapCoeffs_C"))
        except Exception:
            pass
    return results


def _r0293_to_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Mathlib.Meta.NormNum.IsNat.to_eq
    # {a a' : α} → IsNat a n → n = a' → a = a'   | _, _, ⟨rfl⟩, rfl => rfl  theorem IsNat.to_raw_eq {a : α} {n : ℕ} [AddMonoid
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("n_rawCast", (OVar("pipe"), OVar("e"), OVar("eq_gt"), OVar("e_theorem"), OVar("IsNat_of_raw"), OVar("a"), OSeq((OOp("AddMonoidWithOne", (OVar("a"),)),)), OOp("n", (OVar("colon"), OVar("_unknown"),)), OVar("colon"), OVar("IsNat"), OOp("n_rawCast", (OVar("colon"), OVar("a"),)), OVar("n"),))
            results.append((rhs, "Mathlib: Mathlib_Meta_NormNum_IsNat_to_eq"))
    except Exception:
        pass
    return results


def _r0294_to_isNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Mathlib.Meta.NormNum.IsInt.to_isNat
    # ∀ {a : α} {n}, IsInt a (.ofNat n) → IsNat a n   | _, _, ⟨rfl⟩ => ⟨by simp⟩  theorem IsNat.to_isInt {α} [Ring α] : ∀ {a :
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("n_rawCast", (OVar("pipe"), OVar("e"), OVar("eq_gt"), OVar("e_theorem"), OVar("IsInt_of_raw"), OVar("a"), OSeq((OOp("Ring", (OVar("a"),)),)), OOp("n", (OVar("colon"), OVar("_unknown"),)), OVar("colon"), OVar("IsInt"), OOp("n_rawCast", (OVar("colon"), OVar("a"),)), OVar("n"),))
            results.append((rhs, "Mathlib: Mathlib_Meta_NormNum_IsInt_to_isNat"))
    except Exception:
        pass
    return results


def _r0295_to_isNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Mathlib.Meta.NormNum.IsNNRat.to_isNat
    # ∀ {a : α} {n}, IsNNRat a (n) (nat_lit 1) → IsNat a n   | _, num, ⟨inv, rfl⟩ => have
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsNat", 6)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("have"),))
            results.append((rhs, "Mathlib: Mathlib_Meta_NormNum_IsNNRat_to_isNat"))
        except Exception:
            pass
    return results


def _r0296_tsum_eq_top_of_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.tsum_eq_top_of_eq_top
    # (∃ a, f a = ∞) → ∑' a, f a = ∞   | ⟨a, ha⟩ => top_unique <| ha ▸ ENNReal.le_tsum a  protected theorem lt_top_of_tsum_ne_
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prime", 3)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("subst", (OOp("inf", (OVar("pipe"), OVar("a_ha"), OVar("eq_gt"), OVar("top_unique"), OVar("lt_pipe"), OVar("ha"),)), OOp("ENNReal_le_tsum", (OVar("a_protected"), OVar("theorem"), OVar("lt_top_of_tsum_ne_top"), OVar("a_colon_a_to_ge_0inf"), OOp("!=", (OOp("tsum_ne_top", (OVar("colon"), OVar("prime"), OVar("i"), args[2], OVar("i"),)), OVar("inf"))), OOp("j", (OVar("colon"), args[2],)), OVar("colon"), args[2], OVar("j"),)))), OVar("inf")))
            results.append((rhs, "Mathlib: ENNReal_tsum_eq_top_of_eq_top"))
        except Exception:
            pass
    return results


def _r0297_tsum_const(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.tsum_const
    # ∑' _ : α, c = ENat.card α * c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prime", 4)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("ENat_card", (args[2],)), args[3]))
            results.append((rhs, "Mathlib: ENNReal_tsum_const"))
        except Exception:
            pass
    return results


def _r0298_map_coe_nhdsGT(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.map_coe_nhdsGT
    # (𝓝[>] x).map toReal = 𝓝[>] ↑x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "gt_x_map", 1)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("x"),))
            results.append((rhs, "Mathlib: NNReal_map_coe_nhdsGT"))
        except Exception:
            pass
    return results


def _r0299_map_coe_nhdsGE(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.map_coe_nhdsGE
    # (𝓝[≥] x).map toReal = 𝓝[≥] ↑x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ge_x_map", 1)
    if args is not None:
        try:
            rhs = OOp("ge", (OVar("x"),))
            results.append((rhs, "Mathlib: NNReal_map_coe_nhdsGE"))
        except Exception:
            pass
    return results


def _r0300_comap_coe_atTop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.comap_coe_atTop
    # comap toReal atTop = atTop
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comap", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: NNReal_comap_coe_atTop"))
        except Exception:
            pass
    return results


def _r0301_coeNNRealReal_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.coeNNRealReal_zero
    # ContinuousMap.coeNNRealReal 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ContinuousMap_coeNNRealReal", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: NNReal_coeNNRealReal_zero"))
        except Exception:
            pass
    return results


def _r0302_summable_one_div_rpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.summable_one_div_rpow
    # Summable (fun n => 1 / (n : ℝ≥0) ^ p : ℕ → ℝ≥0) ↔ 1 < p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Summable", 1)
    if args is not None:
        try:
            rhs = OOp("<", (OLit(1), OVar("p")))
            results.append((rhs, "Mathlib: NNReal_summable_one_div_rpow"))
        except Exception:
            pass
    return results


def _r0303_coe_ne_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_ne_coe
    # (p : ℝ≥0∞) ≠ q ↔ p ≠ q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OVar("p"), args[1]))
            results.append((rhs, "Mathlib: ENNReal_coe_ne_coe"))
        except Exception:
            pass
    return results


def _r0304_coe_le_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_le_coe
    # (↑r : ℝ≥0∞) ≤ ↑q ↔ r ≤ q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("r"), args[1]))
            results.append((rhs, "Mathlib: ENNReal_coe_le_coe"))
        except Exception:
            pass
    return results


def _r0305_coe_lt_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_lt_coe
    # (↑r : ℝ≥0∞) < ↑q ↔ r < q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("r"), args[1]))
            results.append((rhs, "Mathlib: ENNReal_coe_lt_coe"))
        except Exception:
            pass
    return results


def _r0306_coe_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_pos
    # 0 < (r : ℝ≥0∞) ↔ 0 < r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OLit(0), OVar("r")))
            results.append((rhs, "Mathlib: ENNReal_coe_pos"))
        except Exception:
            pass
    return results


def _r0307_coe_ne_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_ne_zero
    # (r : ℝ≥0∞) ≠ 0 ↔ r ≠ 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OVar("r"), OLit(0)))
            results.append((rhs, "Mathlib: ENNReal_coe_ne_zero"))
        except Exception:
            pass
    return results


def _r0308_coe_ne_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_ne_one
    # (r : ℝ≥0∞) ≠ 1 ↔ r ≠ 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OVar("r"), OLit(1)))
            results.append((rhs, "Mathlib: ENNReal_coe_ne_one"))
        except Exception:
            pass
    return results


def _r0309_coe_le_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_le_one_iff
    # ↑r ≤ (1 : ℝ≥0∞) ↔ r ≤ 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (args[0], OLit(1)))
            results.append((rhs, "Mathlib: ENNReal_coe_le_one_iff"))
        except Exception:
            pass
    return results


def _r0310_coe_lt_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.coe_lt_one_iff
    # (↑p : ℝ≥0∞) < 1 ↔ p < 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("p"), OLit(1)))
            results.append((rhs, "Mathlib: ENNReal_coe_lt_one_iff"))
        except Exception:
            pass
    return results


def _r0311_one_lt_coe_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.one_lt_coe_iff
    # 1 < (↑p : ℝ≥0∞) ↔ 1 < p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OLit(1), OVar("p")))
            results.append((rhs, "Mathlib: ENNReal_one_lt_coe_iff"))
        except Exception:
            pass
    return results


def _r0312_natCast_le_ofNNReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.natCast_le_ofNNReal
    # (n : ℝ≥0∞) ≤ r ↔ n ≤ r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("n"), args[1]))
            results.append((rhs, "Mathlib: ENNReal_natCast_le_ofNNReal"))
        except Exception:
            pass
    return results


def _r0313_ofNNReal_le_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofNNReal_le_natCast
    # r ≤ (n : ℝ≥0∞) ↔ r ≤ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (args[0], OVar("n")))
            results.append((rhs, "Mathlib: ENNReal_ofNNReal_le_natCast"))
        except Exception:
            pass
    return results


def _r0314_inv_ne_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.inv_ne_top
    # a⁻¹ ≠ ∞ ↔ a ≠ 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OVar("a"), OLit(0)))
            results.append((rhs, "Mathlib: ENNReal_inv_ne_top"))
        except Exception:
            pass
    return results


def _r0315_inv_ne_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.inv_ne_zero
    # a⁻¹ ≠ 0 ↔ a ≠ ∞
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OVar("a"), OVar("inf")))
            results.append((rhs, "Mathlib: ENNReal_inv_ne_zero"))
        except Exception:
            pass
    return results


def _r0316_inv_lt_iff_inv_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.inv_lt_iff_inv_lt
    # a⁻¹ < b ↔ b⁻¹ < a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("binv"), OVar("a")))
            results.append((rhs, "Mathlib: ENNReal_inv_lt_iff_inv_lt"))
        except Exception:
            pass
    return results


def _r0317_inv_le_iff_inv_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.inv_le_iff_inv_le
    # a⁻¹ ≤ b ↔ b⁻¹ ≤ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("binv"), OVar("a")))
            results.append((rhs, "Mathlib: ENNReal_inv_le_iff_inv_le"))
        except Exception:
            pass
    return results


def _r0318_one_le_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.one_le_inv
    # 1 ≤ a⁻¹ ↔ a ≤ 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("a"), OLit(1)))
            results.append((rhs, "Mathlib: ENNReal_one_le_inv"))
        except Exception:
            pass
    return results


def _r0319_one_lt_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.one_lt_inv
    # 1 < a⁻¹ ↔ a < 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("a"), OLit(1)))
            results.append((rhs, "Mathlib: ENNReal_one_lt_inv"))
        except Exception:
            pass
    return results


def _r0320_div_pos_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.div_pos_iff
    # 0 < a / b ↔ a ≠ 0 ∧ b ≠ ∞
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OVar("a"), OOp("!=", (OOp("and", (OLit(0), OVar("b"))), OVar("inf")))))
            results.append((rhs, "Mathlib: ENNReal_div_pos_iff"))
        except Exception:
            pass
    return results


def _r0321_div_ne_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.div_ne_zero
    # a / b ≠ 0 ↔ a ≠ 0 ∧ b ≠ ∞
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OVar("a"), OOp("!=", (OOp("and", (OLit(0), OVar("b"))), OVar("inf")))))
            results.append((rhs, "Mathlib: ENNReal_div_ne_zero"))
        except Exception:
            pass
    return results


def _r0322_ofReal_ne_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofReal_ne_zero_iff
    # ENNReal.ofReal r ≠ 0 ↔ 0 < r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OLit(0), OVar("r")))
            results.append((rhs, "Mathlib: ENNReal_ofReal_ne_zero_iff"))
        except Exception:
            pass
    return results


def _r0323_ofReal_lt_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofReal_lt_one
    # ENNReal.ofReal p < 1 ↔ p < 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("p"), OLit(1)))
            results.append((rhs, "Mathlib: ENNReal_ofReal_lt_one"))
        except Exception:
            pass
    return results


def _r0324_ofReal_lt_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofReal_lt_ofNat
    # ENNReal.ofReal p < ofNat(n) ↔ p < OfNat.ofNat n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("p"), OOp("OfNat_ofNat", (OVar("n"),))))
            results.append((rhs, "Mathlib: ENNReal_ofReal_lt_ofNat"))
        except Exception:
            pass
    return results


def _r0325_one_le_ofReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.one_le_ofReal
    # 1 ≤ ENNReal.ofReal p ↔ 1 ≤ p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OLit(1), OVar("p")))
            results.append((rhs, "Mathlib: ENNReal_one_le_ofReal"))
        except Exception:
            pass
    return results


def _r0326_ofNat_le_ofReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofNat_le_ofReal
    # ofNat(n) ≤ ENNReal.ofReal p ↔ OfNat.ofNat n ≤ p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("OfNat_ofNat", (OVar("n"),)), OVar("p")))
            results.append((rhs, "Mathlib: ENNReal_ofNat_le_ofReal"))
        except Exception:
            pass
    return results


def _r0327_ofReal_le_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofReal_le_one
    # ENNReal.ofReal r ≤ 1 ↔ r ≤ 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("r"), OLit(1)))
            results.append((rhs, "Mathlib: ENNReal_ofReal_le_one"))
        except Exception:
            pass
    return results


def _r0328_ofReal_le_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofReal_le_ofNat
    # ENNReal.ofReal r ≤ ofNat(n) ↔ r ≤ OfNat.ofNat n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("r"), OOp("OfNat_ofNat", (OVar("n"),))))
            results.append((rhs, "Mathlib: ENNReal_ofReal_le_ofNat"))
        except Exception:
            pass
    return results


def _r0329_one_lt_ofReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.one_lt_ofReal
    # 1 < ENNReal.ofReal r ↔ 1 < r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OLit(1), OVar("r")))
            results.append((rhs, "Mathlib: ENNReal_one_lt_ofReal"))
        except Exception:
            pass
    return results


def _r0330_ofNat_lt_ofReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofNat_lt_ofReal
    # ofNat(n) < ENNReal.ofReal r ↔ OfNat.ofNat n < r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("OfNat_ofNat", (OVar("n"),)), OVar("r")))
            results.append((rhs, "Mathlib: ENNReal_ofNat_lt_ofReal"))
        except Exception:
            pass
    return results


def _r0331_ofReal_lt_coe_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.ofReal_lt_coe_iff
    # ENNReal.ofReal a < b ↔ a < b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("a"), args[1]))
            results.append((rhs, "Mathlib: ENNReal_ofReal_lt_coe_iff"))
        except Exception:
            pass
    return results


def _r0332_bddAbove_range_natCast_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.bddAbove_range_natCast_iff
    # BddAbove (Set.range (f ·) : Set NNReal) ↔ BddAbove (Set.range f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "BddAbove", 1)
    if args is not None:
        try:
            rhs = OOp("BddAbove", (OOp("Set_range", (OVar("f"),)),))
            results.append((rhs, "Mathlib: NNReal_bddAbove_range_natCast_iff"))
        except Exception:
            pass
    return results


def _r0333_sqrt_le_sqrt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.sqrt_le_sqrt
    # sqrt x ≤ sqrt y ↔ x ≤ y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("x"), OVar("y")))
            results.append((rhs, "Mathlib: NNReal_sqrt_le_sqrt"))
        except Exception:
            pass
    return results


def _r0334_sqrt_lt_sqrt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.sqrt_lt_sqrt
    # sqrt x < sqrt y ↔ x < y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("x"), OVar("y")))
            results.append((rhs, "Mathlib: NNReal_sqrt_lt_sqrt"))
        except Exception:
            pass
    return results


def _r0335_sqrt_le_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.sqrt_le_one
    # sqrt x ≤ 1 ↔ x ≤ 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("x"), OLit(1)))
            results.append((rhs, "Mathlib: NNReal_sqrt_le_one"))
        except Exception:
            pass
    return results


def _r0336_one_le_sqrt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.one_le_sqrt
    # 1 ≤ sqrt x ↔ 1 ≤ x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OLit(1), OVar("x")))
            results.append((rhs, "Mathlib: NNReal_one_le_sqrt"))
        except Exception:
            pass
    return results


def _r0337_integrableOn_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.integrableOn_univ
    # IntegrableOn f univ μ ↔ Integrable f μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IntegrableOn", 3)
    if args is not None:
        try:
            rhs = OOp("Integrable", (args[0], args[2],))
            results.append((rhs, "Mathlib: MeasureTheory_integrableOn_univ"))
        except Exception:
            pass
    return results


def _r0338_integrableOn_fun_neg_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.integrableOn_fun_neg_iff
    # IntegrableOn (fun x ↦ -f x) s μ ↔ IntegrableOn f s μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IntegrableOn", 3)
    if args is not None:
        try:
            rhs = OOp("IntegrableOn", (OVar("f"), args[1], args[2],))
            results.append((rhs, "Mathlib: MeasureTheory_integrableOn_fun_neg_iff"))
        except Exception:
            pass
    return results


def _r0339_union_right_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.AEDisjoint.union_right_iff
    # AEDisjoint μ s (t ∪ u) ↔ AEDisjoint μ s t ∧ AEDisjoint μ s u
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "AEDisjoint", 3)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("AEDisjoint", (args[0], args[1], OVar("t"),)), OOp("AEDisjoint", (args[0], args[1], OVar("u"),))))
            results.append((rhs, "Mathlib: MeasureTheory_AEDisjoint_union_right_iff"))
        except Exception:
            pass
    return results


def _r0340_restrict_nonzero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.FiniteMeasure.restrict_nonzero_iff
    # μ.restrict A ≠ 0 ↔ μ A ≠ 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("mu", (OVar("A"),)), OLit(0)))
            results.append((rhs, "Mathlib: MeasureTheory_FiniteMeasure_restrict_nonzero_iff"))
        except Exception:
            pass
    return results


def _r0341_add_left_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.MutuallySingular.add_left_iff
    # μ₁ + μ₂ ⟂ₘ ν ↔ μ₁ ⟂ₘ ν ∧ μ₂ ⟂ₘ ν
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("mu_1", (OVar("_unknown"), OVar("nu"),)), OOp("mu_2", (OVar("_unknown"), OVar("nu"),))))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_MutuallySingular_add_left_iff"))
        except Exception:
            pass
    return results


def _r0342_add_right_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.MutuallySingular.add_right_iff
    # μ ⟂ₘ ν₁ + ν₂ ↔ μ ⟂ₘ ν₁ ∧ μ ⟂ₘ ν₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("mu", (OVar("_unknown"), OVar("nu_1"),)), OOp("mu", (OVar("_unknown"), args[1],))))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_MutuallySingular_add_right_iff"))
        except Exception:
            pass
    return results


def _r0343_le_boundedBy(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.le_boundedBy
    # μ ≤ boundedBy m ↔ ∀ s, μ s ≤ m s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("forall", (OVar("s"), args[0], OVar("s"),)), OOp("m", (OVar("s"),))))
            results.append((rhs, "Mathlib: MeasureTheory_le_boundedBy"))
        except Exception:
            pass
    return results


def _r0344_hasSum_iff_tendsto_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENNReal.hasSum_iff_tendsto_nat
    # HasSum f r ↔ Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (𝓝 r)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "HasSum", 2)
    if args is not None:
        try:
            rhs = OOp("Tendsto", (OOp("in", (OOp("fun", (OVar("n"), OVar("colon"), OVar("_unknown"), OVar("eq_gt"), OVar("_unknown"), OVar("i"),)), OOp("range", (OVar("n"), args[0], OVar("i"),)))), OVar("atTop"), OOp("_unknown", (args[1],)),))
            results.append((rhs, "Mathlib: ENNReal_hasSum_iff_tendsto_nat"))
        except Exception:
            pass
    return results


def _r0345_tendsto_coe_atTop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.tendsto_coe_atTop
    # Tendsto (fun a => (m a : ℝ)) f atTop ↔ Tendsto m f atTop
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Tendsto", 3)
    if args is not None:
        try:
            rhs = OOp("Tendsto", (OVar("m"), args[1], args[2],))
            results.append((rhs, "Mathlib: NNReal_tendsto_coe_atTop"))
        except Exception:
            pass
    return results


def _r0346_congr_d(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PresheafOfModules.Derivation.congr_d
    # d.d b = d'.d b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "d_d", 1)
    if args is not None:
        try:
            rhs = OOp("d_prime_d", (args[0],))
            results.append((rhs, "Mathlib: PresheafOfModules_Derivation_congr_d"))
        except Exception:
            pass
    return results


def _r0347_d_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PresheafOfModules.Derivation.d_one
    # d.d (X := X) 1 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "d_d", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: PresheafOfModules_Derivation_d_one"))
        except Exception:
            pass
    return results


def _r0348_d_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PresheafOfModules.Derivation.d_app
    # d.d (φ'.app X a) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "d_d", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: PresheafOfModules_Derivation_d_app"))
        except Exception:
            pass
    return results


def _r0349_app_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PresheafOfModules.Derivation.app_apply
    # (d.app X).d b = d.d b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "d_app_X_d", 1)
    if args is not None:
        try:
            rhs = OOp("d_d", (args[0],))
            results.append((rhs, "Mathlib: PresheafOfModules_Derivation_app_apply"))
        except Exception:
            pass
    return results


def _r0350_mk_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PresheafOfModules.Derivation.mk_app
    # (mk d d_map).app X = d X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mk_d_d_map_app", 1)
    if args is not None:
        try:
            rhs = OOp("d", (args[0],))
            results.append((rhs, "Mathlib: PresheafOfModules_Derivation_mk_app"))
        except Exception:
            pass
    return results


def _r0351_conjAct(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Normal.conjAct
    # g • H = H
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Normal_conjAct"))
        except Exception:
            pass
    return results


def _r0352_conj_smul_eq_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Normal.conj_smul_eq_self
    # MulAut.conj g • H = H
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "MulAut_conj", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: Normal_conj_smul_eq_self"))
        except Exception:
            pass
    return results


def _r0353_to_singleFunctor_obj_eq_zero_of_injectiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.to_singleFunctor_obj_eq_zero_of_injective
    # φ = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: DerivedCategory_to_singleFunctor_obj_eq_zero_of_injective"))
    except Exception:
        pass
    return results


def _r0354_from_singleFunctor_obj_eq_zero_of_projec(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective
    # φ = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: DerivedCategory_from_singleFunctor_obj_eq_zero_of_projective"))
    except Exception:
        pass
    return results


def _r0355_right_fac(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.right_fac
    # ∃ (X' : CochainComplex C ℤ) (s : X' ⟶ X) (_ : IsIso (Q.map s)) (g : X' ⟶ Y),       f = inv (Q.map s) ≫ Q.map g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 5)
    if args is not None:
        try:
            rhs = OOp("inv", (OOp("Q_map", (OVar("s"),)), OVar("_unknown"), OVar("Q_map"), OVar("g"),))
            results.append((rhs, "Mathlib: DerivedCategory_right_fac"))
        except Exception:
            pass
    return results


def _r0356_left_fac(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.left_fac
    # ∃ (Y' : CochainComplex C ℤ) (g : X ⟶ Y') (s : Y ⟶ Y') (_ : IsIso (Q.map s)),       f = Q.map g ≫ inv (Q.map s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 5)
    if args is not None:
        try:
            rhs = OOp("Q_map", (OVar("g"), OVar("_unknown"), OVar("inv"), OOp("Q_map", (OVar("s"),)),))
            results.append((rhs, "Mathlib: DerivedCategory_left_fac"))
        except Exception:
            pass
    return results


def _r0357_right_fac_of_isStrictlyLE(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.right_fac_of_isStrictlyLE
    # ∃ (X' : CochainComplex C ℤ) (_ : X'.IsStrictlyLE n) (s : X' ⟶ X) (_ : IsIso (Q.map s))       (g : X' ⟶ Y), f = inv (Q.ma
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 6)
    if args is not None:
        try:
            rhs = OOp("inv", (OOp("Q_map", (OVar("s"),)), OVar("_unknown"), OVar("Q_map"), OVar("g"),))
            results.append((rhs, "Mathlib: DerivedCategory_right_fac_of_isStrictlyLE"))
        except Exception:
            pass
    return results


def _r0358_left_fac_of_isStrictlyGE(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.left_fac_of_isStrictlyGE
    # ∃ (Y' : CochainComplex C ℤ) (_ : Y'.IsStrictlyGE n) (g : X ⟶ Y') (s : Y ⟶ Y')       (_ : IsIso (Q.map s)), f = Q.map g ≫
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 6)
    if args is not None:
        try:
            rhs = OOp("Q_map", (OVar("g"), OVar("_unknown"), OVar("inv"), OOp("Q_map", (OVar("s"),)),))
            results.append((rhs, "Mathlib: DerivedCategory_left_fac_of_isStrictlyGE"))
        except Exception:
            pass
    return results


def _r0359_right_fac_of_isStrictlyLE_of_isStrictlyG(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.right_fac_of_isStrictlyLE_of_isStrictlyGE
    # ∃ (X' : CochainComplex C ℤ) (_ : X'.IsStrictlyGE a) (_ : X'.IsStrictlyLE b)     (s : X' ⟶ X) (_ : IsIso (Q.map s)) (g : 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 7)
    if args is not None:
        try:
            rhs = OOp("inv", (OOp("Q_map", (OVar("s"),)), OVar("_unknown"), OVar("Q_map"), OVar("g"),))
            results.append((rhs, "Mathlib: DerivedCategory_right_fac_of_isStrictlyLE_of_isStrictlyGE"))
        except Exception:
            pass
    return results


def _r0360_left_fac_of_isStrictlyLE_of_isStrictlyGE(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.left_fac_of_isStrictlyLE_of_isStrictlyGE
    # ∃ (Y' : CochainComplex C ℤ) (_ : Y'.IsStrictlyGE a) (_ : Y'.IsStrictlyLE b)     (g : X ⟶ Y') (s : Y ⟶ Y') (_ : IsIso (Q.
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 7)
    if args is not None:
        try:
            rhs = OOp("Q_map", (OVar("g"), OVar("_unknown"), OVar("inv"), OOp("Q_map", (OVar("s"),)),))
            results.append((rhs, "Mathlib: DerivedCategory_left_fac_of_isStrictlyLE_of_isStrictlyGE"))
        except Exception:
            pass
    return results


def _r0361_homologyFunctorFactors_hom_naturality(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.homologyFunctorFactors_hom_naturality
    # (homologyFunctor C n).map (Q.map f) ≫ (homologyFunctorFactors C n).hom.app L =     (homologyFunctorFactors C n).hom.app 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homologyFunctor_C_n_map", 4)
    if args is not None:
        try:
            rhs = OOp("homologyFunctorFactors_C_n_hom_app", (OVar("K"), args[1], OVar("HomologicalComplex_homologyMap"), OVar("f"), OVar("n"),))
            results.append((rhs, "Mathlib: DerivedCategory_homologyFunctorFactors_hom_naturality"))
        except Exception:
            pass
    return results


def _r0362_homologyFunctorFactorsh_hom_app_quotient(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj
    # (homologyFunctorFactorsh C n).hom.app ((HomotopyCategory.quotient _ _).obj K) =     (homologyFunctor C n).map ((quotient
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homologyFunctorFactorsh_C_n_hom_app", 1)
    if args is not None:
        try:
            rhs = OOp("homologyFunctor_C_n_map", (OOp("quotientCompQhIso_C_hom_app", (OVar("K"),)), OVar("_unknown"), OVar("homologyFunctorFactors_C_n_hom_app"), OVar("K"), OVar("_unknown"), OVar("HomotopyCategory_homologyFunctorFactors_C_up_n_inv_app"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: DerivedCategory_homologyFunctorFactorsh_hom_app_quotient_obj"))
        except Exception:
            pass
    return results


def _r0363_homologyFunctorFactorsh_inv_app_quotient(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.homologyFunctorFactorsh_inv_app_quotient_obj
    # (homologyFunctorFactorsh C n).inv.app ((HomotopyCategory.quotient _ _).obj K) =     (HomotopyCategory.homologyFunctorFac
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homologyFunctorFactorsh_C_n_inv_app", 1)
    if args is not None:
        try:
            rhs = OOp("HomotopyCategory_homologyFunctorFactors_C_up_n_hom_app", (OVar("_unknown"), OVar("_unknown"), OVar("homologyFunctorFactors_C_n_inv_app"), OVar("K"), OVar("_unknown"), OVar("homologyFunctor_C_n_map"), OOp("quotientCompQhIso_C_inv_app", (OVar("K"),)),))
            results.append((rhs, "Mathlib: DerivedCategory_homologyFunctorFactorsh_inv_app_quotient_obj"))
        except Exception:
            pass
    return results


def _r0364_shift_homologyFunctor(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.shift_homologyFunctor
    # (homologyFunctor C 0).shift n = homologyFunctor C n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homologyFunctor_C_0_shift", 1)
    if args is not None:
        try:
            rhs = OOp("homologyFunctor", (OVar("C"), args[0],))
            results.append((rhs, "Mathlib: DerivedCategory_shift_homologyFunctor"))
        except Exception:
            pass
    return results


def _r0365_shiftMap_homologyFunctor_map_Qh(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.shiftMap_homologyFunctor_map_Qh
    # (homologyFunctor C 0).shiftMap (ShiftedHom.map f Qh) a a' h =     (homologyFunctorFactorsh C a).hom.app _ ≫       (Homot
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homologyFunctor_C_0_shiftMap", 4)
    if args is not None:
        try:
            rhs = OOp("homologyFunctorFactorsh_C_a_hom_app", (OVar("_unknown"), OVar("_unknown"), OVar("HomotopyCategory_homologyFunctor_C_up_0_shiftMap"), OVar("f"), args[1], args[2], args[3], OVar("_unknown"), OVar("homologyFunctorFactorsh_C_a_prime_inv_app"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: DerivedCategory_shiftMap_homologyFunctor_map_Qh"))
        except Exception:
            pass
    return results


def _r0366_shiftMap_homologyFunctor_map_Q(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.shiftMap_homologyFunctor_map_Q
    # (homologyFunctor C 0).shiftMap (ShiftedHom.map f Q) a a' h =     (homologyFunctorFactors C a).hom.app _ ≫       (Homolog
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homologyFunctor_C_0_shiftMap", 4)
    if args is not None:
        try:
            rhs = OOp("homologyFunctorFactors_C_a_hom_app", (OVar("_unknown"), OVar("_unknown"), OVar("HomologicalComplex_homologyFunctor_C_up_0_shiftMap"), OVar("f"), args[1], args[2], args[3], OVar("_unknown"), OVar("homologyFunctorFactors_C_a_prime_inv_app"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: DerivedCategory_shiftMap_homologyFunctor_map_Q"))
        except Exception:
            pass
    return results


def _r0367_comp_d(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.HomologySequence.comp_δ
    # (homologyFunctor C n₀).map T.mor₂ ≫ δ T n₀ n₁ h = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homologyFunctor_C_n_0_map", 7)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: DerivedCategory_HomologySequence_comp_d"))
        except Exception:
            pass
    return results


def _r0368_d_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.HomologySequence.δ_comp
    # δ T n₀ n₁ h ≫ (homologyFunctor C n₁).map T.mor₁ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "d", 7)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: DerivedCategory_HomologySequence_d_comp"))
        except Exception:
            pass
    return results


def _r0369_epi_homologyMap_mor_1_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff
    # Epi ((homologyFunctor C n₀).map T.mor₁) ↔ (homologyFunctor C n₀).map T.mor₂ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: DerivedCategory_HomologySequence_epi_homologyMap_mor_1_iff"))
        except Exception:
            pass
    return results


def _r0370_mono_homologyMap_mor_1_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
    # Mono ((homologyFunctor C n₁).map T.mor₁) ↔ δ T n₀ n₁ h = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: DerivedCategory_HomologySequence_mono_homologyMap_mor_1_iff"))
        except Exception:
            pass
    return results


def _r0371_epi_homologyMap_mor_2_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
    # Epi ((homologyFunctor C n₀).map T.mor₂) ↔ δ T n₀ n₁ h = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: DerivedCategory_HomologySequence_epi_homologyMap_mor_2_iff"))
        except Exception:
            pass
    return results


def _r0372_mono_homologyMap_mor_2_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff
    # Mono ((homologyFunctor C n₀).map T.mor₂) ↔ (homologyFunctor C n₀).map T.mor₁ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: DerivedCategory_HomologySequence_mono_homologyMap_mor_2_iff"))
        except Exception:
            pass
    return results


def _r0373_descShortComplex_triangleOfSESd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.descShortComplex_triangleOfSESδ
    # Q.map (CochainComplex.mappingCone.descShortComplex S) ≫ triangleOfSESδ hS =     Q.map (CochainComplex.mappingCone.triang
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Q_map", 4)
    if args is not None:
        try:
            rhs = OOp("Q_map", (OVar("CochainComplex_mappingCone_triangle_S_f_mor_3"), args[1], OVar("Functor_commShiftIso_Q_1_hom_app"), OVar("S_X_1"),))
            results.append((rhs, "Mathlib: DerivedCategory_descShortComplex_triangleOfSESd"))
        except Exception:
            pass
    return results


def _r0374_triangleOfSESd_naturality(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DerivedCategory.triangleOfSESδ_naturality
    # triangleOfSESδ hS₁ ≫ (Q.map f.τ₁)⟦1⟧' = Q.map f.τ₃ ≫ triangleOfSESδ hS₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "triangleOfSESd", 3)
    if args is not None:
        try:
            rhs = OOp("Q_map", (OVar("f_tau_3"), args[1], OVar("triangleOfSESd"), OVar("hS_2"),))
            results.append((rhs, "Mathlib: DerivedCategory_triangleOfSESd_naturality"))
        except Exception:
            pass
    return results


def _r0375_ofDerivation_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Lie.Derivation.ofDerivation_apply
    # ofDerivation L d x = d.toLinearMap.rTensor L x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofDerivation", 3)
    if args is not None:
        try:
            rhs = OOp("d_toLinearMap_rTensor", (args[0], args[2],))
            results.append((rhs, "Mathlib: Lie_Derivation_ofDerivation_apply"))
        except Exception:
            pass
    return results


def _r0376_ofLieDerivation_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Lie.Derivation.ofLieDerivation_apply
    # ofLieDerivation A d x = d.toLinearMap.lTensor A x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofLieDerivation", 3)
    if args is not None:
        try:
            rhs = OOp("d_toLinearMap_lTensor", (args[0], args[2],))
            results.append((rhs, "Mathlib: Lie_Derivation_ofLieDerivation_apply"))
        except Exception:
            pass
    return results


def _r0377_compAEval_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Derivation.compAEval_eq
    # d.compAEval a f = derivative f • (AEval.of R M a (d a))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "d_compAEval", 2)
    if args is not None:
        try:
            rhs = OOp("derivative", (args[1], OVar("_unknown"), OOp("AEval_of", (OVar("R"), OVar("M"), args[0], OOp("d", (args[0],)),)),))
            results.append((rhs, "Mathlib: Derivation_compAEval_eq"))
        except Exception:
            pass
    return results


def _r0378_comp_aeval_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Derivation.comp_aeval_eq
    # d (aeval a f) = aeval a (derivative f) • d a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "d", 1)
    if args is not None:
        try:
            rhs = OOp("aeval", (OVar("a"), OOp("derivative", (OVar("f"),)), OVar("_unknown"), OVar("d"), OVar("a"),))
            results.append((rhs, "Mathlib: Derivation_comp_aeval_eq"))
        except Exception:
            pass
    return results


def _r0379_box_integral_eq_integral(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.SimpleFunc.box_integral_eq_integral
    # BoxIntegral.integral.{u, v, v} I l f μ.toBoxAdditive.toSMul = f.integral (μ.restrict I)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "BoxIntegral_integral_u_v_v", 4)
    if args is not None:
        try:
            rhs = OOp("f_integral", (OOp("mu_restrict", (args[0],)),))
            results.append((rhs, "Mathlib: MeasureTheory_SimpleFunc_box_integral_eq_integral"))
        except Exception:
            pass
    return results


def _r0380_isBigO_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: HasDerivAtFilter.isBigO_sub
    # (fun p => f p.1 - f p.2) =O[L] fun p => p.1 - p.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("O_L", (OVar("fun"), OVar("p"), OVar("eq_gt"), OVar("p_1"),)), OVar("p_2")))
            results.append((rhs, "Mathlib: HasDerivAtFilter_isBigO_sub"))
        except Exception:
            pass
    return results


def _r0381_isBigO_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: HasDerivAt.isBigO_sub
    # (f · - f x) =O[𝓝 x] (· - x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("O_x", (OOp("-", (OVar("_unknown"), OVar("x"))),))
            results.append((rhs, "Mathlib: HasDerivAt_isBigO_sub"))
        except Exception:
            pass
    return results


def _r0382_isTheta_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: HasDerivAtFilter.isTheta_sub
    # (fun p ↦ f p.1 - f p.2) =Θ[L] (fun p ↦ p.1 - p.2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("L", (OOp("-", (OOp("fun", (OVar("p"), OVar("_unknown"), OVar("p_1"),)), OVar("p_2"))),))
            results.append((rhs, "Mathlib: HasDerivAtFilter_isTheta_sub"))
        except Exception:
            pass
    return results


def _r0383_isBigO_sub_rev(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: HasDerivAtFilter.isBigO_sub_rev
    # (fun p => p.1 - p.2) =O[L] fun p => f p.1 - f p.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("O_L", (OVar("fun"), OVar("p"), OVar("eq_gt"), OVar("f"), OVar("p_1"),)), OOp("f", (args[1],))))
            results.append((rhs, "Mathlib: HasDerivAtFilter_isBigO_sub_rev"))
        except Exception:
            pass
    return results


def _r0384_deriv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: HasDerivAt.deriv
    # deriv f x = f'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "deriv", 2)
    if args is not None:
        try:
            rhs = OVar("f_prime")
            results.append((rhs, "Mathlib: HasDerivAt_deriv"))
        except Exception:
            pass
    return results


def _r0385_segment_eq_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.segment_eq_Icc
    # segment ℝ≥0 x y = Icc x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "segment", 3)
    if args is not None:
        try:
            rhs = OOp("Icc", (args[1], args[2],))
            results.append((rhs, "Mathlib: NNReal_segment_eq_Icc"))
        except Exception:
            pass
    return results


def _r0386_segment_eq_uIcc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNReal.segment_eq_uIcc
    # segment ℝ≥0 x y = uIcc x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "segment", 3)
    if args is not None:
        try:
            rhs = OOp("uIcc", (args[1], args[2],))
            results.append((rhs, "Mathlib: NNReal_segment_eq_uIcc"))
        except Exception:
            pass
    return results


def _r0387_convolution_integrand_fst(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Continuous.convolution_integrand_fst
    # Continuous fun x => L (f t) (g (x - t))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Continuous", 2)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("L"), OOp("f", (OVar("t"),)), OOp("g", (OOp("-", (args[1], OVar("t"))),)),))
            results.append((rhs, "Mathlib: Continuous_convolution_integrand_fst"))
        except Exception:
            pass
    return results


def _r0388_toTemperedDistribution_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Measure.toTemperedDistribution_apply
    # μ.toTemperedDistribution g = ∫ (x : E), g x ∂μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu_toTemperedDistribution", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("x_colon_E"), args[0], OVar("x"), OVar("mu"),))
            results.append((rhs, "Mathlib: MeasureTheory_Measure_toTemperedDistribution_apply"))
        except Exception:
            pass
    return results


def _r0389_toTemperedDistribution_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Lp.toTemperedDistribution_apply
    # toTemperedDistribution f g = ∫ (x : E), g x • f x ∂μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toTemperedDistribution", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("x_colon_E"), args[1], OVar("x"), OVar("_unknown"), args[0], OVar("x"), OVar("mu"),))
            results.append((rhs, "Mathlib: MeasureTheory_Lp_toTemperedDistribution_apply"))
        except Exception:
            pass
    return results


def _r0390_toTemperedDistribution_toLp_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Lp.toTemperedDistribution_toLp_eq
    # ((f.toLp p μ) : 𝓢'(E, F)) = f.toTemperedDistributionCLM E F μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_toLp_p_mu", 2)
    if args is not None:
        try:
            rhs = OOp("f_toTemperedDistributionCLM", (OVar("E"), OVar("F"), OVar("mu"),))
            results.append((rhs, "Mathlib: MeasureTheory_Lp_toTemperedDistribution_toLp_eq"))
        except Exception:
            pass
    return results


def _r0391_toTemperedDistributionCLM_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Lp.toTemperedDistributionCLM_apply
    # toTemperedDistributionCLM F μ p f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toTemperedDistributionCLM", 4)
    if args is not None:
        try:
            rhs = args[3]
            results.append((rhs, "Mathlib: MeasureTheory_Lp_toTemperedDistributionCLM_apply"))
        except Exception:
            pass
    return results


def _r0392_ker_toTemperedDistributionCLM_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
    # (MeasureTheory.Lp.toTemperedDistributionCLM F μ p).ker = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("MeasureTheory_Lp_toTemperedDistributionCLM_F_mu_p_ker")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: MeasureTheory_Lp_ker_toTemperedDistributionCLM_eq_bot"))
    except Exception:
        pass
    return results


def _r0393_toTemperedDistribution_smul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Lp.toTemperedDistribution_smul_eq
    # ((hg₂.toLp _) • f : Lp F r μ) = smulLeftCLM F g f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hg_2_toLp", 7)
    if args is not None:
        try:
            rhs = OOp("smulLeftCLM", (args[4], OVar("g"), args[1],))
            results.append((rhs, "Mathlib: MeasureTheory_Lp_toTemperedDistribution_smul_eq"))
        except Exception:
            pass
    return results


def _r0394_fourierInv_fourier_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Integrable.fourierInv_fourier_eq
    # 𝓕⁻ (𝓕 f) v = f v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inv", 2)
    if args is not None:
        try:
            rhs = OOp("f", (args[1],))
            results.append((rhs, "Mathlib: MeasureTheory_Integrable_fourierInv_fourier_eq"))
        except Exception:
            pass
    return results


def _r0395_fourier_fourierInv_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Integrable.fourier_fourierInv_eq
    # 𝓕 (𝓕⁻ f) v = f v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 2)
    if args is not None:
        try:
            rhs = OOp("f", (args[1],))
            results.append((rhs, "Mathlib: MeasureTheory_Integrable_fourier_fourierInv_eq"))
        except Exception:
            pass
    return results


def _r0396_norm_fourier_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Lp.norm_fourier_eq
    # ‖𝓕 f‖ = ‖f‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: MeasureTheory_Lp_norm_fourier_eq"))
        except Exception:
            pass
    return results


def _r0397_fourier_toTemperedDistribution_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Lp.fourier_toTemperedDistribution_eq
    # 𝓕 (f : 𝓢'(E, F)) = (𝓕 f : Lp (α := E) F 2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("f"), OVar("colon"), OVar("Lp"), OOp("a", (OVar("colon_eq"), OVar("E"),)), OVar("F"), OLit(2),))
            results.append((rhs, "Mathlib: MeasureTheory_Lp_fourier_toTemperedDistribution_eq"))
        except Exception:
            pass
    return results


def _r0398_fourierInv_toTemperedDistribution_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq
    # 𝓕⁻ (f : 𝓢'(E, F)) = (𝓕⁻ f : Lp (α := E) F 2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inv", 1)
    if args is not None:
        try:
            rhs = OOp("inv", (OVar("f"), OVar("colon"), OVar("Lp"), OOp("a", (OVar("colon_eq"), OVar("E"),)), OVar("F"), OLit(2),))
            results.append((rhs, "Mathlib: MeasureTheory_Lp_fourierInv_toTemperedDistribution_eq"))
        except Exception:
            pass
    return results


def _r0399_T_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MeasureTheory.GridLines.T_univ
    # T μ p f univ x =     ∫⁻ (x : ∀ i, A i), (f x ^ (1 - (#ι - 1 : ℝ) * p)     * ∏ i : ι, (∫⁻ t : A i, f (update x i t) ∂(μ i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "T", 5)
    if args is not None:
        try:
            rhs = OOp("inv", (OVar("x_colon_forall_i_A_i"), OOp("*", (OOp("**", (OOp("f", (args[4],)), OOp("*", (OOp("-", (OLit(1), OOp("-", (OVar("hash_i"), OOp("_1", (OVar("colon"), OVar("_unknown"),)))))), args[1])))), OOp("**", (OOp("_unknown", (OVar("i"), OVar("colon"), OVar("i"), OOp("inv", (OVar("t"), OVar("colon"), OVar("A"), OVar("i"), args[2], OOp("update", (args[4], OVar("i"), OVar("t"),)), OVar("mu_i"),)),)), args[1])))), OVar("pi_mu"),))
            results.append((rhs, "Mathlib: MeasureTheory_GridLines_T_univ"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_analysis rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("!=", "*", "**", "+", "-", "//", "<", "<=", "AEDisjoint", "BddAbove", "BoxIntegral_integral_u_v_v", "C", "CochainComplex_mappingCone_descShortComplex", "Continuous", "ContinuousMap_coeNNRealReal", "D", "D1", "D1_plus_D2", "ENNReal_ofReal", "ENNReal_toNNReal", "ENNReal_toReal", "Epi", "FiniteMeasure_pi_mu", "FiniteMeasure_pi_mu_map", "FiniteMeasure_toMeasure", "HasSum", "HomotopyCategory_quotient_obj", "IntegrableOn", "IsNat", "Kernel_copy", "Kernel_deterministic", "Kernel_swap_a_b", "MeasurableSet", "Measure_map", "Measure_toFinite", "Measure_tprod", "Mono", "MulAut_conj", "ProbabilityMeasure_pi", "Q_map", "Real_toNNReal", "Set_pi", "Set_range", "ShiftedHom_map", "SimpleFunc_mk", "StronglyAdapted", "Summable", "T", "Tendsto", "X",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_analysis axioms."""
    if recognizes(term):
        return 0.6
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_analysis rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_unique(term, ctx))
    results.extend(_r0001_inner_fourier_eq(term, ctx))
    results.extend(_r0002_zero_mlconvolution(term, ctx))
    results.extend(_r0003_mlconvolution_zero(term, ctx))
    results.extend(_r0004_expSeries_apply_eq(term, ctx))
    results.extend(_r0005_coe_mk(term, ctx))
    results.extend(_r0006_add_apply(term, ctx))
    results.extend(_r0007_zero_apply(term, ctx))
    results.extend(_r0008_neg_apply(term, ctx))
    results.extend(_r0009_sub_apply(term, ctx))
    results.extend(_r0010_smul_apply(term, ctx))
    results.extend(_r0011_completion_coe(term, ctx))
    results.extend(_r0012_norm_completion(term, ctx))
    results.extend(_r0013_inclusionInDoubleDual_norm_eq(term, ctx))
    results.extend(_r0014_normalize_eq_zero_iff(term, ctx))
    results.extend(_r0015_norm_smul_normalize(term, ctx))
    results.extend(_r0016_norm_normalize_eq_one_iff(term, ctx))
    results.extend(_r0017_normalize_smul_of_pos(term, ctx))
    results.extend(_r0018_enorm_eq(term, ctx))
    results.extend(_r0019_agmSequences_succ(term, ctx))
    results.extend(_r0020_log_one(term, ctx))
    results.extend(_r0021_log_top(term, ctx))
    results.extend(_r0022_log_ofReal(term, ctx))
    results.extend(_r0023_logOrderIso_symm(term, ctx))
    results.extend(_r0024_expOrderIso_symm(term, ctx))
    results.extend(_r0025_coe_rpow(term, ctx))
    results.extend(_r0026_rpow_zero(term, ctx))
    results.extend(_r0027_zero_rpow_def(term, ctx))
    results.extend(_r0028_rpow_neg(term, ctx))
    results.extend(_r0029_rpow_intCast(term, ctx))
    results.extend(_r0030_rpow_add(term, ctx))
    results.extend(_r0031_rpow_zero(term, ctx))
    results.extend(_r0032_top_rpow_of_neg(term, ctx))
    results.extend(_r0033_zero_rpow_of_pos(term, ctx))
    results.extend(_r0034_rpow_inv_rpow(term, ctx))
    results.extend(_r0035_rpow_rpow_inv_eq_iff(term, ctx))
    results.extend(_r0036_rpow_inv_rpow_eq_iff(term, ctx))
    results.extend(_r0037_pow_rpow_inv_natCast(term, ctx))
    results.extend(_r0038_some_eq_coe(term, ctx))
    results.extend(_r0039_coe_inj(term, ctx))
    results.extend(_r0040_coe_toNNReal(term, ctx))
    results.extend(_r0041_toReal_ofReal(term, ctx))
    results.extend(_r0042_coe_zero(term, ctx))
    results.extend(_r0043_coe_one(term, ctx))
    results.extend(_r0044_coe_toNNReal_eq_toReal(term, ctx))
    results.extend(_r0045_toNNReal_toReal_eq(term, ctx))
    results.extend(_r0046_toNNReal_top(term, ctx))
    results.extend(_r0047_toReal_top(term, ctx))
    results.extend(_r0048_toReal_one(term, ctx))
    results.extend(_r0049_toNNReal_one(term, ctx))
    results.extend(_r0050_coe_toReal(term, ctx))
    results.extend(_r0051_toNNReal_zero(term, ctx))
    results.extend(_r0052_toReal_zero(term, ctx))
    results.extend(_r0053_ofReal_zero(term, ctx))
    results.extend(_r0054_ofReal_one(term, ctx))
    results.extend(_r0055_ofReal_toReal_eq_iff(term, ctx))
    results.extend(_r0056_zero_eq_coe(term, ctx))
    results.extend(_r0057_coe_eq_one(term, ctx))
    results.extend(_r0058_one_eq_coe(term, ctx))
    results.extend(_r0059_coe_mul(term, ctx))
    results.extend(_r0060_coe_nsmul(term, ctx))
    results.extend(_r0061_coe_pow(term, ctx))
    results.extend(_r0062_coe_ofNat(term, ctx))
    results.extend(_r0063_bot_eq_zero(term, ctx))
    results.extend(_r0064_coe_natCast(term, ctx))
    results.extend(_r0065_ofReal_natCast(term, ctx))
    results.extend(_r0066_ofReal_ofNat(term, ctx))
    results.extend(_r0067_ofNNReal_add_natCast(term, ctx))
    results.extend(_r0068_ofNNReal_natCast_add(term, ctx))
    results.extend(_r0069_ofNNReal_sub_natCast(term, ctx))
    results.extend(_r0070_ofNNReal_natCast_sub(term, ctx))
    results.extend(_r0071_toNNReal_natCast(term, ctx))
    results.extend(_r0072_toNNReal_ofNat(term, ctx))
    results.extend(_r0073_toReal_ofNat(term, ctx))
    results.extend(_r0074_toNNReal_natCast_eq_toNNReal(term, ctx))
    results.extend(_r0075_min_eq_zero_iff(term, ctx))
    results.extend(_r0076_max_zero_left(term, ctx))
    results.extend(_r0077_iUnion_Ioo_coe_nat(term, ctx))
    results.extend(_r0078_iUnion_Icc_coe_nat(term, ctx))
    results.extend(_r0079_iUnion_Ico_coe_nat(term, ctx))
    results.extend(_r0080_iInter_Ici_coe_nat(term, ctx))
    results.extend(_r0081_iInter_Ioi_coe_nat(term, ctx))
    results.extend(_r0082_coe_min(term, ctx))
    results.extend(_r0083_coe_max(term, ctx))
    results.extend(_r0084_coe_finset_prod(term, ctx))
    results.extend(_r0085_toNNReal_prod(term, ctx))
    results.extend(_r0086_inv_top(term, ctx))
    results.extend(_r0087_coe_inv_two(term, ctx))
    results.extend(_r0088_inv_eq_top(term, ctx))
    results.extend(_r0089_top_div(term, ctx))
    results.extend(_r0090_top_div_of_ne_top(term, ctx))
    results.extend(_r0091_top_div_of_lt_top(term, ctx))
    results.extend(_r0092_zero_div(term, ctx))
    results.extend(_r0093_div_eq_top(term, ctx))
    results.extend(_r0094_add_thirds(term, ctx))
    results.extend(_r0095_div_eq_zero_iff(term, ctx))
    results.extend(_r0096_toReal_inv(term, ctx))
    results.extend(_r0097_toReal_div(term, ctx))
    results.extend(_r0098_ofReal_min(term, ctx))
    results.extend(_r0099_ofReal_max(term, ctx))
    results.extend(_r0100_ofReal_eq_one(term, ctx))
    results.extend(_r0101_ofReal_eq_ofNat(term, ctx))
    results.extend(_r0102_toNNReal_mul_top(term, ctx))
    results.extend(_r0103_toReal_nsmul(term, ctx))
    results.extend(_r0104_toReal_ofReal_mul(term, ctx))
    results.extend(_r0105_coe_expect(term, ctx))
    results.extend(_r0106_toNNReal_sum_of_nonneg(term, ctx))
    results.extend(_r0107_toNNReal_prod_of_nonneg(term, ctx))
    results.extend(_r0108_sqrt_sq(term, ctx))
    results.extend(_r0109_mul_self_sqrt(term, ctx))
    results.extend(_r0110_sqrt_mul_self(term, ctx))
    results.extend(_r0111_sqrt_eq_one(term, ctx))
    results.extend(_r0112_sqrt_zero(term, ctx))
    results.extend(_r0113_sqrt_one(term, ctx))
    results.extend(_r0114_group_smul_toList(term, ctx))
    results.extend(_r0115_prod_smul(term, ctx))
    results.extend(_r0116_toSphere_eq_zero_iff_finrank(term, ctx))
    results.extend(_r0117_piPremeasure_pi(term, ctx))
    results.extend(_r0118_tprod_cons(term, ctx))
    results.extend(_r0119_condLExp_congr_ae_trim(term, ctx))
    results.extend(_r0120_essSup_const_mul(term, ctx))
    results.extend(_r0121_lpNorm_of_not_memLp(term, ctx))
    results.extend(_r0122_lpNorm_eq_integral_norm_rpow_toReal(term, ctx))
    results.extend(_r0123_lpNorm_measure_zero(term, ctx))
    results.extend(_r0124_lpNorm_eq_zero(term, ctx))
    results.extend(_r0125_lpNorm_neg(term, ctx))
    results.extend(_r0126_lpNorm_sub_comm(term, ctx))
    results.extend(_r0127_lpNorm_abs(term, ctx))
    results.extend(_r0128_lpNorm_fun_abs(term, ctx))
    results.extend(_r0129_lpNorm_const(term, ctx))
    results.extend(_r0130_toLp_zero(term, ctx))
    results.extend(_r0131_toLp_add(term, ctx))
    results.extend(_r0132_enorm_def(term, ctx))
    results.extend(_r0133_norm_toLp(term, ctx))
    results.extend(_r0134_nnnorm_toLp(term, ctx))
    results.extend(_r0135_nnnorm_zero(term, ctx))
    results.extend(_r0136_norm_measure_zero(term, ctx))
    results.extend(_r0137_eq_zero_iff_ae_eq_zero(term, ctx))
    results.extend(_r0138_norm_neg(term, ctx))
    results.extend(_r0139_apply_mk(term, ctx))
    results.extend(_r0140_range_const(term, ctx))
    results.extend(_r0141_piecewise_empty(term, ctx))
    results.extend(_r0142_range_map(term, ctx))
    results.extend(_r0143_map_const(term, ctx))
    results.extend(_r0144_pair_preimage(term, ctx))
    results.extend(_r0145_map_snd_pair(term, ctx))
    results.extend(_r0146_bind_const(term, ctx))
    results.extend(_r0147_coe_mul(term, ctx))
    results.extend(_r0148_coe_inv(term, ctx))
    results.extend(_r0149_coe_div(term, ctx))
    results.extend(_r0150_coe_sup(term, ctx))
    results.extend(_r0151_coe_inf(term, ctx))
    results.extend(_r0152_mul_apply(term, ctx))
    results.extend(_r0153_range_eq_empty_of_isEmpty(term, ctx))
    results.extend(_r0154_smul_apply(term, ctx))
    results.extend(_r0155_pow_apply(term, ctx))
    results.extend(_r0156_zpow_apply(term, ctx))
    results.extend(_r0157_nearestPt_zero(term, ctx))
    results.extend(_r0158_nearestPtInd_succ(term, ctx))
    results.extend(_r0159_dirac_one_mconv(term, ctx))
    results.extend(_r0160_mconv_dirac_one(term, ctx))
    results.extend(_r0161_sdiff_fundamentalFrontier(term, ctx))
    results.extend(_r0162_fundamentalFrontier_smul(term, ctx))
    results.extend(_r0163_laverage_zero_measure(term, ctx))
    results.extend(_r0164_integral_indicator_2(term, ctx))
    results.extend(_r0165_weightedSMul_empty(term, ctx))
    results.extend(_r0166_addContent_sUnion(term, ctx))
    results.extend(_r0167_mk_apply(term, ctx))
    results.extend(_r0168_count_apply_finset(term, ctx))
    results.extend(_r0169_count_eq_dirac(term, ctx))
    results.extend(_r0170_dirac_apply_eq_zero_or_one(term, ctx))
    results.extend(_r0171_ae_dirac_eq(term, ctx))
    results.extend(_r0172_diracProba_toMeasure_apply_of_mem(term, ctx))
    results.extend(_r0173_diracProba_toMeasure_apply(term, ctx))
    results.extend(_r0174_diracProbaInverse_eq(term, ctx))
    results.extend(_r0175_toMeasure_mk(term, ctx))
    results.extend(_r0176_measureReal_eq_coe_coeFn(term, ctx))
    results.extend(_r0177_ennreal_coeFn_eq_coeFn_toMeasure(term, ctx))
    results.extend(_r0178_ennreal_mass(term, ctx))
    results.extend(_r0179_zero_mass(term, ctx))
    results.extend(_r0180_mass_zero_iff(term, ctx))
    results.extend(_r0181_toMeasure_add(term, ctx))
    results.extend(_r0182_toMeasure_smul(term, ctx))
    results.extend(_r0183_restrict_apply_measure(term, ctx))
    results.extend(_r0184_restrict_univ(term, ctx))
    results.extend(_r0185_restrict_union(term, ctx))
    results.extend(_r0186_testAgainstNN_one(term, ctx))
    results.extend(_r0187_zero_testAgainstNN(term, ctx))
    results.extend(_r0188_toWeakDualBCNN_apply(term, ctx))
    results.extend(_r0189_pi_pi(term, ctx))
    results.extend(_r0190_mass_pi(term, ctx))
    results.extend(_r0191_pi_map_pi(term, ctx))
    results.extend(_r0192_pi_pi(term, ctx))
    results.extend(_r0193_prod_apply(term, ctx))
    results.extend(_r0194_mass_prod(term, ctx))
    results.extend(_r0195_prod_zero(term, ctx))
    results.extend(_r0196_map_fst_prod(term, ctx))
    results.extend(_r0197_map_snd_prod(term, ctx))
    results.extend(_r0198_map_prod_map(term, ctx))
    results.extend(_r0199_bind_apply(term, ctx))
    results.extend(_r0200_bind_dirac(term, ctx))
    results.extend(_r0201_levyProkhorovEDist_self(term, ctx))
    results.extend(_r0202_map_zero(term, ctx))
    results.extend(_r0203_map_of_not_aemeasurable(term, ctx))
    results.extend(_r0204_map_apply(term, ctx))
    results.extend(_r0205_map_eq_zero_iff(term, ctx))
    results.extend(_r0206_measure_preimage_of_map_eq_self(term, ctx))
    results.extend(_r0207_ae_eq_of_ae_subset_of_measure_ge(term, ctx))
    results.extend(_r0208_toMeasure_zero(term, ctx))
    results.extend(_r0209_toOuterMeasure_apply(term, ctx))
    results.extend(_r0210_exists_measurable_superset(term, ctx))
    results.extend(_r0211_measure_compl_nullSet(term, ctx))
    results.extend(_r0212_val_eq_to_measure(term, ctx))
    results.extend(_r0213_coeFn_univ(term, ctx))
    results.extend(_r0214_coeFn_empty(term, ctx))
    results.extend(_r0215_toNNReal_measureReal_eq_coeFn(term, ctx))
    results.extend(_r0216_toFiniteMeasure_apply(term, ctx))
    results.extend(_r0217_toFiniteMeasure_apply_eq_apply(term, ctx))
    results.extend(_r0218_ennreal_coeFn_eq_coeFn_toMeasure(term, ctx))
    results.extend(_r0219_range_toFiniteMeasure(term, ctx))
    results.extend(_r0220_toWeakDualBCNN_apply(term, ctx))
    results.extend(_r0221_map_prod_map(term, ctx))
    results.extend(_r0222_fst_sum(term, ctx))
    results.extend(_r0223_snd_sum(term, ctx))
    results.extend(_r0224_snd_map_swap(term, ctx))
    results.extend(_r0225_measureReal_zero_apply(term, ctx))
    results.extend(_r0226_measureReal_empty(term, ctx))
    results.extend(_r0227_measureReal_nnreal_smul_apply(term, ctx))
    results.extend(_r0228_map_measureReal_apply(term, ctx))
    results.extend(_r0229_measureReal_mono_null(term, ctx))
    results.extend(_r0230_restrict_smul(term, ctx))
    results.extend(_r0231_restrict_restrict_of_subset(term, ctx))
    results.extend(_r0232_restrict_univ(term, ctx))
    results.extend(_r0233_restrict_inter_add_diff_0(term, ctx))
    results.extend(_r0234_zero_sub(term, ctx))
    results.extend(_r0235_sub_self(term, ctx))
    results.extend(_r0236_sub_zero(term, ctx))
    results.extend(_r0237_support_add(term, ctx))
    results.extend(_r0238_trim_measurableSet_eq(term, ctx))
    results.extend(_r0239_measure_zero(term, ctx))
    results.extend(_r0240_toFinite_apply_eq_zero_iff(term, ctx))
    results.extend(_r0241_toFinite_eq_zero_iff(term, ctx))
    results.extend(_r0242_toFinite_zero(term, ctx))
    results.extend(_r0243_toFinite_eq_self(term, ctx))
    results.extend(_r0244_ae_le_set(term, ctx))
    results.extend(_r0245_ae_eq_set_compl(term, ctx))
    results.extend(_r0246_measure_union_null(term, ctx))
    results.extend(_r0247_top_caratheodory(term, ctx))
    results.extend(_r0248_add_apply(term, ctx))
    results.extend(_r0249_smul_apply(term, ctx))
    results.extend(_r0250_coe_iSup(term, ctx))
    results.extend(_r0251_smul_iSup(term, ctx))
    results.extend(_r0252_not_measurable(term, ctx))
    results.extend(_r0253_smul_apply(term, ctx))
    results.extend(_r0254_toENNRealVectorMeasure_ennrealToMeasure(term, ctx))
    results.extend(_r0255_zero_negPart(term, ctx))
    results.extend(_r0256_neg_posPart(term, ctx))
    results.extend(_r0257_neg_negPart(term, ctx))
    results.extend(_r0258_smul_posPart(term, ctx))
    results.extend(_r0259_smul_negPart(term, ctx))
    results.extend(_r0260_real_smul_def(term, ctx))
    results.extend(_r0261_real_smul_nonneg(term, ctx))
    results.extend(_r0262_ennrealVariation_apply(term, ctx))
    results.extend(_r0263_serreDerivative_eq(term, ctx))
    results.extend(_r0264_limsup_of_not_isBoundedUnder(term, ctx))
    results.extend(_r0265_liminf_of_not_isCoboundedUnder(term, ctx))
    results.extend(_r0266_toReal_liminf(term, ctx))
    results.extend(_r0267_deterministic_comp_eq_map(term, ctx))
    results.extend(_r0268_swap_comp(term, ctx))
    results.extend(_r0269_map_comp(term, ctx))
    results.extend(_r0270_copy_comp_map(term, ctx))
    results.extend(_r0271_compProd_apply_prod(term, ctx))
    results.extend(_r0272_compProd_zero_right(term, ctx))
    results.extend(_r0273_compProd_eq_zero_iff(term, ctx))
    results.extend(_r0274_stronglyAdapted_predictablePart(term, ctx))
    results.extend(_r0275_lowerCrossingTime_zero(term, ctx))
    results.extend(_r0276_upperCrossingTime_succ(term, ctx))
    results.extend(_r0277_hittingAfter_empty(term, ctx))
    results.extend(_r0278_hittingBtwn_univ(term, ctx))
    results.extend(_r0279_leibniz(term, ctx))
    results.extend(_r0280_map_smul_of_tower(term, ctx))
    results.extend(_r0281_map_algebraMap(term, ctx))
    results.extend(_r0282_map_natCast(term, ctx))
    results.extend(_r0283_leibniz_pow(term, ctx))
    results.extend(_r0284_coe_zero_linearMap(term, ctx))
    results.extend(_r0285_zero_apply(term, ctx))
    results.extend(_r0286_coe_add_linearMap(term, ctx))
    results.extend(_r0287_add_apply(term, ctx))
    results.extend(_r0288_coe_smul_linearMap(term, ctx))
    results.extend(_r0289_smul_apply(term, ctx))
    results.extend(_r0290_commutator_apply(term, ctx))
    results.extend(_r0291_mapCoeffs_monomial(term, ctx))
    results.extend(_r0292_mapCoeffs_C(term, ctx))
    results.extend(_r0293_to_eq(term, ctx))
    results.extend(_r0294_to_isNat(term, ctx))
    results.extend(_r0295_to_isNat(term, ctx))
    results.extend(_r0296_tsum_eq_top_of_eq_top(term, ctx))
    results.extend(_r0297_tsum_const(term, ctx))
    results.extend(_r0298_map_coe_nhdsGT(term, ctx))
    results.extend(_r0299_map_coe_nhdsGE(term, ctx))
    results.extend(_r0300_comap_coe_atTop(term, ctx))
    results.extend(_r0301_coeNNRealReal_zero(term, ctx))
    results.extend(_r0302_summable_one_div_rpow(term, ctx))
    results.extend(_r0303_coe_ne_coe(term, ctx))
    results.extend(_r0304_coe_le_coe(term, ctx))
    results.extend(_r0305_coe_lt_coe(term, ctx))
    results.extend(_r0306_coe_pos(term, ctx))
    results.extend(_r0307_coe_ne_zero(term, ctx))
    results.extend(_r0308_coe_ne_one(term, ctx))
    results.extend(_r0309_coe_le_one_iff(term, ctx))
    results.extend(_r0310_coe_lt_one_iff(term, ctx))
    results.extend(_r0311_one_lt_coe_iff(term, ctx))
    results.extend(_r0312_natCast_le_ofNNReal(term, ctx))
    results.extend(_r0313_ofNNReal_le_natCast(term, ctx))
    results.extend(_r0314_inv_ne_top(term, ctx))
    results.extend(_r0315_inv_ne_zero(term, ctx))
    results.extend(_r0316_inv_lt_iff_inv_lt(term, ctx))
    results.extend(_r0317_inv_le_iff_inv_le(term, ctx))
    results.extend(_r0318_one_le_inv(term, ctx))
    results.extend(_r0319_one_lt_inv(term, ctx))
    results.extend(_r0320_div_pos_iff(term, ctx))
    results.extend(_r0321_div_ne_zero(term, ctx))
    results.extend(_r0322_ofReal_ne_zero_iff(term, ctx))
    results.extend(_r0323_ofReal_lt_one(term, ctx))
    results.extend(_r0324_ofReal_lt_ofNat(term, ctx))
    results.extend(_r0325_one_le_ofReal(term, ctx))
    results.extend(_r0326_ofNat_le_ofReal(term, ctx))
    results.extend(_r0327_ofReal_le_one(term, ctx))
    results.extend(_r0328_ofReal_le_ofNat(term, ctx))
    results.extend(_r0329_one_lt_ofReal(term, ctx))
    results.extend(_r0330_ofNat_lt_ofReal(term, ctx))
    results.extend(_r0331_ofReal_lt_coe_iff(term, ctx))
    results.extend(_r0332_bddAbove_range_natCast_iff(term, ctx))
    results.extend(_r0333_sqrt_le_sqrt(term, ctx))
    results.extend(_r0334_sqrt_lt_sqrt(term, ctx))
    results.extend(_r0335_sqrt_le_one(term, ctx))
    results.extend(_r0336_one_le_sqrt(term, ctx))
    results.extend(_r0337_integrableOn_univ(term, ctx))
    results.extend(_r0338_integrableOn_fun_neg_iff(term, ctx))
    results.extend(_r0339_union_right_iff(term, ctx))
    results.extend(_r0340_restrict_nonzero_iff(term, ctx))
    results.extend(_r0341_add_left_iff(term, ctx))
    results.extend(_r0342_add_right_iff(term, ctx))
    results.extend(_r0343_le_boundedBy(term, ctx))
    results.extend(_r0344_hasSum_iff_tendsto_nat(term, ctx))
    results.extend(_r0345_tendsto_coe_atTop(term, ctx))
    results.extend(_r0346_congr_d(term, ctx))
    results.extend(_r0347_d_one(term, ctx))
    results.extend(_r0348_d_app(term, ctx))
    results.extend(_r0349_app_apply(term, ctx))
    results.extend(_r0350_mk_app(term, ctx))
    results.extend(_r0351_conjAct(term, ctx))
    results.extend(_r0352_conj_smul_eq_self(term, ctx))
    results.extend(_r0353_to_singleFunctor_obj_eq_zero_of_injectiv(term, ctx))
    results.extend(_r0354_from_singleFunctor_obj_eq_zero_of_projec(term, ctx))
    results.extend(_r0355_right_fac(term, ctx))
    results.extend(_r0356_left_fac(term, ctx))
    results.extend(_r0357_right_fac_of_isStrictlyLE(term, ctx))
    results.extend(_r0358_left_fac_of_isStrictlyGE(term, ctx))
    results.extend(_r0359_right_fac_of_isStrictlyLE_of_isStrictlyG(term, ctx))
    results.extend(_r0360_left_fac_of_isStrictlyLE_of_isStrictlyGE(term, ctx))
    results.extend(_r0361_homologyFunctorFactors_hom_naturality(term, ctx))
    results.extend(_r0362_homologyFunctorFactorsh_hom_app_quotient(term, ctx))
    results.extend(_r0363_homologyFunctorFactorsh_inv_app_quotient(term, ctx))
    results.extend(_r0364_shift_homologyFunctor(term, ctx))
    results.extend(_r0365_shiftMap_homologyFunctor_map_Qh(term, ctx))
    results.extend(_r0366_shiftMap_homologyFunctor_map_Q(term, ctx))
    results.extend(_r0367_comp_d(term, ctx))
    results.extend(_r0368_d_comp(term, ctx))
    results.extend(_r0369_epi_homologyMap_mor_1_iff(term, ctx))
    results.extend(_r0370_mono_homologyMap_mor_1_iff(term, ctx))
    results.extend(_r0371_epi_homologyMap_mor_2_iff(term, ctx))
    results.extend(_r0372_mono_homologyMap_mor_2_iff(term, ctx))
    results.extend(_r0373_descShortComplex_triangleOfSESd(term, ctx))
    results.extend(_r0374_triangleOfSESd_naturality(term, ctx))
    results.extend(_r0375_ofDerivation_apply(term, ctx))
    results.extend(_r0376_ofLieDerivation_apply(term, ctx))
    results.extend(_r0377_compAEval_eq(term, ctx))
    results.extend(_r0378_comp_aeval_eq(term, ctx))
    results.extend(_r0379_box_integral_eq_integral(term, ctx))
    results.extend(_r0380_isBigO_sub(term, ctx))
    results.extend(_r0381_isBigO_sub(term, ctx))
    results.extend(_r0382_isTheta_sub(term, ctx))
    results.extend(_r0383_isBigO_sub_rev(term, ctx))
    results.extend(_r0384_deriv(term, ctx))
    results.extend(_r0385_segment_eq_Icc(term, ctx))
    results.extend(_r0386_segment_eq_uIcc(term, ctx))
    results.extend(_r0387_convolution_integrand_fst(term, ctx))
    results.extend(_r0388_toTemperedDistribution_apply(term, ctx))
    results.extend(_r0389_toTemperedDistribution_apply(term, ctx))
    results.extend(_r0390_toTemperedDistribution_toLp_eq(term, ctx))
    results.extend(_r0391_toTemperedDistributionCLM_apply(term, ctx))
    results.extend(_r0392_ker_toTemperedDistributionCLM_eq_bot(term, ctx))
    results.extend(_r0393_toTemperedDistribution_smul_eq(term, ctx))
    results.extend(_r0394_fourierInv_fourier_eq(term, ctx))
    results.extend(_r0395_fourier_fourierInv_eq(term, ctx))
    results.extend(_r0396_norm_fourier_eq(term, ctx))
    results.extend(_r0397_fourier_toTemperedDistribution_eq(term, ctx))
    results.extend(_r0398_fourierInv_toTemperedDistribution_eq(term, ctx))
    results.extend(_r0399_T_univ(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_analysis rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("Normal_of_conjugate_fixed", "H_Normal", "Not an equality or iff proposition"),
    ("DerivedCategory_mappingCone_triangle_distinguished", "DerivedCategory_Q_mapTriangle_obj_mappingCone_triangle_phi_in_distTriang", "Not an equality or iff proposition"),
    ("DerivedCategory_mappingCocone_triangle_distinguished", "DerivedCategory_Q_mapTriangle_obj_mappingCocone_triangle_phi_in_distTriang", "Not an equality or iff proposition"),
    ("DerivedCategory_subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE", "Subsingleton_Q_obj_X_Q_obj_Y", "Not an equality or iff proposition"),
    ("DerivedCategory_HomologySequence_exact_2", "ShortComplex_mk_homologyFunctor_C_n_0_map_T_mor_1_homologyFunctor_C_n_0_map", "Not an equality or iff proposition"),
    ("DerivedCategory_HomologySequence_exact_3", "ShortComplex_mk_comp_d_T_hT_n_0_n_1_h_Exact", "Not an equality or iff proposition"),
    ("DerivedCategory_HomologySequence_exact_1", "ShortComplex_mk_d_comp_T_hT_n_0_n_1_h_Exact", "Not an equality or iff proposition"),
    ("DerivedCategory_triangleOfSES_distinguished", "triangleOfSES_hS_in_distTriang_DerivedCategory_C", "Not an equality or iff proposition"),
    ("DerivedCategory_isZero_of_isGE", "IsZero_homologyFunctor_i_obj_X", "Not an equality or iff proposition"),
    ("DerivedCategory_isZero_of_isLE", "IsZero_homologyFunctor_i_obj_X", "Not an equality or iff proposition"),
    ("DerivedCategory_exists_iso_Q_obj_of_isLE", "exists_K_colon_CochainComplex_C_colon_K_IsStrictlyLE_n_Nonempty_X_Q_obj_K", "Not an equality or iff proposition"),
    ("DerivedCategory_exists_iso_Q_obj_of_isGE", "exists_K_colon_CochainComplex_C_colon_K_IsStrictlyGE_n_Nonempty_X_Q_obj_K", "Not an equality or iff proposition"),
    ("DerivedCategory_exists_iso_Q_obj_of_isGE_of_isLE", "exists_K_colon_CochainComplex_C_colon_K_IsStrictlyGE_a_colon_K_IsStrictlyLE_b", "Not an equality or iff proposition"),
    ("DerivedCategory_exists_iso_singleFunctor_obj_of_isGE_of_isLE", "exists_Y_colon_C_Nonempty_X_singleFunctor_C_n_obj_Y", "Not an equality or iff proposition"),
    ("Mathlib_Meta_NormNum_IsNat_natFloor", "IsNat_r_m_to_IsNat_r_m", "Not an equality or iff proposition"),
    ("Mathlib_Meta_NormNum_IsInt_natFloor", "IsInt_r_negOfNat_m_to_IsNat_r_0", "Not an equality or iff proposition"),
    ("Mathlib_Meta_NormNum_IsNNRat_natFloor", "IsNat_r_res", "Not an equality or iff proposition"),
    ("Mathlib_Meta_NormNum_IsRat_natFloor", "IsNat_r_0", "Not an equality or iff proposition"),
    ("NormedField_tendsto_zero_smul_of_tendsto_zero_of_bounded", "Tendsto_e_f_l_0", "Not an equality or iff proposition"),
    ("MeasureTheory_SimpleFunc_hasBoxIntegral", "HasIntegral_u_v_v_I_l_f_mu_toBoxAdditive_toSMul_f_integral_mu_restrict_I", "Not an equality or iff proposition"),
    ("MeasureTheory_IntegrableOn_hasBoxIntegral", "HasIntegral_u_v_v_I_l_f_mu_toBoxAdditive_toSMul_x_in_I_f_x_mu", "Not an equality or iff proposition"),
    ("MeasureTheory_ContinuousOn_hasBoxIntegral", "HasIntegral_u_v_v_I_l_f_mu_toBoxAdditive_toSMul_x_in_I_f_x_mu", "Not an equality or iff proposition"),
    ("MeasureTheory_AEContinuous_hasBoxIntegral", "HasIntegral_u_v_v_I_l_f_mu_toBoxAdditive_toSMul_x_in_I_f_x_mu", "Not an equality or iff proposition"),
    ("NNReal_spectrum_nonempty", "spectrum_ge_0_a_Nonempty", "Not an equality or iff proposition"),
    ("MeasureTheory_LocallyIntegrable_exists_contDiff_dist_le_of_forall_mem_ball_dist_le", "exists_g_colon_E_to_F_ContDiff_inf_g_and_forall_a_forall_d_forall_x_in_ball_a_e_dist_f_x_f_a_le_d_to", "Not an equality or iff proposition"),
    ("HasCompactSupport_hasFDerivAt_convolution_right", "HasFDerivAt_f_L_mu_g_f_L_precompR_G_mu_fderiv_g_x_0_x_0", "Not an equality or iff proposition"),
    ("HasCompactSupport_hasFDerivAt_convolution_left", "HasFDerivAt_f_L_mu_g_fderiv_f_L_precompL_G_mu_g_x_0_x_0", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_add", "HasDerivAtFilter_f_plus_g_f_prime_plus_g_prime_L", "Not an equality or iff proposition"),
    ("HasDerivAt_add", "HasDerivAt_f_plus_g_f_prime_plus_g_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_fun_sum", "HasDerivAtFilter_fun_y_i_in_u_A_i_y_i_in_u_A_prime_i_L", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_sum", "HasDerivAtFilter_i_in_u_A_i_i_in_u_A_prime_i_L", "Not an equality or iff proposition"),
    ("HasDerivAt_fun_sum", "HasDerivAt_fun_y_i_in_u_A_i_y_i_in_u_A_prime_i_x", "Not an equality or iff proposition"),
    ("HasDerivAt_sum", "HasDerivAt_i_in_u_A_i_i_in_u_A_prime_i_x", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_neg", "HasDerivAtFilter_minus_f_minus_f_prime_L", "Not an equality or iff proposition"),
    ("HasDerivAt_neg", "HasDerivAt_minus_f_minus_f_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_sub", "HasDerivAtFilter_f_minus_g_f_prime_minus_g_prime_L", "Not an equality or iff proposition"),
    ("HasDerivAt_sub", "HasDerivAt_f_minus_g_f_prime_minus_g_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_const_sub", "HasDerivAtFilter_fun_x_c_minus_f_x_minus_f_prime_L", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_isEquivalent_sub", "fun_p_f_p_1_minus_f_p_2_tilde_L_fun_p_p_1_minus_p_2_f_prime", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_mono", "HasDerivAtFilter_f_f_prime_L_1", "Not an equality or iff proposition"),
    ("HasDerivAt_hasDerivAtFilter", "HasDerivAtFilter_f_f_prime_L", "Not an equality or iff proposition"),
    ("HasDerivAt_hasDerivWithinAt", "HasDerivWithinAt_f_f_prime_s_x", "Not an equality or iff proposition"),
    ("HasDerivAt_differentiableAt", "DifferentiableAt_f_x", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_congr_of_eventuallyEq", "HasDerivAtFilter_f_1_f_prime_L", "Not an equality or iff proposition"),
    ("HasDerivAt_congr_deriv", "HasDerivAt_f_g_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAt_congr_of_eventuallyEq", "HasDerivAt_f_1_f_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_tendsto_nhds", "Tendsto_f_L_f_x", "Not an equality or iff proposition"),
    ("HasDerivAt_continuousAt", "ContinuousAt_f_x", "Not an equality or iff proposition"),
    ("HasDerivAt_continuousOn", "ContinuousOn_f_s", "Not an equality or iff proposition"),
    ("HasDerivAt_le_of_lip", "_unknown", "Empty proposition"),
    ("HasDerivAt_le_of_lipschitzOn", "f_prime_le_C", "Not an equality or iff proposition"),
    ("HasDerivAt_le_of_lipschitz", "f_prime_le_C", "Not an equality or iff proposition"),
    ("HasDerivAt_comp_semilinear", "HasDerivAt_L_comp_f_comp_sig_prime_L_f_prime_sig_x", "Not an equality or iff proposition"),
    ("HasDerivAt_comp_ringHom", "HasDerivAt_sig_comp_f_comp_sig_prime_sig_f_prime_sig_x", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_scomp", "HasDerivAtFilter_g_1_comp_h_h_prime_g_1_prime_L", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_scomp_of_eq", "HasDerivAtFilter_g_1_comp_h_h_prime_g_1_prime_L_times_pure_x", "Not an equality or iff proposition"),
    ("HasDerivAt_scomp", "HasDerivAt_g_1_comp_h_h_prime_g_1_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAt_scomp_of_eq", "HasDerivAt_g_1_comp_h_h_prime_g_1_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAt_scomp_hasDerivWithinAt", "HasDerivWithinAt_g_1_comp_h_h_prime_g_1_prime_s_x", "Not an equality or iff proposition"),
    ("HasDerivAt_scomp_hasDerivWithinAt_of_eq", "HasDerivWithinAt_g_1_comp_h_h_prime_g_1_prime_s_x", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_comp_hasFDerivAtFilter", "HasFDerivAtFilter_h_2_comp_f_h_2_prime_f_prime_L_prime_prime", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_comp_hasFDerivAtFilter_of_eq", "HasFDerivAtFilter_h_2_comp_f_h_2_prime_f_prime_L_prime_prime_times_pure_x", "Not an equality or iff proposition"),
    ("HasDerivAt_comp_hasFDerivAt", "HasFDerivAt_h_2_comp_f_h_2_prime_f_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAt_comp_hasFDerivAt_of_eq", "HasFDerivAt_h_2_comp_f_h_2_prime_f_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAt_comp_hasFDerivWithinAt", "HasFDerivWithinAt_h_2_comp_f_h_2_prime_f_prime_s_x", "Not an equality or iff proposition"),
    ("HasDerivAt_comp_hasFDerivWithinAt_of_eq", "HasFDerivWithinAt_h_2_comp_f_h_2_prime_f_prime_s_x", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_comp", "HasDerivAtFilter_h_2_comp_h_h_2_prime_star_h_prime_L", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_comp_of_eq", "HasDerivAtFilter_h_2_comp_h_h_2_prime_star_h_prime_L_times_pure_x", "Not an equality or iff proposition"),
    ("HasDerivAt_comp", "HasDerivAt_h_2_comp_h_h_2_prime_star_h_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAt_comp_of_eq", "HasDerivAt_h_2_comp_h_h_2_prime_star_h_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAt_comp_hasDerivWithinAt", "HasDerivWithinAt_h_2_comp_h_h_2_prime_star_h_prime_s_x", "Not an equality or iff proposition"),
    ("HasDerivAt_comp_hasDerivWithinAt_of_eq", "HasDerivWithinAt_h_2_comp_h_h_2_prime_star_h_prime_s_x", "Not an equality or iff proposition"),
    ("HasDerivAt_inv", "HasDerivAt_cinv_minus_c_prime_slash_c_x_pow_2_x", "Not an equality or iff proposition"),
    ("HasDerivAt_fun_div", "HasDerivAt_fun_y_eq_gt_c_y_slash_d_y_c_prime_star_d_x_minus_c_x_star_d_prime_slash_d_x_pow_2_x", "Not an equality or iff proposition"),
    ("HasDerivAt_div", "HasDerivAt_c_slash_d_c_prime_star_d_x_minus_c_x_star_d_prime_slash_d_x_pow_2_x", "Not an equality or iff proposition"),
    ("HasDerivAt_hasFDerivAt_equiv", "HasFDerivAt_f_ContinuousLinearEquiv_unitsEquivAut_Units_mk0_f_prime_hf_prime_colon_to_L", "Not an equality or iff proposition"),
    ("HasDerivAt_of_local_left_inverse", "HasDerivAt_g_f_primeinv_a", "Not an equality or iff proposition"),
    ("HasDerivAt_tendsto_nhdsNE", "Tendsto_f_ne_x_ne_f_x", "Not an equality or iff proposition"),
    ("HasDerivAt_eventually_ne", "forall_z_in_ne_x_f_z_ne_c", "Not an equality or iff proposition"),
    ("HasDerivAt_eventually_notMem", "forall_z_in_ne_x_f_z_notin_t", "Not an equality or iff proposition"),
    ("HasDerivAt_smul", "HasDerivAt_c_f_c_x_f_prime_plus_c_prime_f_x_x", "Not an equality or iff proposition"),
    ("HasDerivAt_smul_const", "HasDerivAt_fun_y_eq_gt_c_y_f_c_prime_f_x", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_const_smul", "HasDerivAtFilter_c_f_c_f_prime_L", "Not an equality or iff proposition"),
    ("HasDerivAt_const_smul", "HasDerivAt_c_f_c_f_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAt_mul", "HasDerivAt_c_star_d_c_prime_star_d_x_plus_c_x_star_d_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAt_mul_const", "HasDerivAt_fun_y_eq_gt_c_y_star_d_c_prime_star_d_x", "Not an equality or iff proposition"),
    ("HasDerivAt_const_mul", "HasDerivAt_fun_y_eq_gt_c_star_d_y_c_star_d_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAt_fun_finset_prod", "HasDerivAt_i_in_u_f_i_i_in_u_j_in_u_erase_i_f_j_x_f_prime_i_x", "Not an equality or iff proposition"),
    ("HasDerivAt_finset_prod", "HasDerivAt_i_in_u_f_i_i_in_u_j_in_u_erase_i_f_j_x_f_prime_i_x", "Not an equality or iff proposition"),
    ("HasDerivAt_div_const", "HasDerivAt_fun_x_eq_gt_c_x_slash_d_c_prime_slash_d_x", "Not an equality or iff proposition"),
    ("HasDerivAt_clm_comp", "HasDerivAt_fun_y_eq_gt_c_y_comp_d_y_c_prime_comp_d_x_plus_c_x_comp_d_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAt_clm_apply", "HasDerivAt_fun_y_eq_gt_c_y_u_y_c_prime_u_x_plus_c_x_u_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAt_fun_pow", "_unknown", "Empty proposition"),
    ("HasDerivAt_pow", "_unknown", "Empty proposition"),
    ("HasDerivAt_fun_pow", "HasDerivAt_fun_x_f_x_pow_n_n_star_f_x_pow_n_minus_1_star_f_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAt_pow", "HasDerivAt_f_pow_n_n_star_f_x_pow_n_minus_1_star_f_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_prodMk", "HasDerivAtFilter_fun_x_eq_gt_f_1_x_f_2_x_f_1_prime_f_2_prime_L", "Not an equality or iff proposition"),
    ("HasDerivAt_prodMk", "HasDerivAt_fun_x_eq_gt_f_1_x_f_2_x_f_1_prime_f_2_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_finCons", "HasDerivAtFilter_fun_x_eq_gt_Fin_cons_phi_x_phis_x_Fin_cons_phi_prime_phis_prime_l", "Not an equality or iff proposition"),
    ("HasDerivAt_finCons", "HasDerivAt_fun_x_eq_gt_Fin_cons_phi_x_phis_x_Fin_cons_phi_prime_phis_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAt_comp_const_add", "HasDerivAt_fun_x_f_a_plus_x_f_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAt_comp_add_const", "HasDerivAt_fun_x_f_x_plus_a_f_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAt_comp_const_sub", "HasDerivAt_fun_x_f_a_minus_x_minus_f_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAt_comp_sub_const", "HasDerivAt_fun_x_f_x_minus_a_f_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAt_tendsto_slope_zero_right", "Tendsto_fun_t_tinv_f_x_plus_t_minus_f_x_gt_0_f_prime", "Not an equality or iff proposition"),
    ("HasDerivAt_tendsto_slope_zero_left", "Tendsto_fun_t_tinv_f_x_plus_t_minus_f_x_lt_0_f_prime", "Not an equality or iff proposition"),
    ("HasDerivAt_continuousAt_div", "ContinuousAt_Function_update_fun_x_f_x_minus_f_c_slash_x_minus_c_c_a_c", "Not an equality or iff proposition"),
    ("HasDerivAt_nonneg_of_monotone", "_0_le_g_prime", "Not an equality or iff proposition"),
    ("HasDerivAt_nonpos_of_antitone", "g_prime_le_0", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_star", "HasDerivAtFilter_fun_x_eq_gt_star_f_x_star_f_prime_L", "Not an equality or iff proposition"),
    ("HasDerivAt_star", "HasDerivAt_fun_x_eq_gt_star_f_x_star_f_prime_x", "Not an equality or iff proposition"),
    ("HasDerivAt_star_conj", "HasDerivAt_star_comp_f_comp_conj_star_f_prime_conj_x", "Not an equality or iff proposition"),
    ("HasDerivAt_conj_conj", "HasDerivAt_conj_comp_f_comp_conj_conj_f_prime_conj_x", "Not an equality or iff proposition"),
    ("HasDerivAt_of_notMem_tsupport", "HasDerivAt_f_0_x", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_hasGradientAtFilter", "HasGradientAtFilter_g_conj_g_prime_u_L_prime", "Not an equality or iff proposition"),
    ("HasDerivAt_hasGradientAt", "HasGradientAt_g_conj_g_prime_u", "Not an equality or iff proposition"),
    ("HasDerivAtFilter_hasGradientAtFilter", "_unknown", "Empty proposition"),
    ("HasDerivAt_hasGradientAt", "_unknown", "Empty proposition"),
    ("HasDerivAt_lhopital_zero_right_on_Ioo", "Tendsto_fun_x_eq_gt_f_x_slash_g_x_gt_a_l", "Not an equality or iff proposition"),
    ("HasDerivAt_lhopital_zero_right_on_Ico", "Tendsto_fun_x_eq_gt_f_x_slash_g_x_gt_a_l", "Not an equality or iff proposition"),
    ("HasDerivAt_lhopital_zero_left_on_Ioo", "Tendsto_fun_x_eq_gt_f_x_slash_g_x_lt_b_l", "Not an equality or iff proposition"),
    ("HasDerivAt_lhopital_zero_left_on_Ioc", "Tendsto_fun_x_eq_gt_f_x_slash_g_x_lt_b_l", "Not an equality or iff proposition"),
    ("HasDerivAt_lhopital_zero_atTop_on_Ioi", "Tendsto_fun_x_eq_gt_f_x_slash_g_x_atTop_l", "Not an equality or iff proposition"),
    ("HasDerivAt_lhopital_zero_atBot_on_Iio", "Tendsto_fun_x_eq_gt_f_x_slash_g_x_atBot_l", "Not an equality or iff proposition"),
    ("HasDerivAt_lhopital_zero_nhdsGT", "Tendsto_fun_x_eq_gt_f_x_slash_g_x_gt_a_l", "Not an equality or iff proposition"),
    ("HasDerivAt_lhopital_zero_nhdsLT", "Tendsto_fun_x_eq_gt_f_x_slash_g_x_lt_a_l", "Not an equality or iff proposition"),
    ("HasDerivAt_lhopital_zero_nhdsNE", "Tendsto_fun_x_eq_gt_f_x_slash_g_x_ne_a_l", "Not an equality or iff proposition"),
    ("HasDerivWithinAt_lhopital_zero_nhdsWithin_convex", "Tendsto_fun_x_f_x_slash_g_x_s_bsl_a_a_l", "Not an equality or iff proposition"),
    ("HasDerivAt_lhopital_zero_nhds", "Tendsto_fun_x_eq_gt_f_x_slash_g_x_ne_a_l", "Not an equality or iff proposition"),
    ("HasDerivAt_lhopital_zero_atTop", "Tendsto_fun_x_eq_gt_f_x_slash_g_x_atTop_l", "Not an equality or iff proposition"),
    ("HasDerivAt_lhopital_zero_atBot", "Tendsto_fun_x_eq_gt_f_x_slash_g_x_atBot_l", "Not an equality or iff proposition"),
    ("HasDerivAt_real_of_complex", "HasDerivAt_fun_x_colon_eq_gt_e_x_re_e_prime_re_z", "Not an equality or iff proposition"),
    ("HasDerivAt_complexToReal_fderiv", "_unknown", "Empty proposition"),
    ("HasDerivAt_complexToReal_fderiv", "HasFDerivAt_f_f_prime_1_colon_to_L_x", "Not an equality or iff proposition"),
    ("HasDerivAt_comp_ofReal", "HasDerivAt_fun_y_colon_eq_gt_e_y_e_prime_z", "Not an equality or iff proposition"),
    ("HasDerivAt_ofReal_comp", "HasDerivAt_fun_y_colon_eq_gt_f_y_colon_to_u_z", "Not an equality or iff proposition"),
    ("NNReal_Icc_subset_segment", "Icc_x_y_sub_segment_ge_0_x_y", "Not an equality or iff proposition"),
    ("NNReal_strictConcaveOn_rpow", "StrictConcaveOn_ge_0_univ_fun_x_colon_ge_0_x_pow_p", "Not an equality or iff proposition"),
    ("NNReal_concaveOn_rpow", "ConcaveOn_ge_0_univ_fun_x_colon_ge_0_x_pow_p", "Not an equality or iff proposition"),
    ("NNReal_strictConcaveOn_sqrt", "StrictConcaveOn_ge_0_univ_NNReal_sqrt", "Not an equality or iff proposition"),
    ("MeasureTheory_convolution_integrand_bound_right_of_le_of_subset", "L_f_t_g_x_minus_t_le_u_indicator_fun_t_eq_gt_L_star_f_t_star_C_t", "Not an equality or iff proposition"),
    ("HasCompactSupport_convolution_integrand_bound_right_of_subset", "L_f_t_g_x_minus_t_le_u_indicator_fun_t_eq_gt_L_star_f_t_star_i_g_i_t", "Not an equality or iff proposition"),
    ("HasCompactSupport_convolution_integrand_bound_right", "L_f_t_g_x_minus_t_le_minus_tsupport_g_plus_s_indicator_fun_t_eq_gt_L_star_f_t_star_i", "Not an equality or iff proposition"),
    ("HasCompactSupport_convolution_integrand_bound_left", "L_f_x_minus_t_g_t_le_minus_tsupport_f_plus_s_indicator_fun_t_eq_gt_L_star_i", "Not an equality or iff proposition"),
    ("MeasureTheory_Measure_integrable_pow_neg_integrablePower", "Integrable_fun_x_1_plus_x_pow_minus_mu_integrablePower_colon_mu", "Not an equality or iff proposition"),
    ("pow_mul_le_of_le_of_pow_mul_le", "x_pow_k_star_f_le_2_pow_l_star_C_1_plus_C_2_star_1_plus_x_pow_minus_l_colon", "Not an equality or iff proposition"),
    ("integrable_of_le_of_pow_mul_le", "Integrable_fun_x_x_pow_k_star_f_x_mu", "Not an equality or iff proposition"),
    ("integral_pow_mul_le_of_le_of_pow_mul_le", "x_x_pow_k_star_f_x_mu_le_2_pow_mu_integrablePower_star_x_1_plus_x_pow_minus_mu", "Not an equality or iff proposition"),
    ("MeasureTheory_Measure_HasTemperateGrowth_exists_eLpNorm_lt_top", "exists_k_colon_eLpNorm_fun_x_1_plus_x_pow_minus_k_colon_p_mu_lt_top", "Not an equality or iff proposition"),
    ("MeasureTheory_Integrable_fourier_smul", "Integrable_fun_t_fourier_n_t_f_t_haarAddCircle", "Not an equality or iff proposition"),
    ("MeasureTheory_AEStronglyMeasurable_fourierSMulRight", "AEStronglyMeasurable_fun_v_fourierSMulRight_L_f_v_mu", "Not an equality or iff proposition"),
    ("MeasureTheory_AEStronglyMeasurable_fourierPowSMulRight", "AEStronglyMeasurable_fun_v_fourierPowSMulRight_L_f_v_n_mu", "Not an equality or iff proposition"),
    ("MeasureTheory_GridLines_T_insert_le_T_lmarginal_singleton", "T_mu_p_f_insert_i_s_le_T_mu_p_inv_i_f_mu_s", "Not an equality or iff proposition"),
    ("MeasureTheory_GridLines_T_lmarginal_antitone", "Antitone_fun_s_T_mu_p_inv_s_f_mu_s", "Not an equality or iff proposition"),
    ("MeasureTheory_lintegral_mul_prod_lintegral_pow_le", "inv_x_f_x_pow_1_minus_hash_i_minus_1_colon_star_p_star_i_inv_x_f_update_x_i_x_mu_i_pow_p", "Not an equality or iff proposition"),
    ("MeasureTheory_lintegral_prod_lintegral_pow_le", "inv_x_i_inv_x_f_update_x_i_x_mu_i_pow_1_colon_slash_hash_i_minus_1_colon_pi_mu", "Not an equality or iff proposition"),
    ("HasDerivAt_inner", "HasDerivAt_f_f_prime_x_to_HasDerivAt_g_g_prime_x_to_HasDerivAt_fun_t_eq_gt_f_t_g_t", "Not an equality or iff proposition"),
    ("HasDerivAt_norm_sq", "HasDerivAt_f_pow_2_2_star_f_x_f_prime_x", "Not an equality or iff proposition"),
    ("MeasureTheory_measurable_mlconvolution", "Measurable_f_mu_g", "Not an equality or iff proposition"),
    ("NormedSpace_isVonNBounded_of_isBounded", "Bornology_IsVonNBounded_s", "Not an equality or iff proposition"),
    ("NormedSpace_isVonNBounded_ball", "Bornology_IsVonNBounded_Metric_ball_0_colon_E_r", "Not an equality or iff proposition"),
    ("NormedSpace_isVonNBounded_closedBall", "Bornology_IsVonNBounded_Metric_closedBall_0_colon_E_r", "Not an equality or iff proposition"),
    ("NormedSpace_toLocallyConvexSpace", "_unknown", "Empty proposition"),
    ("NNReal_geom_mean_le_arith_mean_weighted", "i_in_s_z_i_pow_w_i_colon_le_i_in_s_w_i_star_z_i", "Not an equality or iff proposition"),
    ("NNReal_young_inequality", "a_star_b_le_a_pow_p_colon_slash_p_plus_b_pow_q_colon_slash_q", "Not an equality or iff proposition"),
    ("NNReal_young_inequality_real", "a_star_b_le_a_pow_p_slash_Real_toNNReal_p_plus_b_pow_q_slash_Real_toNNReal_q", "Not an equality or iff proposition"),
    ("ENNReal_young_inequality", "a_star_b_le_a_pow_p_slash_ENNReal_ofReal_p_plus_b_pow_q_slash_ENNReal_ofReal_q", "Not an equality or iff proposition"),
    ("NNReal_inner_le_Lp_mul_Lp_of_norm_le_one", "i_in_s_f_i_star_g_i_le_1", "Not an equality or iff proposition"),
    ("NNReal_inner_le_Lp_mul_Lp_of_norm_eq_zero", "i_in_s_f_i_star_g_i_le_i_in_s_f_i_pow_p_pow_1_slash_p_star_i_in_s_g_i_pow_q_pow_1_slash_q", "Not an equality or iff proposition"),
    ("NNReal_inner_le_Lp_mul_Lq", "i_in_s_f_i_star_g_i_le_i_in_s_f_i_pow_p_pow_1_slash_p_star_i_in_s_g_i_pow_q_pow_1_slash_q", "Not an equality or iff proposition"),
    ("NNReal_Lr_rpow_le_Lp_mul_Lq", "i_in_s_f_i_star_g_i_pow_r_le_i_in_s_f_i_pow_p_pow_r_slash_p_star_i_in_s_g_i_pow_q_pow", "Not an equality or iff proposition"),
    ("NNReal_Lr_le_Lp_mul_Lq", "i_in_s_f_i_star_g_i_pow_r_pow_1_slash_r_le_i_in_s_f_i_pow_p_pow_1_slash_p_star_i", "Not an equality or iff proposition"),
    ("NNReal_inner_le_weight_mul_Lp", "i_in_s_w_i_star_f_i_le_i_in_s_w_i_pow_1_minus_pinv_star_i_in_s_w_i_star_f_i_pow_p_pow_pinv", "Not an equality or iff proposition"),
    ("NNReal_summable_and_Lr_rpow_le_Lp_mul_Lq_tsum", "Summable_fun_i_eq_gt_f_i_star_g_i_pow_r_and_prime_i_f_i_star_g_i_pow_r_le_prime_i_f_i_pow", "Not an equality or iff proposition"),
    ("NNReal_summable_and_inner_le_Lp_mul_Lq_tsum", "Summable_fun_i_eq_gt_f_i_star_g_i_and_prime_i_f_i_star_g_i_le_prime_i_f_i_pow_p_pow_1_slash_p", "Not an equality or iff proposition"),
    ("NNReal_Lr_rpow_le_Lp_mul_Lq_tsum", "prime_i_f_i_star_g_i_pow_r_le_prime_i_f_i_pow_p_pow_r_slash_p_star_prime_i_g_i_pow_q_pow_r_slash_q", "Not an equality or iff proposition"),
    ("NNReal_Lr_le_Lp_mul_Lq_tsum", "prime_i_f_i_star_g_i_pow_r_pow_1_slash_r_le_prime_i_f_i_pow_p_pow_1_slash_p_star_prime_i_g_i_pow_q", "Not an equality or iff proposition"),
    ("NNReal_inner_le_Lp_mul_Lq_tsum", "prime_i_f_i_star_g_i_le_prime_i_f_i_pow_p_pow_1_slash_p_star_prime_i_g_i_pow_q_pow_1_slash_q", "Not an equality or iff proposition"),
    ("NNReal_inner_le_Lp_mul_Lq_hasSum", "exists_C_C_le_A_star_B_and_HasSum_fun_i_eq_gt_f_i_star_g_i_C", "Not an equality or iff proposition"),
    ("NNReal_rpow_sum_le_const_mul_sum_rpow", "i_in_s_f_i_pow_p_le_hash_s_colon_ge_0_pow_p_minus_1_star_i_in_s_f_i_pow_p", "Not an equality or iff proposition"),
    ("NNReal_Lp_add_le", "i_in_s_f_i_plus_g_i_pow_p_pow_1_slash_p_le_i_in_s_f_i_pow_p_pow_1_slash_p_plus_i", "Not an equality or iff proposition"),
    ("NNReal_Lp_add_le_tsum", "Summable_fun_i_eq_gt_f_i_plus_g_i_pow_p_and_prime_i_f_i_plus_g_i_pow_p_pow_1_slash_p_le", "Not an equality or iff proposition"),
    ("NNReal_Lp_add_le_tsum", "_unknown", "Empty proposition"),
    ("NNReal_Lp_add_le_hasSum", "exists_C_C_le_A_plus_B_and_HasSum_fun_i_eq_gt_f_i_plus_g_i_pow_p_C_pow_p", "Not an equality or iff proposition"),
    ("ENNReal_inner_le_Lp_mul_Lq", "i_in_s_f_i_star_g_i_le_i_in_s_f_i_pow_p_pow_1_slash_p_star_i_in_s_g_i_pow_q_pow_1_slash_q", "Not an equality or iff proposition"),
    ("ENNReal_inner_le_weight_mul_Lp_of_nonneg", "i_in_s_w_i_star_f_i_le_i_in_s_w_i_pow_1_minus_pinv_star_i_in_s_w_i_star_f_i_pow_p_pow_pinv", "Not an equality or iff proposition"),
    ("ENNReal_rpow_sum_le_const_mul_sum_rpow", "i_in_s_f_i_pow_p_le_card_s_colon_ge_0inf_pow_p_minus_1_star_i_in_s_f_i_pow_p", "Not an equality or iff proposition"),
    ("ENNReal_Lp_add_le", "i_in_s_f_i_plus_g_i_pow_p_pow_1_slash_p_le_i_in_s_f_i_pow_p_pow_1_slash_p_plus_i", "Not an equality or iff proposition"),
    ("NNReal_pow_arith_mean_le_arith_mean_pow", "i_in_s_w_i_star_z_i_pow_n_le_i_in_s_w_i_star_z_i_pow_n", "Not an equality or iff proposition"),
    ("NNReal_rpow_arith_mean_le_arith_mean_rpow", "i_in_s_w_i_star_z_i_pow_p_le_i_in_s_w_i_star_z_i_pow_p", "Not an equality or iff proposition"),
    ("NNReal_rpow_arith_mean_le_arith_mean2_rpow", "w_1_star_z_1_plus_w_2_star_z_2_pow_p_le_w_1_star_z_1_pow_p_plus_w_2_star_z_2_pow_p", "Not an equality or iff proposition"),
    ("NNReal_rpow_add_le_mul_rpow_add_rpow", "z_1_plus_z_2_pow_p_le_2_colon_ge_0_pow_p_minus_1_star_z_1_pow_p_plus_z_2_pow_p", "Not an equality or iff proposition"),
    ("NNReal_arith_mean_le_rpow_mean", "i_in_s_w_i_star_z_i_le_i_in_s_w_i_star_z_i_pow_p_pow_1_slash_p", "Not an equality or iff proposition"),
    ("NNReal_add_rpow_le_one_of_add_le_one", "a_pow_p_plus_b_pow_p_le_1", "Not an equality or iff proposition"),
    ("NNReal_add_rpow_le_rpow_add", "a_pow_p_plus_b_pow_p_le_a_plus_b_pow_p", "Not an equality or iff proposition"),
    ("NNReal_rpow_add_rpow_le_add", "a_pow_p_plus_b_pow_p_pow_1_slash_p_le_a_plus_b", "Not an equality or iff proposition"),
    ("NNReal_rpow_add_rpow_le", "a_pow_q_plus_b_pow_q_pow_1_slash_q_le_a_pow_p_plus_b_pow_p_pow_1_slash_p", "Not an equality or iff proposition"),
    ("NNReal_rpow_add_le_add_rpow", "a_plus_b_pow_p_le_a_pow_p_plus_b_pow_p", "Not an equality or iff proposition"),
    ("ENNReal_rpow_arith_mean_le_arith_mean_rpow", "i_in_s_w_i_star_z_i_pow_p_le_i_in_s_w_i_star_z_i_pow_p", "Not an equality or iff proposition"),
    ("ENNReal_rpow_arith_mean_le_arith_mean2_rpow", "w_1_star_z_1_plus_w_2_star_z_2_pow_p_le_w_1_star_z_1_pow_p_plus_w_2_star_z_2_pow_p", "Not an equality or iff proposition"),
]
