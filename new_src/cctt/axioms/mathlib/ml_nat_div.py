"""Mathlib: Nat Div — auto-generated from Mathlib4.

Contains 342 rewrite rules derived from Mathlib theorems.
Plus 182 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_nat_div"
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
# Rewrite rules (342 total)
# ════════════════════════════════════════════════════════════

def _r0000_two_mul_ediv_two_of_even(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.two_mul_ediv_two_of_even
    # Even n → 2 * (n / 2) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Int_two_mul_ediv_two_of_even"))
        except Exception:
            pass
    return results


def _r0001_ceilDiv_eq_add_pred_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.ceilDiv_eq_add_pred_div
    # a ⌈/⌉ b = (a + b - 1) / b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("+", (OVar("a"), OOp("-", (args[1], OLit(1))))), args[1]))
            results.append((rhs, "Mathlib: Nat_ceilDiv_eq_add_pred_div"))
        except Exception:
            pass
    return results


def _r0002_div_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Interval.div_bot
    # s / ⊥ = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Interval_div_bot"))
        except Exception:
            pass
    return results


def _r0003_natCast_eq_divInt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.natCast_eq_divInt
    # ↑n = n /. 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("n", (OVar("slash"), OLit(1),))
            results.append((rhs, "Mathlib: Rat_natCast_eq_divInt"))
    except Exception:
        pass
    return results


def _r0004_angle_div_left_eq_angle_mul_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.angle_div_left_eq_angle_mul_right
    # angle (x / a) y = angle x (y * a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "angle", 2)
    if args is not None:
        try:
            rhs = OOp("angle", (OVar("x"), OOp("*", (args[1], OVar("a"))),))
            results.append((rhs, "Mathlib: Complex_angle_div_left_eq_angle_mul_right"))
        except Exception:
            pass
    return results


def _r0005_norm_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.norm_div
    # ‖z / w‖ = ‖z‖ / ‖w‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("//", (args[0], args[1]))
            results.append((rhs, "Mathlib: Complex_norm_div"))
        except Exception:
            pass
    return results


def _r0006_tanh_eq_sinh_div_cosh(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.tanh_eq_sinh_div_cosh
    # tanh x = sinh x / cosh x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tanh", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("sinh", (args[0],)), OOp("cosh", (args[0],))))
            results.append((rhs, "Mathlib: Complex_tanh_eq_sinh_div_cosh"))
        except Exception:
            pass
    return results


def _r0007_tan_eq_sin_div_cos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.tan_eq_sin_div_cos
    # tan x = sin x / cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tan", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("sin", (args[0],)), OOp("cos", (args[0],))))
            results.append((rhs, "Mathlib: Complex_tan_eq_sin_div_cos"))
        except Exception:
            pass
    return results


def _r0008_arg_div_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_div_self
    # arg (x / x) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_arg_div_self"))
        except Exception:
            pass
    return results


def _r0009_log_div_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.log_div_self
    # log (x / x) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_log_div_self"))
        except Exception:
            pass
    return results


def _r0010_two_zsmul_coe_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.two_zsmul_coe_div_two
    # (2 : ℤ) • (↑(θ / 2) : Angle) = θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_2_colon", 2)
    if args is not None:
        try:
            rhs = OVar("th")
            results.append((rhs, "Mathlib: Real_Angle_two_zsmul_coe_div_two"))
        except Exception:
            pass
    return results


def _r0011_toReal_eq_pi_div_two_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.toReal_eq_pi_div_two_iff
    # θ.toReal = π / 2 ↔ θ = (π / 2 : ℝ)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("th_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("//", (OVar("pi"), OLit(2))), OVar("th"))), OOp("//", (OVar("pi"), OOp("_2", (OVar("colon"), OVar("_unknown"),))))))
            results.append((rhs, "Mathlib: Real_Angle_toReal_eq_pi_div_two_iff"))
    except Exception:
        pass
    return results


def _r0012_exp_pi_div_two_mul_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.exp_pi_div_two_mul_I
    # exp (π / 2 * I) = I
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exp", 1)
    if args is not None:
        try:
            rhs = OVar("I")
            results.append((rhs, "Mathlib: Complex_exp_pi_div_two_mul_I"))
        except Exception:
            pass
    return results


def _r0013_pi_div_two_eq_arcsin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.pi_div_two_eq_arcsin
    # π / 2 = arcsin x ↔ 1 ≤ x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("iff", (OOp("arcsin", (OVar("x"),)), OLit(1))), OVar("x")))
            results.append((rhs, "Mathlib: Real_pi_div_two_eq_arcsin"))
        except Exception:
            pass
    return results


def _r0014_arccos_eq_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arccos_eq_pi_div_two
    # arccos x = π / 2 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arccos", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("//", (OVar("pi"), OLit(2))), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: Real_arccos_eq_pi_div_two"))
        except Exception:
            pass
    return results


def _r0015_units_div_eq_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.units_div_eq_mul
    # u₁ / u₂ = u₁ * u₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("*", (args[0], args[1]))
            results.append((rhs, "Mathlib: Int_units_div_eq_mul"))
        except Exception:
            pass
    return results


def _r0016_div2_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.div2_two
    # div2 2 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "div2", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Nat_div2_two"))
        except Exception:
            pass
    return results


def _r0017_div2_bit0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.div2_bit0
    # div2 (2 * n) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "div2", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Nat_div2_bit0"))
        except Exception:
            pass
    return results


def _r0018_cast_div_div_div_cancel_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.cast_div_div_div_cancel_right
    # (↑(m / d) : K) / (↑(n / d) : K) = (m : K) / n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("m", (OVar("colon"), OVar("K"),)), OVar("n")))
            results.append((rhs, "Mathlib: Nat_cast_div_div_div_cancel_right"))
        except Exception:
            pass
    return results


def _r0019_maxPowDvdDiv_of_not_dvd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.maxPowDvdDiv_of_not_dvd
    # maxPowDvdDiv p n = (0, n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "maxPowDvdDiv", 2)
    if args is not None:
        try:
            rhs = OOp("_0", (args[1],))
            results.append((rhs, "Mathlib: Nat_maxPowDvdDiv_of_not_dvd"))
        except Exception:
            pass
    return results


def _r0020_maxPowDvdDiv_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.maxPowDvdDiv_self
    # p.maxPowDvdDiv p = (1, 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_maxPowDvdDiv", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OLit(1),))
            results.append((rhs, "Mathlib: Nat_maxPowDvdDiv_self"))
        except Exception:
            pass
    return results


def _r0021_divMaxPow_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.divMaxPow_self
    # p.divMaxPow p = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_divMaxPow", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Nat_divMaxPow_self"))
        except Exception:
            pass
    return results


def _r0022_fst_maxPowDvdDiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.fst_maxPowDvdDiv
    # (p.maxPowDvdDiv n).1 = padicValNat p n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_maxPowDvdDiv_n_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("padicValNat", (OVar("p"), OVar("n"),))
            results.append((rhs, "Mathlib: Nat_fst_maxPowDvdDiv"))
    except Exception:
        pass
    return results


def _r0023_snd_maxPowDvdDiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.snd_maxPowDvdDiv
    # (p.maxPowDvdDiv n).2 = n.divMaxPow p
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_maxPowDvdDiv_n_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("n_divMaxPow", (OVar("p"),))
            results.append((rhs, "Mathlib: Nat_snd_maxPowDvdDiv"))
    except Exception:
        pass
    return results


def _r0024_cast_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.cast_div
    # ↑(p / q) = (p / q : α)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_slash_q")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("//", (OVar("p"), OOp("q", (OVar("colon"), OVar("a"),))))
            results.append((rhs, "Mathlib: Rat_cast_div"))
    except Exception:
        pass
    return results


def _r0025_cast_divInt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.cast_divInt
    # (a /. b : α) = a / b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 4)
    if args is not None:
        try:
            rhs = OOp("//", (args[3], args[1]))
            results.append((rhs, "Mathlib: Rat_cast_divInt"))
        except Exception:
            pass
    return results


def _r0026_mkRat_eq_divInt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.mkRat_eq_divInt
    # mkRat n d = n /. d
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mkRat", 2)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("slash"), args[1],))
            results.append((rhs, "Mathlib: Rat_mkRat_eq_divInt"))
        except Exception:
            pass
    return results


def _r0027_divInt_div_divInt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.divInt_div_divInt
    # (n₁ /. d₁) / (n₂ /. d₂) = (n₁ * d₂) /. (d₁ * n₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("n_1_star_d_2", (OVar("slash"), OOp("*", (OVar("d_1"), OVar("n_2"))),))
            results.append((rhs, "Mathlib: Rat_divInt_div_divInt"))
        except Exception:
            pass
    return results


def _r0028_sqrt_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sqrt_div
    # √(x / y) = √x / √y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_slash_y")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("//", (OVar("x"), OVar("y")))
            results.append((rhs, "Mathlib: Real_sqrt_div"))
    except Exception:
        pass
    return results


def _r0029_coe_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IntermediateField.coe_div
    # (↑(x / y) : L) = ↑x / ↑y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_slash_y", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("x"), OVar("y")))
            results.append((rhs, "Mathlib: IntermediateField_coe_div"))
        except Exception:
            pass
    return results


def _r0030_intDegree_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RatFunc.intDegree_div
    # (x / y).intDegree = x.intDegree - y.intDegree
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_slash_y_intDegree")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("x_intDegree"), OVar("y_intDegree")))
            results.append((rhs, "Mathlib: RatFunc_intDegree_div"))
    except Exception:
        pass
    return results


def _r0031_relrank_top_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IntermediateField.relrank_top_right
    # relrank A ⊤ = Module.rank A E
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "relrank", 2)
    if args is not None:
        try:
            rhs = OOp("Module_rank", (args[0], OVar("E"),))
            results.append((rhs, "Mathlib: IntermediateField_relrank_top_right"))
        except Exception:
            pass
    return results


def _r0032_relrank_bot_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IntermediateField.relrank_bot_left
    # relrank ⊥ A = Module.rank F A
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "relrank", 2)
    if args is not None:
        try:
            rhs = OOp("Module_rank", (OVar("F"), args[1],))
            results.append((rhs, "Mathlib: IntermediateField_relrank_bot_left"))
        except Exception:
            pass
    return results


def _r0033_toFinset_divisorsAntidiagonalList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.toFinset_divisorsAntidiagonalList
    # n.divisorsAntidiagonalList.toFinset = n.divisorsAntidiagonal
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_divisorsAntidiagonalList_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n_divisorsAntidiagonal")
            results.append((rhs, "Mathlib: Nat_toFinset_divisorsAntidiagonalList"))
    except Exception:
        pass
    return results


def _r0034_prod_divisors(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.Prime.prod_divisors
    # ∏ x ∈ p.divisors, f x = f p * f 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("f", (OVar("p"),)), OOp("f", (OLit(1),))))
            results.append((rhs, "Mathlib: Nat_Prime_prod_divisors"))
        except Exception:
            pass
    return results


def _r0035_sum_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.sum_div
    # (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("f"), OVar("i"),)))), args[1]))
            results.append((rhs, "Mathlib: Finset_sum_div"))
        except Exception:
            pass
    return results


def _r0036_prod_intervalGapsWithin_mul_prod_eq_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_intervalGapsWithin_mul_prod_eq_div
    # (∏ i ∈ Finset.range (k + 1),       g (F.intervalGapsWithin h a b i).2 / g (F.intervalGapsWithin h a b i).1) *       ∏ z 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("g", (OVar("b"),)), OOp("g", (OVar("a"),))))
            results.append((rhs, "Mathlib: Finset_prod_intervalGapsWithin_mul_prod_eq_div"))
        except Exception:
            pass
    return results


def _r0037_prod_intervalGapsWithin_eq_div_div_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_intervalGapsWithin_eq_div_div_prod
    # (∏ i ∈ Finset.range (k + 1),       g (F.intervalGapsWithin h a b i).2 / g (F.intervalGapsWithin h a b i).1) =     (g b /
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("//", (OOp("g", (OVar("b"),)), OOp("g", (OVar("a"),)))), OOp("//", (OOp("in", (OOp("_unknown", (OVar("z"),)), OOp("F", (OVar("g"), OVar("z_2"),)))), OOp("g", (OVar("z_1"),))))))
            results.append((rhs, "Mathlib: Finset_prod_intervalGapsWithin_eq_div_div_prod"))
        except Exception:
            pass
    return results


def _r0038_prod_Ico_int_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_Ico_int_div
    # ∏ n ∈ Ico (-b : ℤ) b, f n / f (n + 1) = f (-b) / f b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("f", (OVar("minus_b"),)), OOp("f", (OVar("b"),))))
            results.append((rhs, "Mathlib: Finset_prod_Ico_int_div"))
        except Exception:
            pass
    return results


def _r0039_prod_range_div_prod_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_range_div_prod_range
    # ((∏ k ∈ range m, f k) / ∏ k ∈ range n, f k) = ∏ k ∈ range m with n ≤ k, f k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("in", (OOp("_unknown", (OVar("k"),)), OOp("range", (OVar("m"), OVar("with"), OVar("n"),)))), OOp("k", (OVar("f"), OVar("k"),))))
            results.append((rhs, "Mathlib: Finset_prod_range_div_prod_range"))
        except Exception:
            pass
    return results


def _r0040_sum_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.sum_div
    # (∑ i ∈ s, f i) / n = ∑ i ∈ s, f i / n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("f"), OVar("i"),)))), args[1]))
            results.append((rhs, "Mathlib: Nat_sum_div"))
        except Exception:
            pass
    return results


def _r0041_sum_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.sum_div
    # (∑ i ∈ s, f i) / n = ∑ i ∈ s, f i / n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("f"), OVar("i"),)))), args[1]))
            results.append((rhs, "Mathlib: Int_sum_div"))
        except Exception:
            pass
    return results


def _r0042_ediv_two_mul_two_of_even(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.ediv_two_mul_two_of_even
    # Even n → n / 2 * 2 = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Int_ediv_two_mul_two_of_even"))
        except Exception:
            pass
    return results


def _r0043_two_mul_div_two_of_even(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.two_mul_div_two_of_even
    # Even n → 2 * (n / 2) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Nat_two_mul_div_two_of_even"))
        except Exception:
            pass
    return results


def _r0044_div_two_mul_two_of_even(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.div_two_mul_two_of_even
    # Even n → n / 2 * 2 = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Nat_div_two_mul_two_of_even"))
        except Exception:
            pass
    return results


def _r0045_piFinset_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.piFinset_div
    # piFinset (fun i ↦ s i / t i) = piFinset s / piFinset t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "piFinset", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("piFinset", (OVar("s"),)), OOp("piFinset", (OVar("t"),))))
            results.append((rhs, "Mathlib: Fintype_piFinset_div"))
        except Exception:
            pass
    return results


def _r0046_image_apply_finMulAntidiag(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.image_apply_finMulAntidiag
    # (finMulAntidiag d n).image (fun f => f i) = divisors n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "finMulAntidiag_d_n_image", 1)
    if args is not None:
        try:
            rhs = OOp("divisors", (OVar("n"),))
            results.append((rhs, "Mathlib: Nat_image_apply_finMulAntidiag"))
        except Exception:
            pass
    return results


def _r0047_floorDiv_eq_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.floorDiv_eq_div
    # a ⌊/⌋ b = a / b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("a"), args[1]))
            results.append((rhs, "Mathlib: Nat_floorDiv_eq_div"))
        except Exception:
            pass
    return results


def _r0048_coe_floorDiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.coe_floorDiv
    # f ⌊/⌋ a = fun i ↦ f i ⌊/⌋ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 2)
    if args is not None:
        try:
            rhs = OOp("fun", (OVar("i"), OVar("_unknown"), OVar("f"), OVar("i"), args[0], args[1],))
            results.append((rhs, "Mathlib: Finsupp_coe_floorDiv"))
        except Exception:
            pass
    return results


def _r0049_floorDiv_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.floorDiv_apply
    # (f ⌊/⌋ a) i = f i ⌊/⌋ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_slash_a", 1)
    if args is not None:
        try:
            rhs = OOp("f", (args[0], OVar("slash"), OVar("a"),))
            results.append((rhs, "Mathlib: Finsupp_floorDiv_apply"))
        except Exception:
            pass
    return results


def _r0050_mul_cast_floor_div_cancel_of_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.mul_cast_floor_div_cancel_of_pos
    # ⌊a * n⌋ / n = ⌊a⌋
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Int_mul_cast_floor_div_cancel_of_pos"))
        except Exception:
            pass
    return results


def _r0051_mul_natCast_floor_div_cancel(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.mul_natCast_floor_div_cancel
    # ⌊a * n⌋ / n = ⌊a⌋
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Int_mul_natCast_floor_div_cancel"))
        except Exception:
            pass
    return results


def _r0052_cast_mul_floor_div_cancel_of_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.cast_mul_floor_div_cancel_of_pos
    # ⌊n * a⌋ / n = ⌊a⌋
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Int_cast_mul_floor_div_cancel_of_pos"))
        except Exception:
            pass
    return results


def _r0053_natCast_mul_floor_div_cancel(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.natCast_mul_floor_div_cancel
    # ⌊n * a⌋ / n = ⌊a⌋
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Int_natCast_mul_floor_div_cancel"))
        except Exception:
            pass
    return results


def _r0054_floor_div_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.floor_div_natCast
    # ⌊a / n⌋₊ = ⌊a⌋₊ / n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("//", (args[0], args[1]))
            results.append((rhs, "Mathlib: Nat_floor_div_natCast"))
        except Exception:
            pass
    return results


def _r0055_floor_div_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.floor_div_ofNat
    # ⌊a / ofNat(n)⌋₊ = ⌊a⌋₊ / ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("//", (args[0], args[1]))
            results.append((rhs, "Mathlib: Nat_floor_div_ofNat"))
        except Exception:
            pass
    return results


def _r0056_floor_div_eq_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.floor_div_eq_div
    # ⌊(m : K) / n⌋₊ = m / n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("m"), args[1]))
            results.append((rhs, "Mathlib: Nat_floor_div_eq_div"))
        except Exception:
            pass
    return results


def _r0057_mul_cast_floor_div_cancel(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.mul_cast_floor_div_cancel
    # ⌊a * n⌋₊ / n = ⌊a⌋₊
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Nat_mul_cast_floor_div_cancel"))
        except Exception:
            pass
    return results


def _r0058_cast_mul_floor_div_cancel(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.cast_mul_floor_div_cancel
    # ⌊n * a⌋₊ / n = ⌊a⌋₊
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Nat_cast_mul_floor_div_cancel"))
        except Exception:
            pass
    return results


def _r0059_emod_abs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.emod_abs
    # a % |b| = a % b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("a", (args[0], OVar("b"),))
            results.append((rhs, "Mathlib: Int_emod_abs"))
        except Exception:
            pass
    return results


def _r0060_sign_eq_abs_ediv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.sign_eq_abs_ediv
    # sign a = |a| / a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sign", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("pipe_apipe"), args[0]))
            results.append((rhs, "Mathlib: Int_sign_eq_abs_ediv"))
        except Exception:
            pass
    return results


def _r0061_bot_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Interval.bot_div
    # ⊥ / t = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Interval_bot_div"))
        except Exception:
            pass
    return results


def _r0062_two_mul_ediv_two_of_odd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.two_mul_ediv_two_of_odd
    # 2 * (n / 2) = n - 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OVar("n"), OLit(1)))
            results.append((rhs, "Mathlib: Int_two_mul_ediv_two_of_odd"))
        except Exception:
            pass
    return results


def _r0063_mod_two_add_add_odd_mod_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.mod_two_add_add_odd_mod_two
    # m % 2 + (m + n) % 2 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Nat_mod_two_add_add_odd_mod_two"))
        except Exception:
            pass
    return results


def _r0064_even_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.even_div
    # Even (m / n) ↔ m % (2 * n) / n = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Nat_even_div"))
        except Exception:
            pass
    return results


def _r0065_divInt_div_divInt_cancel_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.divInt_div_divInt_cancel_left
    # n /. x / (d /. x) = n /. d
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("slash"), OVar("d"),))
            results.append((rhs, "Mathlib: Rat_divInt_div_divInt_cancel_left"))
        except Exception:
            pass
    return results


def _r0066_divInt_div_divInt_cancel_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.divInt_div_divInt_cancel_right
    # x /. n / (x /. d) = d /. n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("d", (OVar("slash"), OVar("n"),))
            results.append((rhs, "Mathlib: Rat_divInt_div_divInt_cancel_right"))
        except Exception:
            pass
    return results


def _r0067_num_div_den(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.num_div_den
    # (r.num : ℚ) / (r.den : ℚ) = r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OVar("r")
            results.append((rhs, "Mathlib: Rat_num_div_den"))
        except Exception:
            pass
    return results


def _r0068_divInt_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.divInt_pow
    # (num /. den) ^ n = num ^ n /. den ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("num"), OOp("**", (OOp("n", (OVar("slash"), OVar("den"),)), args[1]))))
            results.append((rhs, "Mathlib: Rat_divInt_pow"))
        except Exception:
            pass
    return results


def _r0069_angle_div_right_eq_angle_mul_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.angle_div_right_eq_angle_mul_left
    # angle x (y / a) = angle (x * a) y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "angle", 2)
    if args is not None:
        try:
            rhs = OOp("angle", (OOp("*", (args[0], OVar("a"))), OVar("y"),))
            results.append((rhs, "Mathlib: Complex_angle_div_right_eq_angle_mul_left"))
        except Exception:
            pass
    return results


def _r0070_angle_exp_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.angle_exp_exp
    # angle (exp (x * I)) (exp (y * I)) = |toIocMod Real.two_pi_pos (-π) (x - y)|
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "angle", 2)
    if args is not None:
        try:
            rhs = OOp("pipe_toIocMod", (OVar("Real_two_pi_pos"), OVar("minus_pi"), OVar("x_minus_y_pipe"),))
            results.append((rhs, "Mathlib: Complex_angle_exp_exp"))
        except Exception:
            pass
    return results


def _r0071_cot_eq_cos_div_sin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cot_eq_cos_div_sin
    # cot x = cos x / sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cot", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("cos", (args[0],)), OOp("sin", (args[0],))))
            results.append((rhs, "Mathlib: Complex_cot_eq_cos_div_sin"))
        except Exception:
            pass
    return results


def _r0072_W_eq_integral_sin_pow_div_integral_sin_p(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Wallis.W_eq_integral_sin_pow_div_integral_sin_pow
    # (π / 2)⁻¹ * W k =     (∫ x : ℝ in 0..π, sin x ^ (2 * k + 1)) / ∫ x : ℝ in 0..π, sin x ^ (2 * k)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("**", (OOp("_unknown", (OVar("x"), OVar("colon"), OVar("_unknown"), OVar("in"), OVar("_0_pi"), OVar("sin"), OVar("x"),)), OOp("+", (OOp("*", (OLit(2), OVar("k"))), OLit(1))))), OOp("**", (OOp("_unknown", (OVar("x"), OVar("colon"), OVar("_unknown"), OVar("in"), OVar("_0_pi"), OVar("sin"), OVar("x"),)), OOp("*", (OLit(2), OVar("k")))))))
            results.append((rhs, "Mathlib: Real_Wallis_W_eq_integral_sin_pow_div_integral_sin_pow"))
        except Exception:
            pass
    return results


def _r0073_arg_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_exp
    # arg (exp z) = toIocMod Real.two_pi_pos (-π) z.im
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OOp("toIocMod", (OVar("Real_two_pi_pos"), OVar("minus_pi"), OVar("z_im"),))
            results.append((rhs, "Mathlib: Complex_arg_exp"))
        except Exception:
            pass
    return results


def _r0074_arg_exp_mul_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_exp_mul_I
    # arg (exp (θ * I)) = toIocMod Real.two_pi_pos (-π) θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OOp("toIocMod", (OVar("Real_two_pi_pos"), OVar("minus_pi"), OVar("th"),))
            results.append((rhs, "Mathlib: Complex_arg_exp_mul_I"))
        except Exception:
            pass
    return results


def _r0075_toIocMod_arg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.toIocMod_arg
    # toIocMod Real.two_pi_pos (-π) z.arg = z.arg
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toIocMod", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: Complex_toIocMod_arg"))
        except Exception:
            pass
    return results


def _r0076_arg_eq_pi_div_two_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_eq_pi_div_two_iff
    # arg z = π / 2 ↔ z.re = 0 ∧ 0 < z.im
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("//", (OVar("pi"), OLit(2))), OVar("z_re"))), OOp("<", (OOp("and", (OLit(0), OLit(0))), OVar("z_im")))))
            results.append((rhs, "Mathlib: Complex_arg_eq_pi_div_two_iff"))
        except Exception:
            pass
    return results


def _r0077_arg_mul_cos_add_sin_mul_I_eq_toIocMod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod
    # arg (r * (cos θ + sin θ * I)) = toIocMod Real.two_pi_pos (-π) θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OOp("toIocMod", (OVar("Real_two_pi_pos"), OVar("minus_pi"), OVar("th"),))
            results.append((rhs, "Mathlib: Complex_arg_mul_cos_add_sin_mul_I_eq_toIocMod"))
        except Exception:
            pass
    return results


def _r0078_arg_cos_add_sin_mul_I_eq_toIocMod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_cos_add_sin_mul_I_eq_toIocMod
    # arg (cos θ + sin θ * I) = toIocMod Real.two_pi_pos (-π) θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OOp("toIocMod", (OVar("Real_two_pi_pos"), OVar("minus_pi"), OVar("th"),))
            results.append((rhs, "Mathlib: Complex_arg_cos_add_sin_mul_I_eq_toIocMod"))
        except Exception:
            pass
    return results


def _r0079_arg_div_coe_angle(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_div_coe_angle
    # (arg (x / y) : Real.Angle) = arg x - arg y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 3)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("arg", (OVar("x"),)), OOp("arg", (OVar("y"),))))
            results.append((rhs, "Mathlib: Complex_arg_div_coe_angle"))
        except Exception:
            pass
    return results


def _r0080_log_exp_eq_re_add_toIocMod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.log_exp_eq_re_add_toIocMod
    # log (exp x) = x.re + (toIocMod Real.two_pi_pos (-π) x.im) * I
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("x_re"), OOp("*", (OOp("toIocMod", (OVar("Real_two_pi_pos"), OVar("minus_pi"), OVar("x_im"),)), OVar("I")))))
            results.append((rhs, "Mathlib: Complex_log_exp_eq_re_add_toIocMod"))
        except Exception:
            pass
    return results


def _r0081_rpowIntegrand_0_1_eq_pow_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpowIntegrand₀₁_eq_pow_div
    # rpowIntegrand₀₁ p t x = t ^ (p - 1) * x / (t + x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rpowIntegrand_0_1", 3)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (args[1], OOp("-", (args[0], OLit(1))))), OOp("//", (args[2], OOp("+", (args[1], args[2]))))))
            results.append((rhs, "Mathlib: Real_rpowIntegrand_0_1_eq_pow_div"))
        except Exception:
            pass
    return results


def _r0082_betaIntegral_eq_Gamma_mul_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.betaIntegral_eq_Gamma_mul_div
    # betaIntegral u v = Gamma u * Gamma v / Gamma (u + v)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "betaIntegral", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("Gamma", (args[0],)), OOp("//", (OOp("Gamma", (args[1],)), OOp("Gamma", (OOp("+", (args[0], args[1])),))))))
            results.append((rhs, "Mathlib: Complex_betaIntegral_eq_Gamma_mul_div"))
        except Exception:
            pass
    return results


def _r0083_log_div_log(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.log_div_log
    # log x / log b = logb b x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("logb", (OVar("b"), OVar("x"),))
            results.append((rhs, "Mathlib: Real_log_div_log"))
        except Exception:
            pass
    return results


def _r0084_logb_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.logb_div
    # logb b (x / y) = logb b x - logb b y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logb", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("logb", (args[0], OVar("x"),)), OOp("logb", (args[0], OVar("y"),))))
            results.append((rhs, "Mathlib: Real_logb_div"))
        except Exception:
            pass
    return results


def _r0085_logb_div_base(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.logb_div_base
    # logb (a / b) c = ((logb a c)⁻¹ - (logb b c)⁻¹)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logb", 2)
    if args is not None:
        try:
            rhs = OVar("logb_a_c_inv_minus_logb_b_c_inv_inv")
            results.append((rhs, "Mathlib: Real_logb_div_base"))
        except Exception:
            pass
    return results


def _r0086_div_logb(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.div_logb
    # logb a c / logb b c = logb a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("logb", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Real_div_logb"))
        except Exception:
            pass
    return results


def _r0087_log_div_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.log_div_self
    # log (x / x) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_log_div_self"))
        except Exception:
            pass
    return results


def _r0088_log_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.log_div
    # log (x / y) = log x - log y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("log", (OVar("x"),)), OOp("log", (OVar("y"),))))
            results.append((rhs, "Mathlib: Real_log_div"))
        except Exception:
            pass
    return results


def _r0089_div_rpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.div_rpow
    # (x / y) ^ z = x ^ z / y ^ z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("**", (OVar("x"), args[1])), OOp("**", (OVar("y"), args[1]))))
            results.append((rhs, "Mathlib: Real_div_rpow"))
        except Exception:
            pass
    return results


def _r0090_rpow_div_two_eq_sqrt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_div_two_eq_sqrt
    # x ^ (r / 2) = √x ^ r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], OVar("r")))
            results.append((rhs, "Mathlib: Real_rpow_div_two_eq_sqrt"))
        except Exception:
            pass
    return results


def _r0091_two_nsmul_coe_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.two_nsmul_coe_div_two
    # (2 : ℕ) • (↑(θ / 2) : Angle) = θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_2_colon", 2)
    if args is not None:
        try:
            rhs = OVar("th")
            results.append((rhs, "Mathlib: Real_Angle_two_nsmul_coe_div_two"))
        except Exception:
            pass
    return results


def _r0092_sin_add_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.sin_add_pi_div_two
    # sin (θ + ↑(π / 2)) = cos θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("cos", (OVar("th"),))
            results.append((rhs, "Mathlib: Real_Angle_sin_add_pi_div_two"))
        except Exception:
            pass
    return results


def _r0093_cos_add_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.cos_add_pi_div_two
    # cos (θ + ↑(π / 2)) = -sin θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("minus_sin", (OVar("th"),))
            results.append((rhs, "Mathlib: Real_Angle_cos_add_pi_div_two"))
        except Exception:
            pass
    return results


def _r0094_coe_toIcoMod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.coe_toIcoMod
    # ↑(toIcoMod two_pi_pos ψ θ) = (θ : Angle)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("toIcoMod_two_pi_pos_psi_th")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("th", (OVar("colon"), OVar("Angle"),))
            results.append((rhs, "Mathlib: Real_Angle_coe_toIcoMod"))
    except Exception:
        pass
    return results


def _r0095_coe_toIocMod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.coe_toIocMod
    # ↑(toIocMod two_pi_pos ψ θ) = (θ : Angle)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("toIocMod_two_pi_pos_psi_th")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("th", (OVar("colon"), OVar("Angle"),))
            results.append((rhs, "Mathlib: Real_Angle_coe_toIocMod"))
    except Exception:
        pass
    return results


def _r0096_toReal_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.toReal_coe
    # (θ : Angle).toReal = toIocMod two_pi_pos (-π) θ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("th_colon_Angle_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("toIocMod", (OVar("two_pi_pos"), OVar("minus_pi"), OVar("th"),))
            results.append((rhs, "Mathlib: Real_Angle_toReal_coe"))
    except Exception:
        pass
    return results


def _r0097_toIocMod_toReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.toIocMod_toReal
    # toIocMod two_pi_pos (-π) θ.toReal = θ.toReal
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toIocMod", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: Real_Angle_toIocMod_toReal"))
        except Exception:
            pass
    return results


def _r0098_toReal_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.toReal_pi_div_two
    # ((π / 2 : ℝ) : Angle).toReal = π / 2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pi_slash_2_colon_colon_Angle_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("//", (OVar("pi"), OLit(2)))
            results.append((rhs, "Mathlib: Real_Angle_toReal_pi_div_two"))
    except Exception:
        pass
    return results


def _r0099_abs_toReal_eq_pi_div_two_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.abs_toReal_eq_pi_div_two_iff
    # |θ.toReal| = π / 2 ↔ θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pipe_th_toRealpipe")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("//", (OVar("pi"), OLit(2))), OVar("th"))), OOp("==", (OOp("or", (OOp("//", (OVar("pi"), OOp("_2", (OVar("colon"), OVar("_unknown"),)))), OVar("th"))), OOp("//", (OVar("minus_pi"), OOp("_2", (OVar("colon"), OVar("_unknown"),))))))))
            results.append((rhs, "Mathlib: Real_Angle_abs_toReal_eq_pi_div_two_iff"))
    except Exception:
        pass
    return results


def _r0100_tan_eq_sin_div_cos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.tan_eq_sin_div_cos
    # tan θ = sin θ / cos θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tan", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("sin", (args[0],)), OOp("cos", (args[0],))))
            results.append((rhs, "Mathlib: Real_Angle_tan_eq_sin_div_cos"))
        except Exception:
            pass
    return results


def _r0101_sign_coe_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.sign_coe_pi_div_two
    # (↑(π / 2) : Angle).sign = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pi_slash_2_colon_Angle_sign")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Real_Angle_sign_coe_pi_div_two"))
    except Exception:
        pass
    return results


def _r0102_tan_int_mul_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.tan_int_mul_pi_div_two
    # tan (n * π / 2) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tan", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_tan_int_mul_pi_div_two"))
        except Exception:
            pass
    return results


def _r0103_arctan_eq_pi_div_four(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arctan_eq_pi_div_four
    # arctan x = π / 4 ↔ x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arctan", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("//", (OVar("pi"), OLit(4))), args[0])), OLit(1)))
            results.append((rhs, "Mathlib: Real_arctan_eq_pi_div_four"))
        except Exception:
            pass
    return results


def _r0104_cos_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_pi_div_two
    # cos (π / 2) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_cos_pi_div_two"))
        except Exception:
            pass
    return results


def _r0105_sin_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_pi_div_two
    # sin (π / 2) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Real_sin_pi_div_two"))
        except Exception:
            pass
    return results


def _r0106_sin_add_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_add_pi_div_two
    # sin (x + π / 2) = cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("cos", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_sin_add_pi_div_two"))
        except Exception:
            pass
    return results


def _r0107_cos_add_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_add_pi_div_two
    # cos (x + π / 2) = -sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("minus_sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cos_add_pi_div_two"))
        except Exception:
            pass
    return results


def _r0108_cos_pi_div_four(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_pi_div_four
    # cos (π / 4) = √2 / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("_2"), OLit(2)))
            results.append((rhs, "Mathlib: Real_cos_pi_div_four"))
        except Exception:
            pass
    return results


def _r0109_sin_pi_div_four(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_pi_div_four
    # sin (π / 4) = √2 / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("_2"), OLit(2)))
            results.append((rhs, "Mathlib: Real_sin_pi_div_four"))
        except Exception:
            pass
    return results


def _r0110_cos_pi_div_eight(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_pi_div_eight
    # cos (π / 8) = √(2 + √2) / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("_2_plus_2"), OLit(2)))
            results.append((rhs, "Mathlib: Real_cos_pi_div_eight"))
        except Exception:
            pass
    return results


def _r0111_sin_pi_div_eight(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_pi_div_eight
    # sin (π / 8) = √(2 - √2) / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("_2_minus_2"), OLit(2)))
            results.append((rhs, "Mathlib: Real_sin_pi_div_eight"))
        except Exception:
            pass
    return results


def _r0112_cos_pi_div_sixteen(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_pi_div_sixteen
    # cos (π / 16) = √(2 + √(2 + √2)) / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("_2_plus_2_plus_2"), OLit(2)))
            results.append((rhs, "Mathlib: Real_cos_pi_div_sixteen"))
        except Exception:
            pass
    return results


def _r0113_sin_pi_div_sixteen(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_pi_div_sixteen
    # sin (π / 16) = √(2 - √(2 + √2)) / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("_2_minus_2_plus_2"), OLit(2)))
            results.append((rhs, "Mathlib: Real_sin_pi_div_sixteen"))
        except Exception:
            pass
    return results


def _r0114_cos_pi_div_thirty_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_pi_div_thirty_two
    # cos (π / 32) = √(2 + √(2 + √(2 + √2))) / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("_2_plus_2_plus_2_plus_2"), OLit(2)))
            results.append((rhs, "Mathlib: Real_cos_pi_div_thirty_two"))
        except Exception:
            pass
    return results


def _r0115_sin_pi_div_thirty_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_pi_div_thirty_two
    # sin (π / 32) = √(2 - √(2 + √(2 + √2))) / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("_2_minus_2_plus_2_plus_2"), OLit(2)))
            results.append((rhs, "Mathlib: Real_sin_pi_div_thirty_two"))
        except Exception:
            pass
    return results


def _r0116_cos_pi_div_three(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_pi_div_three
    # cos (π / 3) = 1 / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OLit(1), OLit(2)))
            results.append((rhs, "Mathlib: Real_cos_pi_div_three"))
        except Exception:
            pass
    return results


def _r0117_cos_pi_div_six(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_pi_div_six
    # cos (π / 6) = √3 / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("_3"), OLit(2)))
            results.append((rhs, "Mathlib: Real_cos_pi_div_six"))
        except Exception:
            pass
    return results


def _r0118_sq_cos_pi_div_six(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sq_cos_pi_div_six
    # cos (π / 6) ^ 2 = 3 / 4
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OLit(3), OLit(4)))
            results.append((rhs, "Mathlib: Real_sq_cos_pi_div_six"))
        except Exception:
            pass
    return results


def _r0119_sin_pi_div_six(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_pi_div_six
    # sin (π / 6) = 1 / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OLit(1), OLit(2)))
            results.append((rhs, "Mathlib: Real_sin_pi_div_six"))
        except Exception:
            pass
    return results


def _r0120_sq_sin_pi_div_three(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sq_sin_pi_div_three
    # sin (π / 3) ^ 2 = 3 / 4
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OLit(3), OLit(4)))
            results.append((rhs, "Mathlib: Real_sq_sin_pi_div_three"))
        except Exception:
            pass
    return results


def _r0121_sin_pi_div_three(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_pi_div_three
    # sin (π / 3) = √3 / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("_3"), OLit(2)))
            results.append((rhs, "Mathlib: Real_sin_pi_div_three"))
        except Exception:
            pass
    return results


def _r0122_cos_pi_div_five(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_pi_div_five
    # cos (π / 5) = (1 + √5) / 4
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("+", (OLit(1), OVar("_5"))), OLit(4)))
            results.append((rhs, "Mathlib: Real_cos_pi_div_five"))
        except Exception:
            pass
    return results


def _r0123_cos_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cos_pi_div_two
    # cos (π / 2) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_cos_pi_div_two"))
        except Exception:
            pass
    return results


def _r0124_sin_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sin_pi_div_two
    # sin (π / 2) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_sin_pi_div_two"))
        except Exception:
            pass
    return results


def _r0125_sin_add_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sin_add_pi_div_two
    # sin (x + π / 2) = cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("cos", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_sin_add_pi_div_two"))
        except Exception:
            pass
    return results


def _r0126_cos_add_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cos_add_pi_div_two
    # cos (x + π / 2) = -sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("minus_sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_cos_add_pi_div_two"))
        except Exception:
            pass
    return results


def _r0127_tan_int_mul_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.tan_int_mul_pi_div_two
    # tan (n * π / 2) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tan", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_tan_int_mul_pi_div_two"))
        except Exception:
            pass
    return results


def _r0128_arcsin_eq_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arcsin_eq_pi_div_two
    # arcsin x = π / 2 ↔ 1 ≤ x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arcsin", 1)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("iff", (OOp("//", (OVar("pi"), OLit(2))), OLit(1))), args[0]))
            results.append((rhs, "Mathlib: Real_arcsin_eq_pi_div_two"))
        except Exception:
            pass
    return results


def _r0129_sum_indicator_mod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.sum_indicator_mod
    # f = ∑ a : ZMod m, {n : ℕ | (n : ZMod m) = a}.indicator f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_unknown", (OVar("a"), OVar("colon"), OVar("ZMod"), OVar("m"), OVar("n_colon_pipe_n_colon_ZMod_m_eq_a_indicator"), OVar("f"),))
            results.append((rhs, "Mathlib: Finset_sum_indicator_mod"))
    except Exception:
        pass
    return results


def _r0130_sumByResidueClasses(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.sumByResidueClasses
    # ∑' n, f n = ∑ j : ZMod N, ∑' m, f (j.val + N * m)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prime", 3)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("j"), OVar("colon"), OVar("ZMod"), OVar("N"), OVar("prime"), OVar("m"), args[1], OOp("+", (OVar("j_val"), OOp("*", (OVar("N"), OVar("m"))))),))
            results.append((rhs, "Mathlib: Nat_sumByResidueClasses"))
        except Exception:
            pass
    return results


def _r0131_uniformBell_eq_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.uniformBell_eq_div
    # uniformBell m n = (m * n)! / (n ! ^ m * m !)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "uniformBell", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("m_star_n_bang"), OOp("*", (OOp("**", (OOp("n", (OOp("not", (OVar("_"),)),)), args[0])), OOp("m", (OOp("not", (OVar("_"),)),))))))
            results.append((rhs, "Mathlib: Nat_uniformBell_eq_div"))
        except Exception:
            pass
    return results


def _r0132_even_iff_mod_of_even(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.even_iff_mod_of_even
    # Even k ↔ k.val % 2 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Fin_even_iff_mod_of_even"))
        except Exception:
            pass
    return results


def _r0133_odd_iff_mod_of_even(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.odd_iff_mod_of_even
    # Odd k ↔ k.val % 2 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Fin_odd_iff_mod_of_even"))
        except Exception:
            pass
    return results


def _r0134_divisors_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.divisors_mul
    # divisors (m * n) = divisors m * divisors n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "divisors", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("divisors", (OVar("m"),)), OOp("divisors", (OVar("n"),))))
            results.append((rhs, "Mathlib: Nat_divisors_mul"))
        except Exception:
            pass
    return results


def _r0135_divisors_sq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.Prime.divisors_sq
    # (p ^ 2).divisors = {p ^ 2, p, 1}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_pow_2_divisors")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("p_pow_2_p_1")
            results.append((rhs, "Mathlib: Nat_Prime_divisors_sq"))
    except Exception:
        pass
    return results


def _r0136_nat_divisors_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.nat_divisors_prod
    # divisors (∏ i ∈ s, f i) = ∏ i ∈ s, divisors (f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "divisors", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("divisors"), OOp("f", (OVar("i"),)),))))
            results.append((rhs, "Mathlib: Finset_nat_divisors_prod"))
        except Exception:
            pass
    return results


def _r0137_bodd_add_div2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.bodd_add_div2
    # ∀ n, cond (bodd n) 1 0 + 2 * div2 n = n   | (n : ℕ) =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("pipe"), OOp("n", (OVar("colon"), OVar("_unknown"),)), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: Int_bodd_add_div2"))
        except Exception:
            pass
    return results


def _r0138_bit_decomp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.bit_decomp
    # bit (bodd n) (div2 n) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bit", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Int_bit_decomp"))
        except Exception:
            pass
    return results


def _r0139_cast_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.cast_div
    # ((m / n : ℤ) : α) = m / n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m_slash_n_colon", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("m"), OVar("n")))
            results.append((rhs, "Mathlib: Int_cast_div"))
        except Exception:
            pass
    return results


def _r0140_fdiv_fdiv_eq_fdiv_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.fdiv_fdiv_eq_fdiv_mul
    # (m.fdiv n).fdiv k = m.fdiv (n * k)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m_fdiv_n_fdiv", 1)
    if args is not None:
        try:
            rhs = OOp("m_fdiv", (OOp("*", (OVar("n"), args[0])),))
            results.append((rhs, "Mathlib: Int_fdiv_fdiv_eq_fdiv_mul"))
        except Exception:
            pass
    return results


def _r0141_image_Ico_emod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.image_Ico_emod
    # (Ico n (n + a)).image (· % a) = Ico 0 a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico_n_n_plus_a_image", 1)
    if args is not None:
        try:
            rhs = OOp("Ico", (OLit(0), OVar("a"),))
            results.append((rhs, "Mathlib: Int_image_Ico_emod"))
        except Exception:
            pass
    return results


def _r0142_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.ModEq.eq
    # a ≡ b [ZMOD n] → a % n = b % n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("b", (args[0], args[1],))
            results.append((rhs, "Mathlib: Int_ModEq_eq"))
        except Exception:
            pass
    return results


def _r0143_modEq_iff_add_fac(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.modEq_iff_add_fac
    # a ≡ b [ZMOD n] ↔ ∃ t, b = a + n * t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("a"), OOp("*", (OVar("n"), OVar("t")))))
            results.append((rhs, "Mathlib: Int_modEq_iff_add_fac"))
        except Exception:
            pass
    return results


def _r0144_mod_mul_right_mod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.mod_mul_right_mod
    # a % (b * c) % b = a % b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 4)
    if args is not None:
        try:
            rhs = OOp("a", (args[2], args[3],))
            results.append((rhs, "Mathlib: Int_mod_mul_right_mod"))
        except Exception:
            pass
    return results


def _r0145_mod_mul_left_mod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.mod_mul_left_mod
    # a % (b * c) % c = a % c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 4)
    if args is not None:
        try:
            rhs = OOp("a", (args[2], args[3],))
            results.append((rhs, "Mathlib: Int_mod_mul_left_mod"))
        except Exception:
            pass
    return results


def _r0146_ext_ediv_modEq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.ext_ediv_modEq
    # a = b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("b")
            results.append((rhs, "Mathlib: Int_ext_ediv_modEq"))
    except Exception:
        pass
    return results


def _r0147_ext_ediv_modEq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.ext_ediv_modEq_iff
    # a = b ↔ a / n = b / n ∧ a ≡ b [ZMOD n]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("b"), OOp("//", (OVar("a"), OVar("n"))))), OOp("and", (OOp("//", (OVar("b"), OVar("n"))), OOp("a", (OVar("_unknown"), OVar("b"), OSeq((OOp("ZMOD", (OVar("n"),)),)),))))))
            results.append((rhs, "Mathlib: Int_ext_ediv_modEq_iff"))
    except Exception:
        pass
    return results


def _r0148_modEq_iff_eq_of_div_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.modEq_iff_eq_of_div_eq
    # a ≡ b [ZMOD n] ↔ a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: Int_modEq_iff_eq_of_div_eq"))
        except Exception:
            pass
    return results


def _r0149_units_pow_eq_pow_mod_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.units_pow_eq_pow_mod_two
    # u ^ n = u ^ (n % 2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], OOp("n", (OVar("_unknown"), OLit(2),))))
            results.append((rhs, "Mathlib: Int_units_pow_eq_pow_mod_two"))
        except Exception:
            pass
    return results


def _r0150_toNNRat_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.toNNRat_div
    # toNNRat (p / q) = toNNRat p / toNNRat q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toNNRat", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("toNNRat", (OVar("p"),)), OOp("toNNRat", (OVar("q"),))))
            results.append((rhs, "Mathlib: Rat_toNNRat_div"))
        except Exception:
            pass
    return results


def _r0151_toNNReal_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.toNNReal_div
    # Real.toNNReal (x / y) = Real.toNNReal x / Real.toNNReal y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Real_toNNReal", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("Real_toNNReal", (OVar("x"),)), OOp("Real_toNNReal", (OVar("y"),))))
            results.append((rhs, "Mathlib: Real_toNNReal_div"))
        except Exception:
            pass
    return results


def _r0152_bit_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.bit_div_two
    # bit b n / 2 = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Nat_bit_div_two"))
        except Exception:
            pass
    return results


def _r0153_bit_mod_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.bit_mod_two
    # bit b n % 2 = b.toNat
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bit", 4)
    if args is not None:
        try:
            rhs = OVar("b_toNat")
            results.append((rhs, "Mathlib: Nat_bit_mod_two"))
        except Exception:
            pass
    return results


def _r0154_mod_two_of_bodd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.mod_two_of_bodd
    # n % 2 = (bodd n).toNat
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n", 2)
    if args is not None:
        try:
            rhs = OVar("bodd_n_toNat")
            results.append((rhs, "Mathlib: Nat_mod_two_of_bodd"))
        except Exception:
            pass
    return results


def _r0155_div2_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.div2_val
    # div2 n = n / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "div2", 1)
    if args is not None:
        try:
            rhs = OOp("//", (args[0], OLit(2)))
            results.append((rhs, "Mathlib: Nat_div2_val"))
        except Exception:
            pass
    return results


def _r0156_bit_bodd_div2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.bit_bodd_div2
    # bit (bodd n) (div2 n) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bit", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Nat_bit_bodd_div2"))
        except Exception:
            pass
    return results


def _r0157_div2_bit(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.div2_bit
    # div2 (bit b n) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "div2", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Nat_div2_bit"))
        except Exception:
            pass
    return results


def _r0158_boddDiv2_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.boddDiv2_eq
    # boddDiv2 n = (bodd n, div2 n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "boddDiv2", 1)
    if args is not None:
        try:
            rhs = OOp("bodd", (args[0], OVar("div2"), args[0],))
            results.append((rhs, "Mathlib: Nat_boddDiv2_eq"))
        except Exception:
            pass
    return results


def _r0159_div2_bit1(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.div2_bit1
    # div2 (2 * n + 1) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "div2", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Nat_div2_bit1"))
        except Exception:
            pass
    return results


def _r0160_cast_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.cast_div
    # (↑(m / n) : K) = m / n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m_slash_n", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("m"), OVar("n")))
            results.append((rhs, "Mathlib: Nat_cast_div"))
        except Exception:
            pass
    return results


def _r0161_choose_eq_factorial_div_factorial(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.choose_eq_factorial_div_factorial
    # choose n k = n ! / (k ! * (n - k)!)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "choose", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("n", (OOp("not", (OVar("_"),)),)), OOp("*", (OOp("k", (OOp("not", (OVar("_"),)),)), OVar("n_minus_k_bang")))))
            results.append((rhs, "Mathlib: Nat_choose_eq_factorial_div_factorial"))
        except Exception:
            pass
    return results


def _r0162_choose_eq_asc_factorial_div_factorial(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.choose_eq_asc_factorial_div_factorial
    # (n + k).choose k = (n + 1).ascFactorial k / k !
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n_plus_k_choose", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("n_plus_1_ascFactorial", (args[0],)), OOp("k", (OOp("not", (OVar("_"),)),))))
            results.append((rhs, "Mathlib: Nat_choose_eq_asc_factorial_div_factorial"))
        except Exception:
            pass
    return results


def _r0163_choose_eq_descFactorial_div_factorial(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.choose_eq_descFactorial_div_factorial
    # n.choose k = n.descFactorial k / k !
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n_choose", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("n_descFactorial", (args[0],)), OOp("k", (OOp("not", (OVar("_"),)),))))
            results.append((rhs, "Mathlib: Nat_choose_eq_descFactorial_div_factorial"))
        except Exception:
            pass
    return results


def _r0164_ofDigits_mod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.ofDigits_mod
    # ofDigits b L % k = ofDigits (b % k) L % k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofDigits", 4)
    if args is not None:
        try:
            rhs = OOp("ofDigits", (OOp("b", (args[2], args[3],)), args[1], args[2], args[3],))
            results.append((rhs, "Mathlib: Nat_ofDigits_mod"))
        except Exception:
            pass
    return results


def _r0165_ofDigits_zmod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.ofDigits_zmod
    # ofDigits b L % k = ofDigits (b % k) L % k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofDigits", 4)
    if args is not None:
        try:
            rhs = OOp("ofDigits", (OOp("b", (args[2], args[3],)), args[1], args[2], args[3],))
            results.append((rhs, "Mathlib: Nat_ofDigits_zmod"))
        except Exception:
            pass
    return results


def _r0166_factorization_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.factorization_div
    # (n / d).factorization = n.factorization - d.factorization
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_slash_d_factorization")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("n_factorization"), OVar("d_factorization")))
            results.append((rhs, "Mathlib: Nat_factorization_div"))
    except Exception:
        pass
    return results


def _r0167_ordCompl_div_pow_of_dvd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.ordCompl_div_pow_of_dvd
    # ordCompl[p] (x / p ^ k) = ordCompl[p] x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ordCompl_p", 1)
    if args is not None:
        try:
            rhs = OOp("ordCompl_p", (OVar("x"),))
            results.append((rhs, "Mathlib: Nat_ordCompl_div_pow_of_dvd"))
        except Exception:
            pass
    return results


def _r0168_ordCompl_div_of_dvd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.ordCompl_div_of_dvd
    # ordCompl[p] (x / p) = ordCompl[p] x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ordCompl_p", 1)
    if args is not None:
        try:
            rhs = OOp("ordCompl_p", (OVar("x"),))
            results.append((rhs, "Mathlib: Nat_ordCompl_div_of_dvd"))
        except Exception:
            pass
    return results


def _r0169_coe_divisors_eq_prod_pow_le_factorizatio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.coe_divisors_eq_prod_pow_le_factorization
    # n.divisors = { f.prod (· ^ ·) | f ≤ n.factorization }
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_divisors")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f_prod_pow_pipe_f_le_n_factorization")
            results.append((rhs, "Mathlib: Nat_coe_divisors_eq_prod_pow_le_factorization"))
    except Exception:
        pass
    return results


def _r0170_divisors_eq_image_Iic_factorization_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.divisors_eq_image_Iic_factorization_prod_pow
    # n.divisors = (Finset.Iic n.factorization).image (·.prod (· ^ ·))
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_divisors")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Finset_Iic_n_factorization_image", (OOp("prod", (OOp("**", (OVar("_unknown"), OVar("_unknown"))),)),))
            results.append((rhs, "Mathlib: Nat_divisors_eq_image_Iic_factorization_prod_pow"))
    except Exception:
        pass
    return results


def _r0171_coe_properDivisors_eq_prod_pow_lt_factor(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.coe_properDivisors_eq_prod_pow_lt_factorization
    # n.properDivisors = { f.prod (· ^ ·) | f < n.factorization }
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_properDivisors")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f_prod_pow_pipe_f_lt_n_factorization")
            results.append((rhs, "Mathlib: Nat_coe_properDivisors_eq_prod_pow_lt_factorization"))
    except Exception:
        pass
    return results


def _r0172_properDivisors_eq_image_Iio_factorizatio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.properDivisors_eq_image_Iio_factorization_prod_pow
    # n.properDivisors = (Finset.Iio n.factorization).image (·.prod (· ^ ·))
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_properDivisors")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Finset_Iio_n_factorization_image", (OOp("prod", (OOp("**", (OVar("_unknown"), OVar("_unknown"))),)),))
            results.append((rhs, "Mathlib: Nat_properDivisors_eq_image_Iio_factorization_prod_pow"))
    except Exception:
        pass
    return results


def _r0173_div_mul_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.div_mul_div
    # (k / m) * (m / n) = k / n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("k"), OVar("n")))
            results.append((rhs, "Mathlib: Nat_div_mul_div"))
        except Exception:
            pass
    return results


def _r0174_div_lcm_eq_div_gcd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.div_lcm_eq_div_gcd
    # (k / m).lcm (k / n) = k / (m.gcd n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "k_slash_m_lcm", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("k"), OOp("m_gcd", (OVar("n"),))))
            results.append((rhs, "Mathlib: Nat_div_lcm_eq_div_gcd"))
        except Exception:
            pass
    return results


def _r0175_two_mul_odd_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.two_mul_odd_div_two
    # 2 * (n / 2) = n - 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OVar("n"), OLit(1)))
            results.append((rhs, "Mathlib: Nat_two_mul_odd_div_two"))
        except Exception:
            pass
    return results


def _r0176_log_div_base(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.log_div_base
    # log b (n / b) = log b n - 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("log", (args[0], OVar("n"),)), OLit(1)))
            results.append((rhs, "Mathlib: Nat_log_div_base"))
        except Exception:
            pass
    return results


def _r0177_log_div_base_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.log_div_base_pow
    # log b (n / b ^ k) = log b n - k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("log", (args[0], OVar("n"),)), OVar("k")))
            results.append((rhs, "Mathlib: Nat_log_div_base_pow"))
        except Exception:
            pass
    return results


def _r0178_log_div_mul_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.log_div_mul_self
    # log b (n / b * b) = log b n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 2)
    if args is not None:
        try:
            rhs = OOp("log", (args[0], OVar("n"),))
            results.append((rhs, "Mathlib: Nat_log_div_mul_self"))
        except Exception:
            pass
    return results


def _r0179_go_spec(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.maxPowDvdDiv.go_spec
    # (go n p hnp).2 * p ^ (go n p hnp).1 = n ∧ ¬p ∣ (go n p hnp).2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OVar("n"), OOp("not_p", (OVar("_unknown"), args[0],))))
            results.append((rhs, "Mathlib: Nat_maxPowDvdDiv_go_spec"))
        except Exception:
            pass
    return results


def _r0180_maxPowDvdDiv_base_pow_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.maxPowDvdDiv_base_pow_mul
    # p.maxPowDvdDiv (p ^ k * n) = (padicValNat p n + k, divMaxPow n p)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_maxPowDvdDiv", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("padicValNat", (OVar("p"), OVar("n"),)), OOp("k", (OVar("divMaxPow"), OVar("n"), OVar("p"),))))
            results.append((rhs, "Mathlib: Nat_maxPowDvdDiv_base_pow_mul"))
        except Exception:
            pass
    return results


def _r0181_maxPowDvdDiv_base_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.maxPowDvdDiv_base_mul
    # p.maxPowDvdDiv (p * n) = (padicValNat p n + 1, divMaxPow n p)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_maxPowDvdDiv", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("padicValNat", (OVar("p"), OVar("n"),)), OOp("_1", (OVar("divMaxPow"), OVar("n"), OVar("p"),))))
            results.append((rhs, "Mathlib: Nat_maxPowDvdDiv_base_mul"))
        except Exception:
            pass
    return results


def _r0182_divMaxPow_base_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.divMaxPow_base_mul
    # (p * n).divMaxPow p = n.divMaxPow p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_star_n_divMaxPow", 1)
    if args is not None:
        try:
            rhs = OOp("n_divMaxPow", (args[0],))
            results.append((rhs, "Mathlib: Nat_divMaxPow_base_mul"))
        except Exception:
            pass
    return results


def _r0183_modEq_iff_exists_eq_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.modEq_iff_exists_eq_add
    # a ≡ b [MOD n] ↔ ∃ (t : ℕ), b = a + n * t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("a"), OOp("*", (OVar("n"), OVar("t")))))
            results.append((rhs, "Mathlib: Nat_modEq_iff_exists_eq_add"))
        except Exception:
            pass
    return results


def _r0184_gcd_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.ModEq.gcd_eq
    # gcd a m = gcd b m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "gcd", 2)
    if args is not None:
        try:
            rhs = OOp("gcd", (OVar("b"), args[1],))
            results.append((rhs, "Mathlib: Nat_ModEq_gcd_eq"))
        except Exception:
            pass
    return results


def _r0185_eq_of_abs_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.ModEq.eq_of_abs_lt
    # a = b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("b")
            results.append((rhs, "Mathlib: Nat_ModEq_eq_of_abs_lt"))
    except Exception:
        pass
    return results


def _r0186_eq_of_lt_of_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.ModEq.eq_of_lt_of_lt
    # a = b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("b")
            results.append((rhs, "Mathlib: Nat_ModEq_eq_of_lt_of_lt"))
    except Exception:
        pass
    return results


def _r0187_add_mod_add_ite(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.add_mod_add_ite
    # ((a + b) % c + if c ≤ a % c + b % c then c else 0) = a % c + b % c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("a", (OVar("_unknown"), OVar("c"),)), OOp("b", (OVar("_unknown"), OVar("c"),))))
            results.append((rhs, "Mathlib: Nat_add_mod_add_ite"))
        except Exception:
            pass
    return results


def _r0188_add_mod_of_add_mod_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.add_mod_of_add_mod_lt
    # (a + b) % c = a % c + b % c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_plus_b", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("a", (args[0], args[1],)), OOp("b", (args[0], args[1],))))
            results.append((rhs, "Mathlib: Nat_add_mod_of_add_mod_lt"))
        except Exception:
            pass
    return results


def _r0189_add_mod_add_of_le_add_mod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.add_mod_add_of_le_add_mod
    # (a + b) % c + c = a % c + b % c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("a", (OVar("_unknown"), args[1],)), OOp("b", (OVar("_unknown"), args[1],))))
            results.append((rhs, "Mathlib: Nat_add_mod_add_of_le_add_mod"))
        except Exception:
            pass
    return results


def _r0190_add_div_eq_of_add_mod_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.add_div_eq_of_add_mod_lt
    # (a + b) / c = a / c + b / c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("//", (OVar("a"), args[1])), OOp("//", (OVar("b"), args[1]))))
            results.append((rhs, "Mathlib: Nat_add_div_eq_of_add_mod_lt"))
        except Exception:
            pass
    return results


def _r0191_add_div_of_dvd_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.add_div_of_dvd_right
    # (a + b) / c = a / c + b / c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("//", (OVar("a"), args[1])), OOp("//", (OVar("b"), args[1]))))
            results.append((rhs, "Mathlib: Nat_add_div_of_dvd_right"))
        except Exception:
            pass
    return results


def _r0192_add_div_of_dvd_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.add_div_of_dvd_left
    # (a + b) / c = a / c + b / c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("//", (OVar("a"), args[1])), OOp("//", (OVar("b"), args[1]))))
            results.append((rhs, "Mathlib: Nat_add_div_of_dvd_left"))
        except Exception:
            pass
    return results


def _r0193_add_div_eq_of_le_mod_add_mod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.add_div_eq_of_le_mod_add_mod
    # (a + b) / c = a / c + b / c + 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("//", (OVar("a"), args[1])), OOp("+", (OOp("//", (OVar("b"), args[1])), OLit(1)))))
            results.append((rhs, "Mathlib: Nat_add_div_eq_of_le_mod_add_mod"))
        except Exception:
            pass
    return results


def _r0194_odd_mul_odd_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.odd_mul_odd_div_two
    # m * n / 2 = m * (n / 2) + m / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("*", (args[0], OOp("//", (OVar("n"), OLit(2))))), OOp("//", (args[0], OLit(2)))))
            results.append((rhs, "Mathlib: Nat_odd_mul_odd_div_two"))
        except Exception:
            pass
    return results


def _r0195_odd_of_mod_four_eq_three(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.odd_of_mod_four_eq_three
    # n % 4 = 3 → n % 2 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Nat_odd_of_mod_four_eq_three"))
        except Exception:
            pass
    return results


def _r0196_odd_mod_four_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.odd_mod_four_iff
    # n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), OOp("n", (args[0], OLit(4),)))), OOp("==", (OOp("or", (OLit(1), OOp("n", (args[0], OLit(4),)))), OLit(3)))))
            results.append((rhs, "Mathlib: Nat_odd_mod_four_iff"))
        except Exception:
            pass
    return results


def _r0197_mod_eq_of_modEq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.mod_eq_of_modEq
    # a % n = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: Nat_mod_eq_of_modEq"))
        except Exception:
            pass
    return results


def _r0198_ext_div_modEq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.ext_div_modEq
    # a = b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("b")
            results.append((rhs, "Mathlib: Nat_ext_div_modEq"))
    except Exception:
        pass
    return results


def _r0199_ext_div_modEq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.ext_div_modEq_iff
    # a = b ↔ a / n = b / n ∧ a ≡ b [MOD n]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("b"), OOp("//", (OVar("a"), OVar("n"))))), OOp("and", (OOp("//", (OVar("b"), OVar("n"))), OOp("a", (OVar("_unknown"), OVar("b"), OSeq((OOp("MOD", (OVar("n"),)),)),))))))
            results.append((rhs, "Mathlib: Nat_ext_div_modEq_iff"))
    except Exception:
        pass
    return results


def _r0200_modEq_iff_eq_of_div_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.modEq_iff_eq_of_div_eq
    # a ≡ b [MOD n] ↔ a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: Nat_modEq_iff_eq_of_div_eq"))
        except Exception:
            pass
    return results


def _r0201_primeFactors_div_gcd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.primeFactors_div_gcd
    # primeFactors (m / m.gcd n) = primeFactors m \\ primeFactors n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "primeFactors", 1)
    if args is not None:
        try:
            rhs = OOp("primeFactors", (OVar("m"), OVar("bsl"), OVar("primeFactors"), OVar("n"),))
            results.append((rhs, "Mathlib: Nat_primeFactors_div_gcd"))
        except Exception:
            pass
    return results


def _r0202_totient_div_of_dvd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.totient_div_of_dvd
    # φ (n / d) = #{k ∈ range n | n.gcd k = d}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi", 1)
    if args is not None:
        try:
            rhs = OVar("hash_k_in_range_n_pipe_n_gcd_k_eq_d")
            results.append((rhs, "Mathlib: Nat_totient_div_of_dvd"))
        except Exception:
            pass
    return results


def _r0203_sum_totient(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.sum_totient
    # n.divisors.sum φ = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n_divisors_sum", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Nat_sum_totient"))
        except Exception:
            pass
    return results


def _r0204_totient_eq_div_primeFactors_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.totient_eq_div_primeFactors_mul
    # φ n = (n / ∏ p ∈ n.primeFactors, p) * ∏ p ∈ n.primeFactors, (p - 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("//", (args[0], OOp("in", (OOp("_unknown", (OVar("p"),)), OOp("n_primeFactors", (OVar("p"),)))))), OOp("in", (OOp("_unknown", (OVar("p"),)), OOp("n_primeFactors", (OOp("-", (OVar("p"), OLit(1))),))))))
            results.append((rhs, "Mathlib: Nat_totient_eq_div_primeFactors_mul"))
        except Exception:
            pass
    return results


def _r0205_prime_pow_pow_totient_ediv_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.prime_pow_pow_totient_ediv_prod
    # (p ^ k : ℕ) ^ φ (p ^ k) / ∏ q ∈ (p ^ k).primeFactors, q ^ (φ (p ^ k) / (q - 1)) =         p ^ (p ^ (k - 1) * ((p - 1) * 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("p"), OOp("*", (OOp("**", (OVar("p"), OOp("-", (OVar("k"), OLit(1))))), OOp("*", (OOp("-", (OVar("p"), OLit(1))), OOp("-", (OVar("k"), OLit(1)))))))))
            results.append((rhs, "Mathlib: Nat_prime_pow_pow_totient_ediv_prod"))
        except Exception:
            pass
    return results


def _r0206_intCast_eq_divInt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.intCast_eq_divInt
    # (z : ℚ) = z /. 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "z", 2)
    if args is not None:
        try:
            rhs = OOp("z", (OVar("slash"), OLit(1),))
            results.append((rhs, "Mathlib: Rat_intCast_eq_divInt"))
        except Exception:
            pass
    return results


def _r0207_pow_eq_divInt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.pow_eq_divInt
    # q ^ n = q.num ^ n /. q.den ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("q_num"), OOp("**", (OOp("n", (OVar("slash"), OVar("q_den"),)), args[1]))))
            results.append((rhs, "Mathlib: Rat_pow_eq_divInt"))
        except Exception:
            pass
    return results


def _r0208_add_divInt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.add_divInt
    # (a + b) /. c = a /. c + b /. c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_plus_b", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("a", (args[0], args[1],)), OOp("b", (args[0], args[1],))))
            results.append((rhs, "Mathlib: Rat_add_divInt"))
        except Exception:
            pass
    return results


def _r0209_intCast_div_eq_divInt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.intCast_div_eq_divInt
    # (n : ℚ) / d = n /. d
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("slash"), args[1],))
            results.append((rhs, "Mathlib: Rat_intCast_div_eq_divInt"))
        except Exception:
            pass
    return results


def _r0210_natCast_div_eq_divInt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.natCast_div_eq_divInt
    # (n : ℚ) / d = n /. d
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("slash"), args[1],))
            results.append((rhs, "Mathlib: Rat_natCast_div_eq_divInt"))
        except Exception:
            pass
    return results


def _r0211_divInt_mul_divInt_cancel(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.divInt_mul_divInt_cancel
    # n /. x * (x /. d) = n /. d
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("slash"), OVar("d"),))
            results.append((rhs, "Mathlib: Rat_divInt_mul_divInt_cancel"))
        except Exception:
            pass
    return results


def _r0212_floor_intCast_div_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.floor_intCast_div_natCast
    # ⌊(↑n / ↑d : ℚ)⌋ = n / (↑d : ℤ)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_slash_d_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("//", (OVar("n"), OOp("d", (OVar("colon"), OVar("_unknown"),))))
            results.append((rhs, "Mathlib: Rat_floor_intCast_div_natCast"))
    except Exception:
        pass
    return results


def _r0213_ceil_intCast_div_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.ceil_intCast_div_natCast
    # ⌈(↑n / ↑d : ℚ)⌉ = -((-n) / (↑d : ℤ))
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_slash_d_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_minus_n_slash_d_colon")
            results.append((rhs, "Mathlib: Rat_ceil_intCast_div_natCast"))
    except Exception:
        pass
    return results


def _r0214_floor_natCast_div_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.floor_natCast_div_natCast
    # ⌊(↑n / ↑d : ℚ)⌋ = n / d
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_slash_d_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("//", (OVar("n"), OVar("d")))
            results.append((rhs, "Mathlib: Rat_floor_natCast_div_natCast"))
    except Exception:
        pass
    return results


def _r0215_ceil_natCast_div_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.ceil_natCast_div_natCast
    # ⌈(↑n / ↑d : ℚ)⌉ = -((-n) / d)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_slash_d_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_minus_n_slash_d")
            results.append((rhs, "Mathlib: Rat_ceil_natCast_div_natCast"))
    except Exception:
        pass
    return results


def _r0216_natFloor_natCast_div_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.natFloor_natCast_div_natCast
    # ⌊(↑n / ↑d : ℚ)⌋₊ = n / d
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_slash_d_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("//", (OVar("n"), OVar("d")))
            results.append((rhs, "Mathlib: Rat_natFloor_natCast_div_natCast"))
    except Exception:
        pass
    return results


def _r0217_mod_nat_eq_sub_mul_floor_rat_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.mod_nat_eq_sub_mul_floor_rat_div
    # n % d = n - d * ⌊(n : ℚ) / d⌋
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("-", (OVar("n"), args[1])), OOp("//", (OVar("n_colon"), args[1]))))
            results.append((rhs, "Mathlib: Int_mod_nat_eq_sub_mul_floor_rat_div"))
        except Exception:
            pass
    return results


def _r0218_exists_eq_mul_div_num_and_eq_mul_div_den(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.exists_eq_mul_div_num_and_eq_mul_div_den
    # ∃ c : ℤ, n = c * ((n : ℚ) / d).num ∧ (d : ℤ) = c * ((n : ℚ) / d).den
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 4)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("and", (OOp("*", (args[0], OVar("n_colon_slash_d_num"))), OOp("d", (args[1], args[2],)))), OOp("*", (args[0], OVar("n_colon_slash_d_den")))))
            results.append((rhs, "Mathlib: Rat_exists_eq_mul_div_num_and_eq_mul_div_den"))
        except Exception:
            pass
    return results


def _r0219_ofCauchy_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.ofCauchy_div
    # (⟨f / g⟩ : ℝ) = (⟨f⟩ : ℝ) / (⟨g⟩ : ℝ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_slash_g", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("f", (args[0], args[1],)), OOp("g", (args[0], args[1],))))
            results.append((rhs, "Mathlib: Real_ofCauchy_div"))
        except Exception:
            pass
    return results


def _r0220_div_sqrt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.div_sqrt
    # x / √x = √x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Real_div_sqrt"))
        except Exception:
            pass
    return results


def _r0221_sqrt_div_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sqrt_div_self
    # √x / x = (√x)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OVar("x_inv")
            results.append((rhs, "Mathlib: Real_sqrt_div_self"))
        except Exception:
            pass
    return results


def _r0222_range_mul_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.range_mul_add
    # Set.range (fun n : ℕ ↦ m * n + k) = {n : ℕ | (n : ZMod m) = k ∧ k ≤ n}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_range", 1)
    if args is not None:
        try:
            rhs = OVar("n_colon_pipe_n_colon_ZMod_m_eq_k_and_k_le_n")
            results.append((rhs, "Mathlib: Nat_range_mul_add"))
        except Exception:
            pass
    return results


def _r0223_finrank_zmod_extension(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FiniteField.finrank_zmod_extension
    # Module.finrank (ZMod p) (Extension k p n) = Module.finrank (ZMod p) k * n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Module_finrank", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("Module_finrank", (OOp("ZMod", (OVar("p"),)), OVar("k"),)), OVar("n")))
            results.append((rhs, "Mathlib: FiniteField_finrank_zmod_extension"))
        except Exception:
            pass
    return results


def _r0224_finrank_extension(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FiniteField.finrank_extension
    # Module.finrank k (Extension k p n) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Module_finrank", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: FiniteField_finrank_extension"))
        except Exception:
            pass
    return results


def _r0225_mem_adjoin_iff_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IntermediateField.mem_adjoin_iff_div
    # x ∈ adjoin F S ↔     ∃ r ∈ Algebra.adjoin F S, ∃ s ∈ Algebra.adjoin F S, x = r / s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("r"), OVar("s")))
            results.append((rhs, "Mathlib: IntermediateField_mem_adjoin_iff_div"))
        except Exception:
            pass
    return results


def _r0226_ofFractionRing_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RatFunc.ofFractionRing_div
    # ofFractionRing (p / q) = ofFractionRing p / ofFractionRing q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofFractionRing", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("ofFractionRing", (OVar("p"),)), OOp("ofFractionRing", (OVar("q"),))))
            results.append((rhs, "Mathlib: RatFunc_ofFractionRing_div"))
        except Exception:
            pass
    return results


def _r0227_finrank_eq_max_natDegree(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RatFunc.finrank_eq_max_natDegree
    # Module.finrank K⟮f⟯ K⟮X⟯ = max f.num.natDegree f.denom.natDegree
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Module_finrank", 2)
    if args is not None:
        try:
            rhs = OOp("max", (OVar("f_num_natDegree"), OVar("f_denom_natDegree"),))
            results.append((rhs, "Mathlib: RatFunc_finrank_eq_max_natDegree"))
        except Exception:
            pass
    return results


def _r0228_phi_natDegree(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RatFunc.Luroth.φ_natDegree
    # (φ E).natDegree = Module.finrank E K⟮X⟯
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi_E_natDegree")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Module_finrank", (OVar("E"), OVar("K_X"),))
            results.append((rhs, "Mathlib: RatFunc_Luroth_phi_natDegree"))
    except Exception:
        pass
    return results


def _r0229_relrank_eq_rank_of_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IntermediateField.relrank_eq_rank_of_le
    # relrank A B = Module.rank A (extendScalars h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "relrank", 2)
    if args is not None:
        try:
            rhs = OOp("Module_rank", (args[0], OOp("extendScalars", (OVar("h"),)),))
            results.append((rhs, "Mathlib: IntermediateField_relrank_eq_rank_of_le"))
        except Exception:
            pass
    return results


def _r0230_relrank_mul_rank_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IntermediateField.relrank_mul_rank_top
    # relrank A B * Module.rank B E = Module.rank A E
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("Module_rank", (OVar("A"), OVar("E"),))
            results.append((rhs, "Mathlib: IntermediateField_relrank_mul_rank_top"))
        except Exception:
            pass
    return results


def _r0231_rank_bot_mul_relrank(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IntermediateField.rank_bot_mul_relrank
    # Module.rank F A * relrank A B = Module.rank F B
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("Module_rank", (OVar("F"), OVar("B"),))
            results.append((rhs, "Mathlib: IntermediateField_rank_bot_mul_relrank"))
        except Exception:
            pass
    return results


def _r0232_rank_rat_real(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rank_rat_real
    # Module.rank ℚ ℝ = continuum
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Module_rank", 2)
    if args is not None:
        try:
            rhs = OVar("continuum")
            results.append((rhs, "Mathlib: Real_rank_rat_real"))
        except Exception:
            pass
    return results


def _r0233_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ComplexStarModule.ext
    # x = y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("y")
            results.append((rhs, "Mathlib: ComplexStarModule_ext"))
    except Exception:
        pass
    return results


def _r0234_ext_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ComplexStarModule.ext_iff
    # x = y ↔ ℜ x = ℜ y ∧ ℑ x = ℑ y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("y"), OOp("_unknown", (OVar("x"),)))), OOp("==", (OOp("and", (OOp("_unknown", (OVar("y"),)), OOp("_unknown", (OVar("x"),)))), OOp("_unknown", (OVar("y"),))))))
            results.append((rhs, "Mathlib: ComplexStarModule_ext_iff"))
    except Exception:
        pass
    return results


def _r0235_comp_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Integrable.comp_div
    # Integrable fun x => g (x / R)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Integrable", 2)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("g"), OOp("//", (args[1], OVar("R"))),))
            results.append((rhs, "Mathlib: Integrable_comp_div"))
        except Exception:
            pass
    return results


def _r0236_sum_divisors(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.sum_divisors
    # ∑ d ∈ n.divisors, d = ∏ p ∈ n.primeFactors, ∑ k ∈ .range (n.factorization p + 1), p ^ k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("p"),)), OOp("in", (OOp("n_primeFactors", (OVar("_unknown"), OVar("k"),)), OOp("**", (OOp("range", (OVar("n_factorization_p_plus_1"), OVar("p"),)), OVar("k")))))))
            results.append((rhs, "Mathlib: Nat_sum_divisors"))
        except Exception:
            pass
    return results


def _r0237_sum_divisors_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.Coprime.sum_divisors_mul
    # ∑ d ∈ (m * n).divisors, d = (∑ d ∈ m.divisors, d) * ∑ d ∈ n.divisors, d
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("in", (OOp("_unknown", (OVar("d"),)), OOp("m_divisors", (OVar("d"),)))), OOp("in", (OOp("_unknown", (OVar("d"),)), OOp("n_divisors", (OVar("d"),))))))
            results.append((rhs, "Mathlib: Nat_Coprime_sum_divisors_mul"))
        except Exception:
            pass
    return results


def _r0238_insert_self_properDivisors(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.insert_self_properDivisors
    # insert n (properDivisors n) = divisors n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "insert", 2)
    if args is not None:
        try:
            rhs = OOp("divisors", (args[0],))
            results.append((rhs, "Mathlib: Nat_insert_self_properDivisors"))
        except Exception:
            pass
    return results


def _r0239_cons_self_properDivisors(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.cons_self_properDivisors
    # cons n (properDivisors n) self_notMem_properDivisors = divisors n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cons", 3)
    if args is not None:
        try:
            rhs = OOp("divisors", (args[0],))
            results.append((rhs, "Mathlib: Nat_cons_self_properDivisors"))
        except Exception:
            pass
    return results


def _r0240_mem_divisorsAntidiagonal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.mem_divisorsAntidiagonal
    # x ∈ divisorsAntidiagonal n ↔ x.fst * x.snd = n ∧ n ≠ 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("and", (OVar("n"), OVar("n"))), OLit(0)))
            results.append((rhs, "Mathlib: Nat_mem_divisorsAntidiagonal"))
        except Exception:
            pass
    return results


def _r0241_val_divisorsAntidiagonal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.val_divisorsAntidiagonal
    # (divisorsAntidiagonal n).val = divisorsAntidiagonalList n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("divisorsAntidiagonal_n_val")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("divisorsAntidiagonalList", (OVar("n"),))
            results.append((rhs, "Mathlib: Nat_val_divisorsAntidiagonal"))
    except Exception:
        pass
    return results


def _r0242_mem_divisorsAntidiagonalList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.mem_divisorsAntidiagonalList
    # a ∈ n.divisorsAntidiagonalList ↔ a.1 * a.2 = n ∧ n ≠ 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("and", (OVar("n"), OVar("n"))), OLit(0)))
            results.append((rhs, "Mathlib: Nat_mem_divisorsAntidiagonalList"))
        except Exception:
            pass
    return results


def _r0243_sup_divisors_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.sup_divisors_id
    # n.divisors.sup id = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n_divisors_sup", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Nat_sup_divisors_id"))
        except Exception:
            pass
    return results


def _r0244_mem_properDivisors_iff_exists(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.mem_properDivisors_iff_exists
    # m ∈ n.properDivisors ↔ ∃ k > 1, n = m * k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, ">", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("m"), OVar("k")))
            results.append((rhs, "Mathlib: Nat_mem_properDivisors_iff_exists"))
        except Exception:
            pass
    return results


def _r0245_prodMk_mem_divisorsAntidiag(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.prodMk_mem_divisorsAntidiag
    # (x, y) ∈ n.divisorsAntidiagonal ↔ x * y = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Nat_prodMk_mem_divisorsAntidiag"))
        except Exception:
            pass
    return results


def _r0246_image_fst_divisorsAntidiagonal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.image_fst_divisorsAntidiagonal
    # (divisorsAntidiagonal n).image Prod.fst = divisors n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "divisorsAntidiagonal_n_image", 1)
    if args is not None:
        try:
            rhs = OOp("divisors", (OVar("n"),))
            results.append((rhs, "Mathlib: Nat_image_fst_divisorsAntidiagonal"))
        except Exception:
            pass
    return results


def _r0247_image_snd_divisorsAntidiagonal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.image_snd_divisorsAntidiagonal
    # (divisorsAntidiagonal n).image Prod.snd = divisors n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "divisorsAntidiagonal_n_image", 1)
    if args is not None:
        try:
            rhs = OOp("divisors", (OVar("n"),))
            results.append((rhs, "Mathlib: Nat_image_snd_divisorsAntidiagonal"))
        except Exception:
            pass
    return results


def _r0248_sum_divisors_eq_sum_properDivisors_add_s(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.sum_divisors_eq_sum_properDivisors_add_self
    # ∑ i ∈ divisors n, i = (∑ i ∈ properDivisors n, i) + n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("properDivisors", (OVar("n"), OVar("i"),)))), OVar("n")))
            results.append((rhs, "Mathlib: Nat_sum_divisors_eq_sum_properDivisors_add_self"))
        except Exception:
            pass
    return results


def _r0249_perfect_iff_sum_properDivisors(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.perfect_iff_sum_properDivisors
    # Perfect n ↔ ∑ i ∈ properDivisors n, i = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Nat_perfect_iff_sum_properDivisors"))
        except Exception:
            pass
    return results


def _r0250_perfect_iff_sum_divisors_eq_two_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.perfect_iff_sum_divisors_eq_two_mul
    # Perfect n ↔ ∑ i ∈ divisors n, i = 2 * n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OLit(2), OVar("n")))
            results.append((rhs, "Mathlib: Nat_perfect_iff_sum_divisors_eq_two_mul"))
        except Exception:
            pass
    return results


def _r0251_mem_divisors_prime_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.mem_divisors_prime_pow
    # x ∈ divisors (p ^ k) ↔ ∃ j ≤ k, x = p ^ j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("p"), OVar("j")))
            results.append((rhs, "Mathlib: Nat_mem_divisors_prime_pow"))
        except Exception:
            pass
    return results


def _r0252_divisors(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.Prime.divisors
    # divisors p = {1, p}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "divisors", 1)
    if args is not None:
        try:
            rhs = OVar("_1_p")
            results.append((rhs, "Mathlib: Nat_Prime_divisors"))
        except Exception:
            pass
    return results


def _r0253_properDivisors(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.Prime.properDivisors
    # properDivisors p = {1}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "properDivisors", 1)
    if args is not None:
        try:
            rhs = OVar("_1")
            results.append((rhs, "Mathlib: Nat_Prime_properDivisors"))
        except Exception:
            pass
    return results


def _r0254_divisors_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.divisors_inj
    # a.divisors = b.divisors ↔ a = b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_divisors")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("b_divisors"), OVar("a"))), OVar("b")))
            results.append((rhs, "Mathlib: Nat_divisors_inj"))
    except Exception:
        pass
    return results


def _r0255_sum_properDivisors_dvd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.sum_properDivisors_dvd
    # ∑ x ∈ n.properDivisors, x = 1 ∨ ∑ x ∈ n.properDivisors, x = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OLit(1), OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("n_properDivisors", (OVar("x"),)))))), OVar("n")))
            results.append((rhs, "Mathlib: Nat_sum_properDivisors_dvd"))
        except Exception:
            pass
    return results


def _r0256_prod_properDivisors(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.Prime.prod_properDivisors
    # ∏ x ∈ p.properDivisors, f x = f 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OLit(1),))
            results.append((rhs, "Mathlib: Nat_Prime_prod_properDivisors"))
        except Exception:
            pass
    return results


def _r0257_mem_properDivisors_prime_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.mem_properDivisors_prime_pow
    # x ∈ properDivisors (p ^ k) ↔ ∃ (j : ℕ) (_ : j < k), x = p ^ j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("p"), OVar("j")))
            results.append((rhs, "Mathlib: Nat_mem_properDivisors_prime_pow"))
        except Exception:
            pass
    return results


def _r0258_prod_properDivisors_prime_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.prod_properDivisors_prime_pow
    # (∏ x ∈ (p ^ k).properDivisors, f x) = ∏ x ∈ range k, f (p ^ x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("range", (OVar("k"), OVar("f"), OOp("**", (OVar("p"), OVar("x"))),))))
            results.append((rhs, "Mathlib: Nat_prod_properDivisors_prime_pow"))
        except Exception:
            pass
    return results


def _r0259_prod_divisors_prime_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.prod_divisors_prime_pow
    # (∏ x ∈ (p ^ k).divisors, f x) = ∏ x ∈ range (k + 1), f (p ^ x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("range", (OVar("k_plus_1"), OVar("f"), OOp("**", (OVar("p"), OVar("x"))),))))
            results.append((rhs, "Mathlib: Nat_prod_divisors_prime_pow"))
        except Exception:
            pass
    return results


def _r0260_prod_divisorsAntidiagonal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.prod_divisorsAntidiagonal
    # ∏ i ∈ n.divisorsAntidiagonal, f i.1 i.2 = ∏ i ∈ n.divisors, f i (n / i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("n_divisors", (OVar("f"), OVar("i"), OOp("//", (OVar("n"), OVar("i"))),))))
            results.append((rhs, "Mathlib: Nat_prod_divisorsAntidiagonal"))
        except Exception:
            pass
    return results


def _r0261_image_div_divisors_eq_divisors(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.image_div_divisors_eq_divisors
    # image (fun x : ℕ => n / x) n.divisors = n.divisors
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Nat_image_div_divisors_eq_divisors"))
        except Exception:
            pass
    return results


def _r0262_prod_div_divisors(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.prod_div_divisors
    # (∏ d ∈ n.divisors, f (n / d)) = n.divisors.prod f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("n_divisors_prod", (OVar("f"),))
            results.append((rhs, "Mathlib: Nat_prod_div_divisors"))
        except Exception:
            pass
    return results


def _r0263_mem_divisorsAntidiag(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.mem_divisorsAntidiag
    # ∀ {z} {xy : ℤ × ℤ}, xy ∈ divisorsAntidiag z ↔ xy.fst * xy.snd = z ∧ z ≠ 0   | (n : ℕ), ((x : ℕ), (y : ℕ)) =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("and", (OVar("z"), OVar("z"))), OOp("_0", (OVar("pipe"), OVar("n_colon"), OOp("x_colon", (OOp("y", (OVar("colon"), OVar("_unknown"),)),)), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: Int_mem_divisorsAntidiag"))
        except Exception:
            pass
    return results


def _r0264_divisorsAntidiagonal_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.divisorsAntidiagonal_two
    # Int.divisorsAntidiag 2 = {(1, 2), (2, 1), (-1, -2), (-2, -1)}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Int_divisorsAntidiag", 1)
    if args is not None:
        try:
            rhs = OVar("_1_2_2_1_minus_1_minus_2_minus_2_minus_1")
            results.append((rhs, "Mathlib: Int_divisorsAntidiagonal_two"))
        except Exception:
            pass
    return results


def _r0265_divisorsAntidiagonal_three(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.divisorsAntidiagonal_three
    # Int.divisorsAntidiag 3 = {(1, 3), (3, 1), (-1, -3), (-3, -1)}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Int_divisorsAntidiag", 1)
    if args is not None:
        try:
            rhs = OVar("_1_3_3_1_minus_1_minus_3_minus_3_minus_1")
            results.append((rhs, "Mathlib: Int_divisorsAntidiagonal_three"))
        except Exception:
            pass
    return results


def _r0266_divisorsAntidiagonal_four(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.divisorsAntidiagonal_four
    # Int.divisorsAntidiag 4 = {(1, 4), (2, 2), (4, 1), (-1, -4), (-2, -2), (-4, -1)}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Int_divisorsAntidiag", 1)
    if args is not None:
        try:
            rhs = OVar("_1_4_2_2_4_1_minus_1_minus_4_minus_2_minus_2_minus_4_minus_1")
            results.append((rhs, "Mathlib: Int_divisorsAntidiagonal_four"))
        except Exception:
            pass
    return results


def _r0267_prodMk_mem_divisorsAntidiag(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.prodMk_mem_divisorsAntidiag
    # (x, y) ∈ z.divisorsAntidiag ↔ x * y = z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("z")
            results.append((rhs, "Mathlib: Int_prodMk_mem_divisorsAntidiag"))
        except Exception:
            pass
    return results


def _r0268_forall_exists_prime_gt_and_eq_mod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.forall_exists_prime_gt_and_eq_mod
    # ∃ p > n, p.Prime ∧ (p : ZMod q) = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, ">", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Nat_forall_exists_prime_gt_and_eq_mod"))
        except Exception:
            pass
    return results


def _r0269_finrank(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsCyclotomicExtension.Rat.finrank
    # Module.finrank ℚ K = k.totient
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Module_finrank", 2)
    if args is not None:
        try:
            rhs = OVar("k_totient")
            results.append((rhs, "Mathlib: IsCyclotomicExtension_Rat_finrank"))
        except Exception:
            pass
    return results


def _r0270_galEquivZMod_apply_of_pow_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
    # σ x = x ^ (galEquivZMod n K σ).val.val
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sig", 1)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], OVar("galEquivZMod_n_K_sig_val_val")))
            results.append((rhs, "Mathlib: IsCyclotomicExtension_Rat_galEquivZMod_apply_of_pow_eq"))
        except Exception:
            pass
    return results


def _r0271_galEquivZMod_smul_of_pow_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq
    # σ • x = x ^ (galEquivZMod n K σ).val.val
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sig", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[1], OVar("galEquivZMod_n_K_sig_val_val")))
            results.append((rhs, "Mathlib: IsCyclotomicExtension_Rat_galEquivZMod_smul_of_pow_eq"))
        except Exception:
            pass
    return results


def _r0272_pow_add_totient_mod_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.pow_add_totient_mod_eq
    # (x ^ (k + φ n)) % n = (x ^ k) % n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_pow_k_plus_phi_n", 2)
    if args is not None:
        try:
            rhs = OOp("x_pow_k", (args[0], args[1],))
            results.append((rhs, "Mathlib: Nat_pow_add_totient_mod_eq"))
        except Exception:
            pass
    return results


def _r0273_pow_add_mul_totient_mod_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.pow_add_mul_totient_mod_eq
    # (x ^ (k + l * φ n)) % n = (x ^ k) % n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_pow_k_plus_l_star_phi_n", 2)
    if args is not None:
        try:
            rhs = OOp("x_pow_k", (args[0], args[1],))
            results.append((rhs, "Mathlib: Nat_pow_add_mul_totient_mod_eq"))
        except Exception:
            pass
    return results


def _r0274_pow_totient_mod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.pow_totient_mod
    # x ^ k % n = x ^ (k % φ n) % n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], OOp("k_phi_n", (OVar("_unknown"), OVar("n"),))))
            results.append((rhs, "Mathlib: Nat_pow_totient_mod"))
        except Exception:
            pass
    return results


def _r0275_eq_sq_add_sq_iff_eq_sq_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.eq_sq_add_sq_iff_eq_sq_mul
    # (∃ x y : ℕ, n = x ^ 2 + y ^ 2) ↔ ∃ a b : ℕ, n = a ^ 2 * b ∧ IsSquare (-1 : ZMod b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("*", (OOp("**", (OVar("a"), OLit(2))), OVar("b"))), OOp("IsSquare", (OOp("minus_1", (OVar("colon"), OVar("ZMod"), OVar("b"),)),))))
            results.append((rhs, "Mathlib: Nat_eq_sq_add_sq_iff_eq_sq_mul"))
        except Exception:
            pass
    return results


def _r0276_frequently_mod_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.frequently_mod_eq
    # ∃ᶠ m in atTop, m % n = d
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 6)
    if args is not None:
        try:
            rhs = OVar("d")
            results.append((rhs, "Mathlib: Nat_frequently_mod_eq"))
        except Exception:
            pass
    return results


def _r0277_galoisConnection_mul_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.galoisConnection_mul_div
    # GaloisConnection (fun n => n * k) fun n => n / k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "GaloisConnection", 3)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("gt", (args[2],)), OVar("k")))
            results.append((rhs, "Mathlib: Nat_galoisConnection_mul_div"))
        except Exception:
            pass
    return results


def _r0278_cast_choose_eq_ascPochhammer_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.cast_choose_eq_ascPochhammer_div
    # (a.choose b : K) = (ascPochhammer K b).eval ↑(a - (b - 1)) / b !
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_choose", 3)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("ascPochhammer_K_b_eval", (OVar("a_minus_b_minus_1"),)), OOp("b", (OOp("not", (OVar("_"),)),))))
            results.append((rhs, "Mathlib: Nat_cast_choose_eq_ascPochhammer_div"))
        except Exception:
            pass
    return results


def _r0279_div_lt_div_iff_mul_lt_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.div_lt_div_iff_mul_lt_mul
    # (a : ℚ) / b < c / d ↔ a * d < c * b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("*", (OVar("a"), OVar("d"))), OOp("*", (OVar("c"), OVar("b")))))
            results.append((rhs, "Mathlib: Rat_div_lt_div_iff_mul_lt_mul"))
        except Exception:
            pass
    return results


def _r0280_arcsin_lt_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arcsin_lt_pi_div_two
    # arcsin x < π / 2 ↔ x < 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("x"), OLit(1)))
            results.append((rhs, "Mathlib: Real_arcsin_lt_pi_div_two"))
        except Exception:
            pass
    return results


def _r0281_pi_div_two_le_arcsin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.pi_div_two_le_arcsin
    # π / 2 ≤ arcsin x ↔ 1 ≤ x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OLit(1), OVar("x")))
            results.append((rhs, "Mathlib: Real_pi_div_two_le_arcsin"))
        except Exception:
            pass
    return results


def _r0282_pi_div_four_le_arcsin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.pi_div_four_le_arcsin
    # π / 4 ≤ arcsin x ↔ √2 / 2 ≤ x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("//", (OVar("_2"), OLit(2))), OVar("x")))
            results.append((rhs, "Mathlib: Real_pi_div_four_le_arcsin"))
        except Exception:
            pass
    return results


def _r0283_arccos_lt_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arccos_lt_pi_div_two
    # arccos x < π / 2 ↔ 0 < x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OLit(0), OVar("x")))
            results.append((rhs, "Mathlib: Real_arccos_lt_pi_div_two"))
        except Exception:
            pass
    return results


def _r0284_arccos_le_pi_div_four(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arccos_le_pi_div_four
    # arccos x ≤ π / 4 ↔ √2 / 2 ≤ x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("//", (OVar("_2"), OLit(2))), OVar("x")))
            results.append((rhs, "Mathlib: Real_arccos_le_pi_div_four"))
        except Exception:
            pass
    return results


def _r0285_modEq_abs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.modEq_abs
    # a ≡ b [ZMOD |n|] ↔ a ≡ b [ZMOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 3)
    if args is not None:
        try:
            rhs = OOp("a", (args[0], args[1], OSeq((OOp("ZMOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Int_modEq_abs"))
        except Exception:
            pass
    return results


def _r0286_modEq_natAbs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.modEq_natAbs
    # a ≡ b [ZMOD n.natAbs] ↔ a ≡ b [ZMOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 3)
    if args is not None:
        try:
            rhs = OOp("a", (args[0], args[1], OSeq((OOp("ZMOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Int_modEq_natAbs"))
        except Exception:
            pass
    return results


def _r0287_add_modEq_right_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.add_modEq_right_iff
    # a + b ≡ b [ZMOD n] ↔ n ∣ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("_unknown"), args[0],))
            results.append((rhs, "Mathlib: Int_add_modEq_right_iff"))
        except Exception:
            pass
    return results


def _r0288_left_modEq_add_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.left_modEq_add_iff
    # a ≡ a + b [ZMOD n] ↔ n ∣ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("_unknown"), OVar("b"),))
            results.append((rhs, "Mathlib: Int_left_modEq_add_iff"))
        except Exception:
            pass
    return results


def _r0289_right_modEq_add_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.right_modEq_add_iff
    # b ≡ a + b [ZMOD n] ↔ n ∣ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("_unknown"), OVar("a"),))
            results.append((rhs, "Mathlib: Int_right_modEq_add_iff"))
        except Exception:
            pass
    return results


def _r0290_add_modulus_modEq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.add_modulus_modEq_iff
    # a + n ≡ b [ZMOD n] ↔ a ≡ b [ZMOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("b"), OSeq((OOp("ZMOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Int_add_modulus_modEq_iff"))
        except Exception:
            pass
    return results


def _r0291_modulus_add_modEq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.modulus_add_modEq_iff
    # n + a ≡ b [ZMOD n] ↔ a ≡ b [ZMOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("b"), OSeq((OOp("ZMOD", (args[0],)),)),))
            results.append((rhs, "Mathlib: Int_modulus_add_modEq_iff"))
        except Exception:
            pass
    return results


def _r0292_modEq_add_modulus_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.modEq_add_modulus_iff
    # a ≡ b + n [ZMOD n] ↔ a ≡ b [ZMOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("b"), OSeq((OOp("ZMOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Int_modEq_add_modulus_iff"))
        except Exception:
            pass
    return results


def _r0293_modEq_modulus_add_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.modEq_modulus_add_iff
    # a ≡ n + b [ZMOD n] ↔ a ≡ b [ZMOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("b"), OSeq((OOp("ZMOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Int_modEq_modulus_add_iff"))
        except Exception:
            pass
    return results


def _r0294_add_mul_modulus_modEq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.add_mul_modulus_modEq_iff
    # a + b * n ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("c"), OSeq((OOp("ZMOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Int_add_mul_modulus_modEq_iff"))
        except Exception:
            pass
    return results


def _r0295_mul_modulus_add_modEq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.mul_modulus_add_modEq_iff
    # b * n + a ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("c"), OSeq((OOp("ZMOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Int_mul_modulus_add_modEq_iff"))
        except Exception:
            pass
    return results


def _r0296_modEq_add_mul_modulus_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.modEq_add_mul_modulus_iff
    # a ≡ b + c * n [ZMOD n] ↔ a ≡ b [ZMOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("b"), OSeq((OOp("ZMOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Int_modEq_add_mul_modulus_iff"))
        except Exception:
            pass
    return results


def _r0297_modEq_mul_modulus_add_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.modEq_mul_modulus_add_iff
    # a ≡ b * n + c [ZMOD n] ↔ a ≡ c [ZMOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("c"), OSeq((OOp("ZMOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Int_modEq_mul_modulus_add_iff"))
        except Exception:
            pass
    return results


def _r0298_add_modulus_mul_modEq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.add_modulus_mul_modEq_iff
    # a + n * b ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("c"), OSeq((OOp("ZMOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Int_add_modulus_mul_modEq_iff"))
        except Exception:
            pass
    return results


def _r0299_modulus_mul_add_modEq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.modulus_mul_add_modEq_iff
    # n * b + a ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("c"), OSeq((OOp("ZMOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Int_modulus_mul_add_modEq_iff"))
        except Exception:
            pass
    return results


def _r0300_modEq_add_modulus_mul_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.modEq_add_modulus_mul_iff
    # a ≡ b + n * c [ZMOD n] ↔ a ≡ b [ZMOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("b"), OSeq((OOp("ZMOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Int_modEq_add_modulus_mul_iff"))
        except Exception:
            pass
    return results


def _r0301_modEq_modulus_mul_add_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.modEq_modulus_mul_add_iff
    # a ≡ n * b + c [ZMOD n] ↔ a ≡ c [ZMOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("c"), OSeq((OOp("ZMOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Int_modEq_modulus_mul_add_iff"))
        except Exception:
            pass
    return results


def _r0302_add_modEq_left_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.add_modEq_left_iff
    # a + b ≡ a [MOD n] ↔ n ∣ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("_unknown"), OVar("b"),))
            results.append((rhs, "Mathlib: Nat_add_modEq_left_iff"))
        except Exception:
            pass
    return results


def _r0303_add_modEq_right_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.add_modEq_right_iff
    # a + b ≡ b [MOD n] ↔ n ∣ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("_unknown"), args[0],))
            results.append((rhs, "Mathlib: Nat_add_modEq_right_iff"))
        except Exception:
            pass
    return results


def _r0304_left_modEq_add_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.left_modEq_add_iff
    # a ≡ a + b [MOD n] ↔ n ∣ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("_unknown"), OVar("b"),))
            results.append((rhs, "Mathlib: Nat_left_modEq_add_iff"))
        except Exception:
            pass
    return results


def _r0305_right_modEq_add_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.right_modEq_add_iff
    # b ≡ a + b [MOD n] ↔ n ∣ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("_unknown"), OVar("a"),))
            results.append((rhs, "Mathlib: Nat_right_modEq_add_iff"))
        except Exception:
            pass
    return results


def _r0306_add_modulus_modEq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.add_modulus_modEq_iff
    # a + n ≡ b [MOD n] ↔ a ≡ b [MOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("b"), OSeq((OOp("MOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Nat_add_modulus_modEq_iff"))
        except Exception:
            pass
    return results


def _r0307_modulus_add_modEq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.modulus_add_modEq_iff
    # n + a ≡ b [MOD n] ↔ a ≡ b [MOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("b"), OSeq((OOp("MOD", (args[0],)),)),))
            results.append((rhs, "Mathlib: Nat_modulus_add_modEq_iff"))
        except Exception:
            pass
    return results


def _r0308_modEq_add_modulus_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.modEq_add_modulus_iff
    # a ≡ b + n [MOD n] ↔ a ≡ b [MOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("b"), OSeq((OOp("MOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Nat_modEq_add_modulus_iff"))
        except Exception:
            pass
    return results


def _r0309_modEq_modulus_add_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.modEq_modulus_add_iff
    # a ≡ n + b [MOD n] ↔ a ≡ b [MOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("b"), OSeq((OOp("MOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Nat_modEq_modulus_add_iff"))
        except Exception:
            pass
    return results


def _r0310_add_mul_modulus_modEq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.add_mul_modulus_modEq_iff
    # a + b * n ≡ c [MOD n] ↔ a ≡ c [MOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("c"), OSeq((OOp("MOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Nat_add_mul_modulus_modEq_iff"))
        except Exception:
            pass
    return results


def _r0311_mul_modulus_add_modEq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.mul_modulus_add_modEq_iff
    # b * n + a ≡ c [MOD n] ↔ a ≡ c [MOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("c"), OSeq((OOp("MOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Nat_mul_modulus_add_modEq_iff"))
        except Exception:
            pass
    return results


def _r0312_modEq_add_mul_modulus_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.modEq_add_mul_modulus_iff
    # a ≡ b + c * n [MOD n] ↔ a ≡ b [MOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("b"), OSeq((OOp("MOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Nat_modEq_add_mul_modulus_iff"))
        except Exception:
            pass
    return results


def _r0313_modEq_mul_modulus_add_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.modEq_mul_modulus_add_iff
    # a ≡ b * n + c [MOD n] ↔ a ≡ c [MOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("c"), OSeq((OOp("MOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Nat_modEq_mul_modulus_add_iff"))
        except Exception:
            pass
    return results


def _r0314_add_modulus_mul_modEq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.add_modulus_mul_modEq_iff
    # a + n * b ≡ c [MOD n] ↔ a ≡ c [MOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("c"), OSeq((OOp("MOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Nat_add_modulus_mul_modEq_iff"))
        except Exception:
            pass
    return results


def _r0315_modulus_mul_add_modEq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.modulus_mul_add_modEq_iff
    # n * b + a ≡ c [MOD n] ↔ a ≡ c [MOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("c"), OSeq((OOp("MOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Nat_modulus_mul_add_modEq_iff"))
        except Exception:
            pass
    return results


def _r0316_modEq_add_modulus_mul_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.modEq_add_modulus_mul_iff
    # a ≡ b + n * c [MOD n] ↔ a ≡ b [MOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("b"), OSeq((OOp("MOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Nat_modEq_add_modulus_mul_iff"))
        except Exception:
            pass
    return results


def _r0317_modEq_modulus_mul_add_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.modEq_modulus_mul_add_iff
    # a ≡ n * b + c [MOD n] ↔ a ≡ c [MOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("c"), OSeq((OOp("MOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Nat_modEq_modulus_mul_add_iff"))
        except Exception:
            pass
    return results


def _r0318_divInt_le_divInt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.divInt_le_divInt
    # a /. b ≤ c /. d ↔ a * d ≤ c * b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("*", (OVar("a"), OVar("d"))), OOp("*", (OVar("c"), OVar("b")))))
            results.append((rhs, "Mathlib: Rat_divInt_le_divInt"))
        except Exception:
            pass
    return results


def _r0319_arg_le_pi_div_two_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_le_pi_div_two_iff
    # arg z ≤ π / 2 ↔ 0 ≤ re z ∨ im z < 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OLit(0), OOp("<", (OOp("or", (OOp("re", (OVar("z"),)), OOp("im", (OVar("z"),)))), OLit(0)))))
            results.append((rhs, "Mathlib: Complex_arg_le_pi_div_two_iff"))
        except Exception:
            pass
    return results


def _r0320_abs_arg_le_pi_div_two_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.abs_arg_le_pi_div_two_iff
    # |arg z| ≤ π / 2 ↔ 0 ≤ re z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OLit(0), OOp("re", (OVar("z"),))))
            results.append((rhs, "Mathlib: Complex_abs_arg_le_pi_div_two_iff"))
        except Exception:
            pass
    return results


def _r0321_exp_mem_slitPlane(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.exp_mem_slitPlane
    # exp z ∈ slitPlane ↔ toIocMod Real.two_pi_pos (-π) z.im ≠ π
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("toIocMod", (OVar("Real_two_pi_pos"), OVar("minus_pi"), OVar("z_im"),)), OVar("pi")))
            results.append((rhs, "Mathlib: Complex_exp_mem_slitPlane"))
        except Exception:
            pass
    return results


def _r0322_arccos_le_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arccos_le_pi_div_two
    # arccos x ≤ π / 2 ↔ 0 ≤ x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OLit(0), OVar("x")))
            results.append((rhs, "Mathlib: Real_arccos_le_pi_div_two"))
        except Exception:
            pass
    return results


def _r0323_natCast_modEq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.natCast_modEq_iff
    # a ≡ b [ZMOD n] ↔ a ≡ b [MOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 3)
    if args is not None:
        try:
            rhs = OOp("a", (args[0], args[1], OSeq((OOp("MOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Int_natCast_modEq_iff"))
        except Exception:
            pass
    return results


def _r0324_modEq_iff_dvd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.modEq_iff_dvd
    # a ≡ b [ZMOD n] ↔ n ∣ b - a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 3)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("n", (args[0], args[1],)), OVar("a")))
            results.append((rhs, "Mathlib: Int_modEq_iff_dvd"))
        except Exception:
            pass
    return results


def _r0325_dvd_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.ModEq.dvd_iff
    # n ∣ a ↔ n ∣ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n", 2)
    if args is not None:
        try:
            rhs = OOp("n", (args[0], OVar("b"),))
            results.append((rhs, "Mathlib: Int_ModEq_dvd_iff"))
        except Exception:
            pass
    return results


def _r0326_add_modEq_left_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.add_modEq_left_iff
    # a + b ≡ a [ZMOD n] ↔ n ∣ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("_unknown"), OVar("b"),))
            results.append((rhs, "Mathlib: Int_add_modEq_left_iff"))
        except Exception:
            pass
    return results


def _r0327_modEq_and_modEq_iff_modEq_lcm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.modEq_and_modEq_iff_modEq_lcm
    # a ≡ b [ZMOD m] ∧ a ≡ b [ZMOD n] ↔ a ≡ b [ZMOD m.lcm n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("b"), OSeq((OOp("ZMOD", (OVar("m_lcm"), OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Int_modEq_and_modEq_iff_modEq_lcm"))
        except Exception:
            pass
    return results


def _r0328_modEq_and_modEq_iff_modEq_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.modEq_and_modEq_iff_modEq_mul
    # a ≡ b [ZMOD m] ∧ a ≡ b [ZMOD n] ↔ a ≡ b [ZMOD m * n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("b"), OSeq((OOp("*", (OOp("ZMOD", (OVar("m"),)), OVar("n"))),)),))
            results.append((rhs, "Mathlib: Int_modEq_and_modEq_iff_modEq_mul"))
        except Exception:
            pass
    return results


def _r0329_le_div_two_iff_mul_two_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.le_div_two_iff_mul_two_le
    # m ≤ n / 2 ↔ (m : ℤ) * 2 ≤ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("*", (OOp("m", (OVar("colon"), OVar("_unknown"),)), OLit(2))), OVar("n")))
            results.append((rhs, "Mathlib: Nat_le_div_two_iff_mul_two_le"))
        except Exception:
            pass
    return results


def _r0330_modEq_iff_dvd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.modEq_iff_dvd
    # a ≡ b [MOD n] ↔ (n : ℤ) ∣ b - a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 3)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("n_colon", (args[0], args[1],)), OVar("a")))
            results.append((rhs, "Mathlib: Nat_modEq_iff_dvd"))
        except Exception:
            pass
    return results


def _r0331_add_iff_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.ModEq.add_iff_left
    # a + c ≡ b + d [MOD n] ↔ c ≡ d [MOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("c", (OVar("_unknown"), OVar("d"), OSeq((OOp("MOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Nat_ModEq_add_iff_left"))
        except Exception:
            pass
    return results


def _r0332_add_iff_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.ModEq.add_iff_right
    # a + c ≡ b + d [MOD n] ↔ a ≡ b [MOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("b"), OSeq((OOp("MOD", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: Nat_ModEq_add_iff_right"))
        except Exception:
            pass
    return results


def _r0333_dvd_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.ModEq.dvd_iff
    # d ∣ a ↔ d ∣ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "d", 2)
    if args is not None:
        try:
            rhs = OOp("d", (args[0], OVar("b"),))
            results.append((rhs, "Mathlib: Nat_ModEq_dvd_iff"))
        except Exception:
            pass
    return results


def _r0334_modEq_and_modEq_iff_modEq_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.modEq_and_modEq_iff_modEq_mul
    # a ≡ b [MOD m] ∧ a ≡ b [MOD n] ↔ a ≡ b [MOD m * n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("b"), OSeq((OOp("*", (OOp("MOD", (OVar("m"),)), OVar("n"))),)),))
            results.append((rhs, "Mathlib: Nat_modEq_and_modEq_iff_modEq_mul"))
        except Exception:
            pass
    return results


def _r0335_mem_properDivisors(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.mem_properDivisors
    # n ∈ properDivisors m ↔ n ∣ m ∧ n < m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("and", (OOp("n", (OVar("_unknown"), OVar("m"),)), args[0])), OVar("m")))
            results.append((rhs, "Mathlib: Nat_mem_properDivisors"))
        except Exception:
            pass
    return results


def _r0336_mem_divisors(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.mem_divisors
    # n ∈ divisors m ↔ n ∣ m ∧ m ≠ 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("and", (OOp("n", (OVar("_unknown"), OVar("m"),)), OVar("m"))), OLit(0)))
            results.append((rhs, "Mathlib: Nat_mem_divisors"))
        except Exception:
            pass
    return results


def _r0337_swap_mem_divisorsAntidiagonalList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.swap_mem_divisorsAntidiagonalList
    # a.swap ∈ n.divisorsAntidiagonalList ↔ a ∈ n.divisorsAntidiagonalList
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OVar("a"), args[1]))
            results.append((rhs, "Mathlib: Nat_swap_mem_divisorsAntidiagonalList"))
        except Exception:
            pass
    return results


def _r0338_swap_mem_divisorsAntidiagonal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.swap_mem_divisorsAntidiagonal
    # x.swap ∈ divisorsAntidiagonal n ↔ x ∈ divisorsAntidiagonal n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OVar("x"), OOp("divisorsAntidiagonal", (OVar("n"),))))
            results.append((rhs, "Mathlib: Nat_swap_mem_divisorsAntidiagonal"))
        except Exception:
            pass
    return results


def _r0339_swap_mem_divisorsAntidiag(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.swap_mem_divisorsAntidiag
    # xy.swap ∈ z.divisorsAntidiag ↔ xy ∈ z.divisorsAntidiag
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OVar("xy"), args[1]))
            results.append((rhs, "Mathlib: Int_swap_mem_divisorsAntidiag"))
        except Exception:
            pass
    return results


def _r0340_abundant_iff_sum_divisors(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.abundant_iff_sum_divisors
    # Abundant n ↔ 2 * n < ∑ i ∈ n.divisors, i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Abundant", 1)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("*", (OLit(2), args[0])), OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("n_divisors", (OVar("i"),))))))
            results.append((rhs, "Mathlib: Nat_abundant_iff_sum_divisors"))
        except Exception:
            pass
    return results


def _r0341_probablePrime_iff_modEq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.probablePrime_iff_modEq
    # ProbablePrime n b ↔ b ^ (n - 1) ≡ 1 [MOD n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ProbablePrime", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[1], OOp("n_minus_1", (OVar("_unknown"), OLit(1), OSeq((OOp("MOD", (args[0],)),)),))))
            results.append((rhs, "Mathlib: Nat_probablePrime_iff_modEq"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_nat_div rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("*", "**", "+", "-", "//", "<", "<=", "==", ">", "Abundant", "Algebra_adjoin", "Even", "Extension", "F", "GaloisConnection", "Ico", "Ico_n_n_plus_a_image", "Int_divisorsAntidiag", "Integrable", "MOD", "Module_finrank", "Module_rank", "Odd", "Perfect", "ProbablePrime", "Real_toNNReal", "Set_range", "W", "ZMOD", "ZMod", "_1", "_2_colon", "_unknown", "a", "a_choose", "a_plus_b", "adjoin", "and", "angle", "arccos", "arcsin", "arctan", "arg", "b", "betaIntegral", "bit", "bodd", "boddDiv2", "c", "choose",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_nat_div axioms."""
    if recognizes(term):
        return 0.8
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_nat_div rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_two_mul_ediv_two_of_even(term, ctx))
    results.extend(_r0001_ceilDiv_eq_add_pred_div(term, ctx))
    results.extend(_r0002_div_bot(term, ctx))
    results.extend(_r0003_natCast_eq_divInt(term, ctx))
    results.extend(_r0004_angle_div_left_eq_angle_mul_right(term, ctx))
    results.extend(_r0005_norm_div(term, ctx))
    results.extend(_r0006_tanh_eq_sinh_div_cosh(term, ctx))
    results.extend(_r0007_tan_eq_sin_div_cos(term, ctx))
    results.extend(_r0008_arg_div_self(term, ctx))
    results.extend(_r0009_log_div_self(term, ctx))
    results.extend(_r0010_two_zsmul_coe_div_two(term, ctx))
    results.extend(_r0011_toReal_eq_pi_div_two_iff(term, ctx))
    results.extend(_r0012_exp_pi_div_two_mul_I(term, ctx))
    results.extend(_r0013_pi_div_two_eq_arcsin(term, ctx))
    results.extend(_r0014_arccos_eq_pi_div_two(term, ctx))
    results.extend(_r0015_units_div_eq_mul(term, ctx))
    results.extend(_r0016_div2_two(term, ctx))
    results.extend(_r0017_div2_bit0(term, ctx))
    results.extend(_r0018_cast_div_div_div_cancel_right(term, ctx))
    results.extend(_r0019_maxPowDvdDiv_of_not_dvd(term, ctx))
    results.extend(_r0020_maxPowDvdDiv_self(term, ctx))
    results.extend(_r0021_divMaxPow_self(term, ctx))
    results.extend(_r0022_fst_maxPowDvdDiv(term, ctx))
    results.extend(_r0023_snd_maxPowDvdDiv(term, ctx))
    results.extend(_r0024_cast_div(term, ctx))
    results.extend(_r0025_cast_divInt(term, ctx))
    results.extend(_r0026_mkRat_eq_divInt(term, ctx))
    results.extend(_r0027_divInt_div_divInt(term, ctx))
    results.extend(_r0028_sqrt_div(term, ctx))
    results.extend(_r0029_coe_div(term, ctx))
    results.extend(_r0030_intDegree_div(term, ctx))
    results.extend(_r0031_relrank_top_right(term, ctx))
    results.extend(_r0032_relrank_bot_left(term, ctx))
    results.extend(_r0033_toFinset_divisorsAntidiagonalList(term, ctx))
    results.extend(_r0034_prod_divisors(term, ctx))
    results.extend(_r0035_sum_div(term, ctx))
    results.extend(_r0036_prod_intervalGapsWithin_mul_prod_eq_div(term, ctx))
    results.extend(_r0037_prod_intervalGapsWithin_eq_div_div_prod(term, ctx))
    results.extend(_r0038_prod_Ico_int_div(term, ctx))
    results.extend(_r0039_prod_range_div_prod_range(term, ctx))
    results.extend(_r0040_sum_div(term, ctx))
    results.extend(_r0041_sum_div(term, ctx))
    results.extend(_r0042_ediv_two_mul_two_of_even(term, ctx))
    results.extend(_r0043_two_mul_div_two_of_even(term, ctx))
    results.extend(_r0044_div_two_mul_two_of_even(term, ctx))
    results.extend(_r0045_piFinset_div(term, ctx))
    results.extend(_r0046_image_apply_finMulAntidiag(term, ctx))
    results.extend(_r0047_floorDiv_eq_div(term, ctx))
    results.extend(_r0048_coe_floorDiv(term, ctx))
    results.extend(_r0049_floorDiv_apply(term, ctx))
    results.extend(_r0050_mul_cast_floor_div_cancel_of_pos(term, ctx))
    results.extend(_r0051_mul_natCast_floor_div_cancel(term, ctx))
    results.extend(_r0052_cast_mul_floor_div_cancel_of_pos(term, ctx))
    results.extend(_r0053_natCast_mul_floor_div_cancel(term, ctx))
    results.extend(_r0054_floor_div_natCast(term, ctx))
    results.extend(_r0055_floor_div_ofNat(term, ctx))
    results.extend(_r0056_floor_div_eq_div(term, ctx))
    results.extend(_r0057_mul_cast_floor_div_cancel(term, ctx))
    results.extend(_r0058_cast_mul_floor_div_cancel(term, ctx))
    results.extend(_r0059_emod_abs(term, ctx))
    results.extend(_r0060_sign_eq_abs_ediv(term, ctx))
    results.extend(_r0061_bot_div(term, ctx))
    results.extend(_r0062_two_mul_ediv_two_of_odd(term, ctx))
    results.extend(_r0063_mod_two_add_add_odd_mod_two(term, ctx))
    results.extend(_r0064_even_div(term, ctx))
    results.extend(_r0065_divInt_div_divInt_cancel_left(term, ctx))
    results.extend(_r0066_divInt_div_divInt_cancel_right(term, ctx))
    results.extend(_r0067_num_div_den(term, ctx))
    results.extend(_r0068_divInt_pow(term, ctx))
    results.extend(_r0069_angle_div_right_eq_angle_mul_left(term, ctx))
    results.extend(_r0070_angle_exp_exp(term, ctx))
    results.extend(_r0071_cot_eq_cos_div_sin(term, ctx))
    results.extend(_r0072_W_eq_integral_sin_pow_div_integral_sin_p(term, ctx))
    results.extend(_r0073_arg_exp(term, ctx))
    results.extend(_r0074_arg_exp_mul_I(term, ctx))
    results.extend(_r0075_toIocMod_arg(term, ctx))
    results.extend(_r0076_arg_eq_pi_div_two_iff(term, ctx))
    results.extend(_r0077_arg_mul_cos_add_sin_mul_I_eq_toIocMod(term, ctx))
    results.extend(_r0078_arg_cos_add_sin_mul_I_eq_toIocMod(term, ctx))
    results.extend(_r0079_arg_div_coe_angle(term, ctx))
    results.extend(_r0080_log_exp_eq_re_add_toIocMod(term, ctx))
    results.extend(_r0081_rpowIntegrand_0_1_eq_pow_div(term, ctx))
    results.extend(_r0082_betaIntegral_eq_Gamma_mul_div(term, ctx))
    results.extend(_r0083_log_div_log(term, ctx))
    results.extend(_r0084_logb_div(term, ctx))
    results.extend(_r0085_logb_div_base(term, ctx))
    results.extend(_r0086_div_logb(term, ctx))
    results.extend(_r0087_log_div_self(term, ctx))
    results.extend(_r0088_log_div(term, ctx))
    results.extend(_r0089_div_rpow(term, ctx))
    results.extend(_r0090_rpow_div_two_eq_sqrt(term, ctx))
    results.extend(_r0091_two_nsmul_coe_div_two(term, ctx))
    results.extend(_r0092_sin_add_pi_div_two(term, ctx))
    results.extend(_r0093_cos_add_pi_div_two(term, ctx))
    results.extend(_r0094_coe_toIcoMod(term, ctx))
    results.extend(_r0095_coe_toIocMod(term, ctx))
    results.extend(_r0096_toReal_coe(term, ctx))
    results.extend(_r0097_toIocMod_toReal(term, ctx))
    results.extend(_r0098_toReal_pi_div_two(term, ctx))
    results.extend(_r0099_abs_toReal_eq_pi_div_two_iff(term, ctx))
    results.extend(_r0100_tan_eq_sin_div_cos(term, ctx))
    results.extend(_r0101_sign_coe_pi_div_two(term, ctx))
    results.extend(_r0102_tan_int_mul_pi_div_two(term, ctx))
    results.extend(_r0103_arctan_eq_pi_div_four(term, ctx))
    results.extend(_r0104_cos_pi_div_two(term, ctx))
    results.extend(_r0105_sin_pi_div_two(term, ctx))
    results.extend(_r0106_sin_add_pi_div_two(term, ctx))
    results.extend(_r0107_cos_add_pi_div_two(term, ctx))
    results.extend(_r0108_cos_pi_div_four(term, ctx))
    results.extend(_r0109_sin_pi_div_four(term, ctx))
    results.extend(_r0110_cos_pi_div_eight(term, ctx))
    results.extend(_r0111_sin_pi_div_eight(term, ctx))
    results.extend(_r0112_cos_pi_div_sixteen(term, ctx))
    results.extend(_r0113_sin_pi_div_sixteen(term, ctx))
    results.extend(_r0114_cos_pi_div_thirty_two(term, ctx))
    results.extend(_r0115_sin_pi_div_thirty_two(term, ctx))
    results.extend(_r0116_cos_pi_div_three(term, ctx))
    results.extend(_r0117_cos_pi_div_six(term, ctx))
    results.extend(_r0118_sq_cos_pi_div_six(term, ctx))
    results.extend(_r0119_sin_pi_div_six(term, ctx))
    results.extend(_r0120_sq_sin_pi_div_three(term, ctx))
    results.extend(_r0121_sin_pi_div_three(term, ctx))
    results.extend(_r0122_cos_pi_div_five(term, ctx))
    results.extend(_r0123_cos_pi_div_two(term, ctx))
    results.extend(_r0124_sin_pi_div_two(term, ctx))
    results.extend(_r0125_sin_add_pi_div_two(term, ctx))
    results.extend(_r0126_cos_add_pi_div_two(term, ctx))
    results.extend(_r0127_tan_int_mul_pi_div_two(term, ctx))
    results.extend(_r0128_arcsin_eq_pi_div_two(term, ctx))
    results.extend(_r0129_sum_indicator_mod(term, ctx))
    results.extend(_r0130_sumByResidueClasses(term, ctx))
    results.extend(_r0131_uniformBell_eq_div(term, ctx))
    results.extend(_r0132_even_iff_mod_of_even(term, ctx))
    results.extend(_r0133_odd_iff_mod_of_even(term, ctx))
    results.extend(_r0134_divisors_mul(term, ctx))
    results.extend(_r0135_divisors_sq(term, ctx))
    results.extend(_r0136_nat_divisors_prod(term, ctx))
    results.extend(_r0137_bodd_add_div2(term, ctx))
    results.extend(_r0138_bit_decomp(term, ctx))
    results.extend(_r0139_cast_div(term, ctx))
    results.extend(_r0140_fdiv_fdiv_eq_fdiv_mul(term, ctx))
    results.extend(_r0141_image_Ico_emod(term, ctx))
    results.extend(_r0142_eq(term, ctx))
    results.extend(_r0143_modEq_iff_add_fac(term, ctx))
    results.extend(_r0144_mod_mul_right_mod(term, ctx))
    results.extend(_r0145_mod_mul_left_mod(term, ctx))
    results.extend(_r0146_ext_ediv_modEq(term, ctx))
    results.extend(_r0147_ext_ediv_modEq_iff(term, ctx))
    results.extend(_r0148_modEq_iff_eq_of_div_eq(term, ctx))
    results.extend(_r0149_units_pow_eq_pow_mod_two(term, ctx))
    results.extend(_r0150_toNNRat_div(term, ctx))
    results.extend(_r0151_toNNReal_div(term, ctx))
    results.extend(_r0152_bit_div_two(term, ctx))
    results.extend(_r0153_bit_mod_two(term, ctx))
    results.extend(_r0154_mod_two_of_bodd(term, ctx))
    results.extend(_r0155_div2_val(term, ctx))
    results.extend(_r0156_bit_bodd_div2(term, ctx))
    results.extend(_r0157_div2_bit(term, ctx))
    results.extend(_r0158_boddDiv2_eq(term, ctx))
    results.extend(_r0159_div2_bit1(term, ctx))
    results.extend(_r0160_cast_div(term, ctx))
    results.extend(_r0161_choose_eq_factorial_div_factorial(term, ctx))
    results.extend(_r0162_choose_eq_asc_factorial_div_factorial(term, ctx))
    results.extend(_r0163_choose_eq_descFactorial_div_factorial(term, ctx))
    results.extend(_r0164_ofDigits_mod(term, ctx))
    results.extend(_r0165_ofDigits_zmod(term, ctx))
    results.extend(_r0166_factorization_div(term, ctx))
    results.extend(_r0167_ordCompl_div_pow_of_dvd(term, ctx))
    results.extend(_r0168_ordCompl_div_of_dvd(term, ctx))
    results.extend(_r0169_coe_divisors_eq_prod_pow_le_factorizatio(term, ctx))
    results.extend(_r0170_divisors_eq_image_Iic_factorization_prod(term, ctx))
    results.extend(_r0171_coe_properDivisors_eq_prod_pow_lt_factor(term, ctx))
    results.extend(_r0172_properDivisors_eq_image_Iio_factorizatio(term, ctx))
    results.extend(_r0173_div_mul_div(term, ctx))
    results.extend(_r0174_div_lcm_eq_div_gcd(term, ctx))
    results.extend(_r0175_two_mul_odd_div_two(term, ctx))
    results.extend(_r0176_log_div_base(term, ctx))
    results.extend(_r0177_log_div_base_pow(term, ctx))
    results.extend(_r0178_log_div_mul_self(term, ctx))
    results.extend(_r0179_go_spec(term, ctx))
    results.extend(_r0180_maxPowDvdDiv_base_pow_mul(term, ctx))
    results.extend(_r0181_maxPowDvdDiv_base_mul(term, ctx))
    results.extend(_r0182_divMaxPow_base_mul(term, ctx))
    results.extend(_r0183_modEq_iff_exists_eq_add(term, ctx))
    results.extend(_r0184_gcd_eq(term, ctx))
    results.extend(_r0185_eq_of_abs_lt(term, ctx))
    results.extend(_r0186_eq_of_lt_of_lt(term, ctx))
    results.extend(_r0187_add_mod_add_ite(term, ctx))
    results.extend(_r0188_add_mod_of_add_mod_lt(term, ctx))
    results.extend(_r0189_add_mod_add_of_le_add_mod(term, ctx))
    results.extend(_r0190_add_div_eq_of_add_mod_lt(term, ctx))
    results.extend(_r0191_add_div_of_dvd_right(term, ctx))
    results.extend(_r0192_add_div_of_dvd_left(term, ctx))
    results.extend(_r0193_add_div_eq_of_le_mod_add_mod(term, ctx))
    results.extend(_r0194_odd_mul_odd_div_two(term, ctx))
    results.extend(_r0195_odd_of_mod_four_eq_three(term, ctx))
    results.extend(_r0196_odd_mod_four_iff(term, ctx))
    results.extend(_r0197_mod_eq_of_modEq(term, ctx))
    results.extend(_r0198_ext_div_modEq(term, ctx))
    results.extend(_r0199_ext_div_modEq_iff(term, ctx))
    results.extend(_r0200_modEq_iff_eq_of_div_eq(term, ctx))
    results.extend(_r0201_primeFactors_div_gcd(term, ctx))
    results.extend(_r0202_totient_div_of_dvd(term, ctx))
    results.extend(_r0203_sum_totient(term, ctx))
    results.extend(_r0204_totient_eq_div_primeFactors_mul(term, ctx))
    results.extend(_r0205_prime_pow_pow_totient_ediv_prod(term, ctx))
    results.extend(_r0206_intCast_eq_divInt(term, ctx))
    results.extend(_r0207_pow_eq_divInt(term, ctx))
    results.extend(_r0208_add_divInt(term, ctx))
    results.extend(_r0209_intCast_div_eq_divInt(term, ctx))
    results.extend(_r0210_natCast_div_eq_divInt(term, ctx))
    results.extend(_r0211_divInt_mul_divInt_cancel(term, ctx))
    results.extend(_r0212_floor_intCast_div_natCast(term, ctx))
    results.extend(_r0213_ceil_intCast_div_natCast(term, ctx))
    results.extend(_r0214_floor_natCast_div_natCast(term, ctx))
    results.extend(_r0215_ceil_natCast_div_natCast(term, ctx))
    results.extend(_r0216_natFloor_natCast_div_natCast(term, ctx))
    results.extend(_r0217_mod_nat_eq_sub_mul_floor_rat_div(term, ctx))
    results.extend(_r0218_exists_eq_mul_div_num_and_eq_mul_div_den(term, ctx))
    results.extend(_r0219_ofCauchy_div(term, ctx))
    results.extend(_r0220_div_sqrt(term, ctx))
    results.extend(_r0221_sqrt_div_self(term, ctx))
    results.extend(_r0222_range_mul_add(term, ctx))
    results.extend(_r0223_finrank_zmod_extension(term, ctx))
    results.extend(_r0224_finrank_extension(term, ctx))
    results.extend(_r0225_mem_adjoin_iff_div(term, ctx))
    results.extend(_r0226_ofFractionRing_div(term, ctx))
    results.extend(_r0227_finrank_eq_max_natDegree(term, ctx))
    results.extend(_r0228_phi_natDegree(term, ctx))
    results.extend(_r0229_relrank_eq_rank_of_le(term, ctx))
    results.extend(_r0230_relrank_mul_rank_top(term, ctx))
    results.extend(_r0231_rank_bot_mul_relrank(term, ctx))
    results.extend(_r0232_rank_rat_real(term, ctx))
    results.extend(_r0233_ext(term, ctx))
    results.extend(_r0234_ext_iff(term, ctx))
    results.extend(_r0235_comp_div(term, ctx))
    results.extend(_r0236_sum_divisors(term, ctx))
    results.extend(_r0237_sum_divisors_mul(term, ctx))
    results.extend(_r0238_insert_self_properDivisors(term, ctx))
    results.extend(_r0239_cons_self_properDivisors(term, ctx))
    results.extend(_r0240_mem_divisorsAntidiagonal(term, ctx))
    results.extend(_r0241_val_divisorsAntidiagonal(term, ctx))
    results.extend(_r0242_mem_divisorsAntidiagonalList(term, ctx))
    results.extend(_r0243_sup_divisors_id(term, ctx))
    results.extend(_r0244_mem_properDivisors_iff_exists(term, ctx))
    results.extend(_r0245_prodMk_mem_divisorsAntidiag(term, ctx))
    results.extend(_r0246_image_fst_divisorsAntidiagonal(term, ctx))
    results.extend(_r0247_image_snd_divisorsAntidiagonal(term, ctx))
    results.extend(_r0248_sum_divisors_eq_sum_properDivisors_add_s(term, ctx))
    results.extend(_r0249_perfect_iff_sum_properDivisors(term, ctx))
    results.extend(_r0250_perfect_iff_sum_divisors_eq_two_mul(term, ctx))
    results.extend(_r0251_mem_divisors_prime_pow(term, ctx))
    results.extend(_r0252_divisors(term, ctx))
    results.extend(_r0253_properDivisors(term, ctx))
    results.extend(_r0254_divisors_inj(term, ctx))
    results.extend(_r0255_sum_properDivisors_dvd(term, ctx))
    results.extend(_r0256_prod_properDivisors(term, ctx))
    results.extend(_r0257_mem_properDivisors_prime_pow(term, ctx))
    results.extend(_r0258_prod_properDivisors_prime_pow(term, ctx))
    results.extend(_r0259_prod_divisors_prime_pow(term, ctx))
    results.extend(_r0260_prod_divisorsAntidiagonal(term, ctx))
    results.extend(_r0261_image_div_divisors_eq_divisors(term, ctx))
    results.extend(_r0262_prod_div_divisors(term, ctx))
    results.extend(_r0263_mem_divisorsAntidiag(term, ctx))
    results.extend(_r0264_divisorsAntidiagonal_two(term, ctx))
    results.extend(_r0265_divisorsAntidiagonal_three(term, ctx))
    results.extend(_r0266_divisorsAntidiagonal_four(term, ctx))
    results.extend(_r0267_prodMk_mem_divisorsAntidiag(term, ctx))
    results.extend(_r0268_forall_exists_prime_gt_and_eq_mod(term, ctx))
    results.extend(_r0269_finrank(term, ctx))
    results.extend(_r0270_galEquivZMod_apply_of_pow_eq(term, ctx))
    results.extend(_r0271_galEquivZMod_smul_of_pow_eq(term, ctx))
    results.extend(_r0272_pow_add_totient_mod_eq(term, ctx))
    results.extend(_r0273_pow_add_mul_totient_mod_eq(term, ctx))
    results.extend(_r0274_pow_totient_mod(term, ctx))
    results.extend(_r0275_eq_sq_add_sq_iff_eq_sq_mul(term, ctx))
    results.extend(_r0276_frequently_mod_eq(term, ctx))
    results.extend(_r0277_galoisConnection_mul_div(term, ctx))
    results.extend(_r0278_cast_choose_eq_ascPochhammer_div(term, ctx))
    results.extend(_r0279_div_lt_div_iff_mul_lt_mul(term, ctx))
    results.extend(_r0280_arcsin_lt_pi_div_two(term, ctx))
    results.extend(_r0281_pi_div_two_le_arcsin(term, ctx))
    results.extend(_r0282_pi_div_four_le_arcsin(term, ctx))
    results.extend(_r0283_arccos_lt_pi_div_two(term, ctx))
    results.extend(_r0284_arccos_le_pi_div_four(term, ctx))
    results.extend(_r0285_modEq_abs(term, ctx))
    results.extend(_r0286_modEq_natAbs(term, ctx))
    results.extend(_r0287_add_modEq_right_iff(term, ctx))
    results.extend(_r0288_left_modEq_add_iff(term, ctx))
    results.extend(_r0289_right_modEq_add_iff(term, ctx))
    results.extend(_r0290_add_modulus_modEq_iff(term, ctx))
    results.extend(_r0291_modulus_add_modEq_iff(term, ctx))
    results.extend(_r0292_modEq_add_modulus_iff(term, ctx))
    results.extend(_r0293_modEq_modulus_add_iff(term, ctx))
    results.extend(_r0294_add_mul_modulus_modEq_iff(term, ctx))
    results.extend(_r0295_mul_modulus_add_modEq_iff(term, ctx))
    results.extend(_r0296_modEq_add_mul_modulus_iff(term, ctx))
    results.extend(_r0297_modEq_mul_modulus_add_iff(term, ctx))
    results.extend(_r0298_add_modulus_mul_modEq_iff(term, ctx))
    results.extend(_r0299_modulus_mul_add_modEq_iff(term, ctx))
    results.extend(_r0300_modEq_add_modulus_mul_iff(term, ctx))
    results.extend(_r0301_modEq_modulus_mul_add_iff(term, ctx))
    results.extend(_r0302_add_modEq_left_iff(term, ctx))
    results.extend(_r0303_add_modEq_right_iff(term, ctx))
    results.extend(_r0304_left_modEq_add_iff(term, ctx))
    results.extend(_r0305_right_modEq_add_iff(term, ctx))
    results.extend(_r0306_add_modulus_modEq_iff(term, ctx))
    results.extend(_r0307_modulus_add_modEq_iff(term, ctx))
    results.extend(_r0308_modEq_add_modulus_iff(term, ctx))
    results.extend(_r0309_modEq_modulus_add_iff(term, ctx))
    results.extend(_r0310_add_mul_modulus_modEq_iff(term, ctx))
    results.extend(_r0311_mul_modulus_add_modEq_iff(term, ctx))
    results.extend(_r0312_modEq_add_mul_modulus_iff(term, ctx))
    results.extend(_r0313_modEq_mul_modulus_add_iff(term, ctx))
    results.extend(_r0314_add_modulus_mul_modEq_iff(term, ctx))
    results.extend(_r0315_modulus_mul_add_modEq_iff(term, ctx))
    results.extend(_r0316_modEq_add_modulus_mul_iff(term, ctx))
    results.extend(_r0317_modEq_modulus_mul_add_iff(term, ctx))
    results.extend(_r0318_divInt_le_divInt(term, ctx))
    results.extend(_r0319_arg_le_pi_div_two_iff(term, ctx))
    results.extend(_r0320_abs_arg_le_pi_div_two_iff(term, ctx))
    results.extend(_r0321_exp_mem_slitPlane(term, ctx))
    results.extend(_r0322_arccos_le_pi_div_two(term, ctx))
    results.extend(_r0323_natCast_modEq_iff(term, ctx))
    results.extend(_r0324_modEq_iff_dvd(term, ctx))
    results.extend(_r0325_dvd_iff(term, ctx))
    results.extend(_r0326_add_modEq_left_iff(term, ctx))
    results.extend(_r0327_modEq_and_modEq_iff_modEq_lcm(term, ctx))
    results.extend(_r0328_modEq_and_modEq_iff_modEq_mul(term, ctx))
    results.extend(_r0329_le_div_two_iff_mul_two_le(term, ctx))
    results.extend(_r0330_modEq_iff_dvd(term, ctx))
    results.extend(_r0331_add_iff_left(term, ctx))
    results.extend(_r0332_add_iff_right(term, ctx))
    results.extend(_r0333_dvd_iff(term, ctx))
    results.extend(_r0334_modEq_and_modEq_iff_modEq_mul(term, ctx))
    results.extend(_r0335_mem_properDivisors(term, ctx))
    results.extend(_r0336_mem_divisors(term, ctx))
    results.extend(_r0337_swap_mem_divisorsAntidiagonalList(term, ctx))
    results.extend(_r0338_swap_mem_divisorsAntidiagonal(term, ctx))
    results.extend(_r0339_swap_mem_divisorsAntidiag(term, ctx))
    results.extend(_r0340_abundant_iff_sum_divisors(term, ctx))
    results.extend(_r0341_probablePrime_iff_modEq(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_nat_div rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("Nat_ModEq_prod", "x_in_s_f_x_x_in_s_g_x_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_sum", "x_in_s_f_x_x_in_s_g_x_MOD_n", "Not an equality or iff proposition"),
    ("Nat_prod_modEq_ite", "x_in_s_f_x_if_a_in_s_then_f_a_else_1_MOD_n", "Not an equality or iff proposition"),
    ("Nat_prod_modEq_single", "x_in_s_f_x_f_a_MOD_n", "Not an equality or iff proposition"),
    ("Nat_sum_modEq_ite", "x_in_s_f_x_if_a_in_s_then_f_a_else_0_MOD_n", "Not an equality or iff proposition"),
    ("Nat_sum_modEq_single", "x_in_s_f_x_f_a_MOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_prod", "x_in_s_f_x_x_in_s_g_x_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_sum", "x_in_s_f_x_x_in_s_g_x_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_prod_modEq_ite", "x_in_s_f_x_if_a_in_s_then_f_a_else_1_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_prod_modEq_single", "x_in_s_f_x_f_a_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_sum_modEq_ite", "x_in_s_f_x_if_a_in_s_then_f_a_else_0_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_sum_modEq_single", "x_in_s_f_x_f_a_ZMOD_n", "Not an equality or iff proposition"),
    ("Finite_div", "s_Finite_to_t_Finite_to_s_slash_t_Finite", "Not an equality or iff proposition"),
    ("Int_emod_lt_abs", "a_b_lt_pipe_bpipe", "Not an equality or iff proposition"),
    ("Int_abs_ediv_le_abs", "forall_a_b_colon_pipe_a_slash_bpipe_le_pipe_apipe", "Not an equality or iff proposition"),
    ("Int_sign_eq_ediv_abs", "_unknown", "Empty proposition"),
    ("Real_pow_div_factorial_le_exp", "x_pow_n_slash_n_bang_le_exp_x", "Not an equality or iff proposition"),
    ("Real_not_summable_indicator_one_div_natCast", "not_Summable_n_colon_pipe_n_colon_ZMod_m_eq_k_indicator_fun_n_colon_1_slash_n_colon", "Not an equality or iff proposition"),
    ("Real_tendsto_sum_pi_div_four", "Tendsto_fun_k_eq_gt_i_in_range_k_minus_1_colon_pow_i_slash_2_star_i_plus_1_atTop_pi_slash_4", "Not an equality or iff proposition"),
    ("Real_Wallis_tendsto_W_nhds_pi_div_two", "Tendsto_W_atTop_lt_pipe_pi_slash_2", "Not an equality or iff proposition"),
    ("Real_tendsto_prod_pi_div_two", "Tendsto_fun_k_eq_gt_i_in_range_k_2_colon_star_i_plus_2_slash_2_star_i_plus_1_star_2_star_i_plus_2", "Not an equality or iff proposition"),
    ("Real_rpowIntegrand_0_1_eqOn_pow_div", "Set_EqOn_rpowIntegrand_0_1_p_x_fun_t_eq_gt_t_pow_p_minus_1_star_x_slash_t_plus_x_Ioi_0", "Not an equality or iff proposition"),
    ("Real_tendsto_exp_div_pow_atTop", "Tendsto_fun_x_eq_gt_exp_x_slash_x_pow_n_atTop_atTop", "Not an equality or iff proposition"),
    ("Real_tendsto_mul_exp_add_div_pow_atTop", "Tendsto_fun_x_eq_gt_b_star_exp_x_plus_c_slash_x_pow_n_atTop_atTop", "Not an equality or iff proposition"),
    ("Real_tendsto_div_pow_mul_exp_add_atTop", "Tendsto_fun_x_eq_gt_x_pow_n_slash_b_star_exp_x_plus_c_atTop_0", "Not an equality or iff proposition"),
    ("Real_tendsto_pow_log_div_mul_add_atTop", "Tendsto_fun_x_eq_gt_log_x_pow_n_slash_a_star_x_plus_b_atTop_0", "Not an equality or iff proposition"),
    ("Real_log_le_rpow_div", "log_x_le_x_pow_e_slash_e", "Not an equality or iff proposition"),
    ("Real_log_natCast_le_rpow_div", "log_n_le_n_pow_e_slash_e", "Not an equality or iff proposition"),
    ("Complex_norm_log_natCast_le_rpow_div", "log_n_le_n_pow_e_slash_e", "Not an equality or iff proposition"),
    ("Real_arctan_lt_pi_div_two", "arctan_x_lt_pi_slash_2", "Not an equality or iff proposition"),
    ("Real_arctan_ne_mul_pi_div_two", "forall_k_colon_arctan_x_ne_2_star_k_plus_1_star_pi_slash_2", "Not an equality or iff proposition"),
    ("Real_arctan_add_arctan_lt_pi_div_two", "arctan_x_plus_arctan_y_lt_pi_slash_2", "Not an equality or iff proposition"),
    ("Real_pi_div_two_le_two", "pi_slash_2_le_2", "Not an equality or iff proposition"),
    ("Real_pi_div_two_pos", "_0_lt_pi_slash_2", "Not an equality or iff proposition"),
    ("Real_cos_nonpos_of_pi_div_two_le_of_le", "cos_x_le_0", "Not an equality or iff proposition"),
    ("Real_sin_le_sin_of_le_of_le_pi_div_two", "sin_x_le_sin_y", "Not an equality or iff proposition"),
    ("Real_quadratic_root_cos_pi_div_five", "letI_c", "Not an equality or iff proposition"),
    ("Real_Polynomial_isRoot_cos_pi_div_five", "_4_X_pow_2_minus_2_X_minus_C_1_colon_X_IsRoot_cos_pi_slash_5", "Not an equality or iff proposition"),
    ("Real_arcsin_le_pi_div_two", "arcsin_x_le_pi_slash_2", "Not an equality or iff proposition"),
    ("Finset_prod_div_prod_mem_mulSpan", "a_in_t_a_slash_a_in_u_a_in_mulSpan_s", "Not an equality or iff proposition"),
    ("Finset_ruzsa_triangle_inequality_div_div_div", "hash_A_slash_C_star_hash_B_le_hash_A_slash_B_star_hash_C_slash_B", "Not an equality or iff proposition"),
    ("Finset_ruzsa_triangle_inequality_div_mul_mul", "hash_A_slash_C_star_hash_B_le_hash_A_star_B_star_hash_C_star_B", "Not an equality or iff proposition"),
    ("Finset_ruzsa_triangle_inequality_mul_div_mul", "hash_B_star_hash_A_star_C_le_hash_B_slash_A_star_hash_B_star_C", "Not an equality or iff proposition"),
    ("Nat_exists_lt_modEq_of_infinite", "exists_m_in_s_exists_n_in_s_m_lt_n_and_m_n_MOD_k", "Not an equality or iff proposition"),
    ("Int_ModEq_refl", "a_a_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_rfl", "a_a_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_symm", "a_b_ZMOD_n_to_b_a_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_trans", "a_b_ZMOD_n_to_b_c_ZMOD_n_to_a_c_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_mod_modEq", "a_n_a_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_of_dvd", "a_b_ZMOD_m", "Not an equality or iff proposition"),
    ("Int_ModEq_mul_left", "_unknown", "Empty proposition"),
    ("Int_ModEq_mul_right", "_unknown", "Empty proposition"),
    ("Int_ModEq_add", "a_plus_c_b_plus_d_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_add_left", "c_plus_a_c_plus_b_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_add_right", "a_plus_c_b_plus_c_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_add_left_cancel", "c_d_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_add_left_cancel", "_unknown", "Empty proposition"),
    ("Int_ModEq_add_right_cancel", "a_b_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_add_right_cancel", "_unknown", "Empty proposition"),
    ("Int_ModEq_mul_left", "c_star_a_c_star_b_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_mul_right", "a_star_c_b_star_c_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_mul", "a_star_c_b_star_d_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_pow", "a_pow_m_b_pow_m_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_of_mul_left", "a_b_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_of_mul_right", "a_b_ZMOD_n_star_m_to_a_b_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_cancel_right_div_gcd", "a_b_ZMOD_m_slash_gcd_m_c", "Not an equality or iff proposition"),
    ("Int_ModEq_cancel_left_div_gcd", "a_b_ZMOD_m_slash_gcd_m_c", "Not an equality or iff proposition"),
    ("Int_ModEq_of_div", "a_b_ZMOD_m", "Not an equality or iff proposition"),
    ("Int_ModEq_mul_left_cancel", "_unknown", "Empty proposition"),
    ("Int_ModEq_mul_left_cancel_iff", "_unknown", "Empty proposition"),
    ("Int_ModEq_mul_right_cancel", "_unknown", "Empty proposition"),
    ("Int_ModEq_mul_right_cancel_iff", "_unknown", "Empty proposition"),
    ("Int_add_modEq_left", "n_plus_a_a_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_add_modEq_right", "a_plus_n_a_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_gcd_a_modEq", "a_colon_star_Nat_gcdA_a_b_Nat_gcd_a_b_ZMOD_b", "Not an equality or iff proposition"),
    ("Int_modEq_add_fac", "a_plus_n_star_c_b_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_modEq_add_fac_self", "a_plus_n_star_t_a_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_mod_coprime", "exists_y_colon_a_star_y_1_ZMOD_b", "Not an equality or iff proposition"),
    ("Rat_toNNRat_div", "_unknown", "Empty proposition"),
    ("Real_toNNReal_div", "_unknown", "Empty proposition"),
    ("Nat_binaryRec_decreasing", "div2_n_lt_n", "Not an equality or iff proposition"),
    ("Nat_cast_div_le", "m_slash_n_colon_colon_a_le_m_slash_n", "Not an equality or iff proposition"),
    ("Nat_choose_eq_asc_factorial_div_factorial", "_unknown", "Empty proposition"),
    ("Nat_choose_le_pow_div", "n_choose_r_colon_a_le_n_pow_r_colon_a_slash_r_bang", "Not an equality or iff proposition"),
    ("Nat_choose_lt_pow_div", "n_choose_k_colon_a_lt_n_pow_k_colon_a_slash_k_bang", "Not an equality or iff proposition"),
    ("Nat_modEq_three_digits_sum", "n_digits_10_n_sum_MOD_3", "Not an equality or iff proposition"),
    ("Nat_modEq_nine_digits_sum", "n_digits_10_n_sum_MOD_9", "Not an equality or iff proposition"),
    ("Nat_ofDigits_modEq", "_unknown", "Empty proposition"),
    ("Nat_ofDigits_modEq", "ofDigits_b_L_ofDigits_b_k_L_MOD_k", "Not an equality or iff proposition"),
    ("Nat_ofDigits_zmodeq", "_unknown", "Empty proposition"),
    ("Nat_ofDigits_zmodeq", "ofDigits_b_L_ofDigits_b_k_L_ZMOD_k", "Not an equality or iff proposition"),
    ("Nat_modEq_digits_sum", "n_digits_b_prime_n_sum_MOD_b", "Not an equality or iff proposition"),
    ("Nat_zmodeq_ofDigits_digits", "n_ofDigits_c_digits_b_prime_n_ZMOD_b", "Not an equality or iff proposition"),
    ("Nat_div_dvd_div_left", "k_slash_m_k_slash_n", "Not an equality or iff proposition"),
    ("Nat_div_lt_self", "_unknown", "Empty proposition"),
    ("Nat_not_dvd_divMaxPow", "not_p_divMaxPow_n_p", "Not an equality or iff proposition"),
    ("Nat_ModEq_refl", "a_a_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_rfl", "a_a_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_symm", "a_b_MOD_n_to_b_a_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_trans", "a_b_MOD_n_to_b_c_MOD_n_to_a_c_MOD_n", "Not an equality or iff proposition"),
    ("Nat_modEq_iff_dvd", "_unknown", "Empty proposition"),
    ("Nat_mod_modEq", "a_n_a_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_modulus_mul_add", "m_star_a_plus_b_b_MOD_m", "Not an equality or iff proposition"),
    ("Nat_ModEq_of_dvd", "a_b_MOD_m", "Not an equality or iff proposition"),
    ("Nat_ModEq_mul_left", "_unknown", "Empty proposition"),
    ("Nat_ModEq_mul_left", "c_star_a_c_star_b_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_mul_right", "_unknown", "Empty proposition"),
    ("Nat_ModEq_mul_right", "a_star_c_b_star_c_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_mul", "a_star_c_b_star_d_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_pow", "a_pow_m_b_pow_m_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_add", "a_plus_c_b_plus_d_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_add_left", "c_plus_a_c_plus_b_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_add_right", "a_plus_c_b_plus_c_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_add_left_cancel", "c_d_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_add_left_cancel", "_unknown", "Empty proposition"),
    ("Nat_ModEq_add_right_cancel", "a_b_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_add_right_cancel", "_unknown", "Empty proposition"),
    ("Nat_ModEq_mul_left_cancel", "_unknown", "Empty proposition"),
    ("Nat_ModEq_mul_left_cancel_iff", "_unknown", "Empty proposition"),
    ("Nat_ModEq_mul_right_cancel", "_unknown", "Empty proposition"),
    ("Nat_ModEq_mul_right_cancel_iff", "_unknown", "Empty proposition"),
    ("Nat_ModEq_of_mul_left", "a_b_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_of_mul_right", "a_b_MOD_n_star_m_to_a_b_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_of_div", "a_b_MOD_m", "Not an equality or iff proposition"),
    ("Nat_add_modEq_left", "n_plus_a_a_MOD_n", "Not an equality or iff proposition"),
    ("Nat_add_modEq_right", "a_plus_n_a_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_cancel_left_div_gcd", "a_b_MOD_m_slash_gcd_m_c", "Not an equality or iff proposition"),
    ("Nat_ModEq_cancel_right_div_gcd", "a_b_MOD_m_slash_gcd_m_c", "Not an equality or iff proposition"),
    ("Nat_ModEq_cancel_left_div_gcd", "_unknown", "Empty proposition"),
    ("Nat_ModEq_cancel_right_div_gcd", "_unknown", "Empty proposition"),
    ("Nat_ModEq_cancel_left_of_coprime", "a_b_MOD_m", "Not an equality or iff proposition"),
    ("Nat_ModEq_cancel_right_of_coprime", "a_b_MOD_m", "Not an equality or iff proposition"),
    ("Nat_mod_lcm", "a_b_MOD_lcm_n_m", "Not an equality or iff proposition"),
    ("Nat_chineseRemainder_modEq_unique", "z_chineseRemainder_co_a_b_MOD_n_star_m", "Not an equality or iff proposition"),
    ("Nat_add_div_le_add_div", "a_slash_c_plus_b_slash_c_le_a_plus_b_slash_c", "Not an equality or iff proposition"),
    ("Nat_le_mod_add_mod_of_dvd_add_of_not_dvd", "c_le_a_c_plus_b_c", "Not an equality or iff proposition"),
    ("Nat_periodic_mod", "Periodic_fun_n_eq_gt_n_a_a", "Not an equality or iff proposition"),
    ("Nat_minFac_le_div", "minFac_n_le_n_slash_minFac_n", "Not an equality or iff proposition"),
    ("Nat_coprime_div_gcd_of_squarefree", "Coprime_m_slash_gcd_m_n_n", "Not an equality or iff proposition"),
    ("Nat_card_units_zmod_lt_sub_one", "Fintype_card_ZMod_p_le_p_minus_1", "Not an equality or iff proposition"),
    ("Nat_prod_primeFactors_pow_totient_ediv_dvd", "p_in_n_primeFactors_p_pow_phi_n_slash_p_minus_1_n_pow_phi_n", "Not an equality or iff proposition"),
    ("Rat_div_def", "_unknown", "Empty proposition"),
    ("Real_HolderTriple_holderConjugate_div_div", "p_slash_r_HolderConjugate_q_slash_r", "Not an equality or iff proposition"),
    ("Real_sqrt_div", "_unknown", "Empty proposition"),
    ("Real_sqrt_div_self", "_unknown", "Empty proposition"),
    ("Int_quotientSpanNatEquivZMod_comp_Quotient_mk", "Int_quotientSpanNatEquivZMod_n_colon_to_plus_star_comp_Ideal_Quotient_mk_Ideal_span", "Not an equality or iff proposition"),
    ("Int_quotientSpanNatEquivZMod_comp_castRingHom", "Int_quotientSpanNatEquivZMod_n_symm_colon_to_plus_star_comp_Int_castRingHom_ZMod_n", "Not an equality or iff proposition"),
    ("Int_quotientSpanEquivZMod_comp_Quotient_mk", "Int_quotientSpanEquivZMod_n_colon_to_plus_star_comp_Ideal_Quotient_mk_Ideal_span_n", "Not an equality or iff proposition"),
    ("Int_quotientSpanEquivZMod_comp_castRingHom", "Int_quotientSpanEquivZMod_n_symm_colon_to_plus_star_comp_Int_castRingHom_ZMod_n_nat", "Not an equality or iff proposition"),
    ("Nat_sq_add_sq_zmodEq", "exists_a_b_colon_a_le_p_slash_2_and_b_le_p_slash_2_and_a_colon_pow_2_plus_b_colon_pow_2_x_ZMOD_p", "Not an equality or iff proposition"),
    ("Nat_sq_add_sq_modEq", "exists_a_b_colon_a_le_p_slash_2_and_b_le_p_slash_2_and_a_pow_2_plus_b_pow_2_x_MOD_p", "Not an equality or iff proposition"),
    ("Nat_ModEq_pow_totient", "x_pow_phi_n_1_MOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_pow_prime_eq_self", "n_pow_p_n_ZMOD_p", "Not an equality or iff proposition"),
    ("Int_ModEq_pow_eq_pow", "n_pow_x_n_pow_y_ZMOD_p", "Not an equality or iff proposition"),
    ("FiniteField_trace_to_zmod_nondegenerate", "exists_b_colon_F_Algebra_trace_ZMod_ringChar_F_F_a_star_b_ne_0", "Not an equality or iff proposition"),
    ("IntermediateField_div_mem", "x_in_S_to_y_in_S_to_x_slash_y_in_S", "Not an equality or iff proposition"),
    ("RatFunc_mk_eq_div", "_unknown", "Empty proposition"),
    ("IntermediateField_relrank_dvd_rank_top_of_le", "relrank_A_B_Module_rank_A_E", "Not an equality or iff proposition"),
    ("IntermediateField_relrank_dvd_rank_bot", "relrank_A_B_Module_rank_F_B", "Not an equality or iff proposition"),
    ("Module_Basis_finiteDimensional_of_finite", "FiniteDimensional_K_V", "Not an equality or iff proposition"),
    ("Integrable_comp_div_right", "Integrable_fun_t_eq_gt_f_t_slash_g_mu", "Not an equality or iff proposition"),
    ("Integrable_comp_div_left", "Integrable_fun_t_eq_gt_f_g_slash_t_mu", "Not an equality or iff proposition"),
    ("Nat_dvd_of_mem_divisors", "n_m", "Not an equality or iff proposition"),
    ("Nat_mem_divisors_self", "n_in_n_divisors", "Not an equality or iff proposition"),
    ("Nat_pairwise_divisorsAntidiagonalList_fst", "n_divisorsAntidiagonalList_Pairwise_fst_lt_fst", "Not an equality or iff proposition"),
    ("Nat_pairwise_divisorsAntidiagonalList_snd", "n_divisorsAntidiagonalList_Pairwise_snd_gt_snd", "Not an equality or iff proposition"),
    ("Nat_nodup_divisorsAntidiagonalList", "n_divisorsAntidiagonalList_Nodup", "Not an equality or iff proposition"),
    ("Nat_divisor_le", "n_in_divisors_m_to_n_le_m", "Not an equality or iff proposition"),
    ("Nat_divisors_subset_properDivisors", "divisors_m_sub_properDivisors_n", "Not an equality or iff proposition"),
    ("Nat_properDivisors_subset_divisors", "properDivisors_n_sub_divisors_n", "Not an equality or iff proposition"),
    ("Nat_pos_of_mem_divisors", "_0_lt_m", "Not an equality or iff proposition"),
    ("Nat_pos_of_mem_properDivisors", "_0_lt_m", "Not an equality or iff proposition"),
    ("Nat_one_lt_div_of_mem_properDivisors", "_1_lt_n_slash_m", "Not an equality or iff proposition"),
    ("Nat_fst_mem_divisors_of_mem_antidiagonal", "x_fst_in_divisors_n", "Not an equality or iff proposition"),
    ("Nat_snd_mem_divisors_of_mem_antidiagonal", "x_snd_in_divisors_n", "Not an equality or iff proposition"),
    ("Nat_prod_divisorsAntidiagonal", "_unknown", "Empty proposition"),
    ("Nat_infinite_setOf_prime_and_eq_mod", "p_colon_pipe_p_Prime_and_p_colon_ZMod_q_eq_a_Infinite", "Not an equality or iff proposition"),
    ("Nat_frequently_atTop_prime_and_modEq", "exists_p_in_atTop_p_Prime_and_p_a_MOD_q", "Not an equality or iff proposition"),
    ("IsCyclotomicExtension_Rat_nrComplexPlaces_eq_totient_div_two", "haveI", "Not an equality or iff proposition"),
    ("Int_sq_ne_two_mod_four", "z_star_z_4_ne_2", "Not an equality or iff proposition"),
    ("Nat_frequently_modEq", "exists_m_in_atTop_m_d_MOD_n", "Not an equality or iff proposition"),
    ("IntermediateField_rank_sup_le", "Module_rank_F_A_B_le_Module_rank_F_A_star_Module_rank_F_B", "Not an equality or iff proposition"),
]
