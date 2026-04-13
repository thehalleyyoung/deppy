"""Mathlib: Nat Order — auto-generated from Mathlib4.

Contains 400 rewrite rules derived from Mathlib theorems.
Plus 961 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_nat_order"
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

def _r0000_prod_univ_fun_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.prod_univ_fun_getElem
    # ∏ i : Fin l.length, f l[i.1] = (l.map f).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 6)
    if args is not None:
        try:
            rhs = OVar("l_map_f_prod")
            results.append((rhs, "Mathlib: Fin_prod_univ_fun_getElem"))
        except Exception:
            pass
    return results


def _r0001_coe_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.coe_sum
    # ⇑(f.sum g) = f.sum fun a₁ b => ⇑(g a₁ b)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_sum_g")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_sum", (OVar("fun"), OVar("a_1"), OVar("b"), OVar("eq_gt"), OVar("g_a_1_b"),))
            results.append((rhs, "Mathlib: Finsupp_coe_sum"))
    except Exception:
        pass
    return results


def _r0002_sum_multiset_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.sum_multiset_singleton
    # ∑ a ∈ s, {a} = s.val
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OVar("s_val")
            results.append((rhs, "Mathlib: Finset_sum_multiset_singleton"))
        except Exception:
            pass
    return results


def _r0003_toFreeAbelianGroup_single(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.toFreeAbelianGroup_single
    # toFreeAbelianGroup (single x n) = n • .of x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFreeAbelianGroup", 1)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("_unknown"), OVar("of"), OVar("x"),))
            results.append((rhs, "Mathlib: Finsupp_toFreeAbelianGroup_single"))
        except Exception:
            pass
    return results


def _r0004_e_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ComplexShape.ε_succ
    # c.ε q = - c.ε p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_e", 1)
    if args is not None:
        try:
            rhs = OOp("minus", (OVar("c_e"), OVar("p"),))
            results.append((rhs, "Mathlib: ComplexShape_e_succ"))
        except Exception:
            pass
    return results


def _r0005_length_add_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Interval.length_add_le
    # ∀ s t : Interval α, (s + t).length ≤ s.length + t.length   | ⊥, _ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: Interval_length_add_le"))
        except Exception:
            pass
    return results


def _r0006_image_add_left_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.image_add_left_Ico
    # (Ico a b).image (c + ·) = Ico (c + a) (c + b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico_a_b_image", 1)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("+", (OVar("c"), OVar("a"))), OOp("+", (OVar("c"), OVar("b"))),))
            results.append((rhs, "Mathlib: Finset_image_add_left_Ico"))
        except Exception:
            pass
    return results


def _r0007_image_add_left_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.image_add_left_Ioc
    # (Ioc a b).image (c + ·) = Ioc (c + a) (c + b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioc_a_b_image", 1)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("+", (OVar("c"), OVar("a"))), OOp("+", (OVar("c"), OVar("b"))),))
            results.append((rhs, "Mathlib: Finset_image_add_left_Ioc"))
        except Exception:
            pass
    return results


def _r0008_image_add_left_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.image_add_left_Ioo
    # (Ioo a b).image (c + ·) = Ioo (c + a) (c + b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioo_a_b_image", 1)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OOp("+", (OVar("c"), OVar("a"))), OOp("+", (OVar("c"), OVar("b"))),))
            results.append((rhs, "Mathlib: Finset_image_add_left_Ioo"))
        except Exception:
            pass
    return results


def _r0009_image_add_right_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.image_add_right_Icc
    # (Icc a b).image (· + c) = Icc (a + c) (b + c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Icc_a_b_image", 1)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("+", (OVar("a"), OVar("c"))), OOp("+", (OVar("b"), OVar("c"))),))
            results.append((rhs, "Mathlib: Finset_image_add_right_Icc"))
        except Exception:
            pass
    return results


def _r0010_image_add_right_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.image_add_right_Ico
    # (Ico a b).image (· + c) = Ico (a + c) (b + c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico_a_b_image", 1)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("+", (OVar("a"), OVar("c"))), OOp("+", (OVar("b"), OVar("c"))),))
            results.append((rhs, "Mathlib: Finset_image_add_right_Ico"))
        except Exception:
            pass
    return results


def _r0011_image_add_right_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.image_add_right_Ioc
    # (Ioc a b).image (· + c) = Ioc (a + c) (b + c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioc_a_b_image", 1)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("+", (OVar("a"), OVar("c"))), OOp("+", (OVar("b"), OVar("c"))),))
            results.append((rhs, "Mathlib: Finset_image_add_right_Ioc"))
        except Exception:
            pass
    return results


def _r0012_image_add_right_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.image_add_right_Ioo
    # (Ioo a b).image (· + c) = Ioo (a + c) (b + c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioo_a_b_image", 1)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OOp("+", (OVar("a"), OVar("c"))), OOp("+", (OVar("b"), OVar("c"))),))
            results.append((rhs, "Mathlib: Finset_image_add_right_Ioo"))
        except Exception:
            pass
    return results


def _r0013_cast_finsetSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.cast_finsetSup
    # (↑(s.sup f) : R) = s.sup fun i ↦ (f i : R)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_sup_f", 2)
    if args is not None:
        try:
            rhs = OOp("s_sup", (OVar("fun"), OVar("i"), OVar("_unknown"), OOp("f", (OVar("i"), args[0], args[1],)),))
            results.append((rhs, "Mathlib: Nat_cast_finsetSup"))
        except Exception:
            pass
    return results


def _r0014_val_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.FiniteElement.val_add
    # (x + y).1 = x.1 + y.1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_plus_y_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("x_1"), OVar("y_1")))
            results.append((rhs, "Mathlib: ArchimedeanClass_FiniteElement_val_add"))
    except Exception:
        pass
    return results


def _r0015_val_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.FiniteElement.val_mul
    # (x * y).1 = x.1 * y.1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_star_y_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("x_1"), OVar("y_1")))
            results.append((rhs, "Mathlib: ArchimedeanClass_FiniteElement_val_mul"))
    except Exception:
        pass
    return results


def _r0016_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.FiniteElement.ext
    # x = y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("y")
            results.append((rhs, "Mathlib: ArchimedeanClass_FiniteElement_ext"))
    except Exception:
        pass
    return results


def _r0017_succ_mod_two_add_mod_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.succ_mod_two_add_mod_two
    # (m + 1) % 2 + m % 2 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Nat_succ_mod_two_add_mod_two"))
        except Exception:
            pass
    return results


def _r0018_expNear_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.expNear_succ
    # expNear (n + 1) x r = expNear n x (1 + x / (n + 1) * r)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "expNear", 3)
    if args is not None:
        try:
            rhs = OOp("expNear", (OVar("n"), args[1], OOp("+", (OLit(1), OOp("*", (OOp("//", (args[1], OOp("+", (OVar("n"), OLit(1))))), args[2])))),))
            results.append((rhs, "Mathlib: Real_expNear_succ"))
        except Exception:
            pass
    return results


def _r0019_range_normSq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.range_normSq
    # range normSq = Ici 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OOp("Ici", (OLit(0),))
            results.append((rhs, "Mathlib: Complex_range_normSq"))
        except Exception:
            pass
    return results


def _r0020_closure_setOf_re_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.closure_setOf_re_lt
    # closure { z : ℂ | z.re < a } = { z | z.re ≤ a }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OVar("z_pipe_z_re_le_a")
            results.append((rhs, "Mathlib: Complex_closure_setOf_re_lt"))
        except Exception:
            pass
    return results


def _r0021_closure_setOf_im_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.closure_setOf_im_lt
    # closure { z : ℂ | z.im < a } = { z | z.im ≤ a }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OVar("z_pipe_z_im_le_a")
            results.append((rhs, "Mathlib: Complex_closure_setOf_im_lt"))
        except Exception:
            pass
    return results


def _r0022_closure_setOf_lt_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.closure_setOf_lt_re
    # closure { z : ℂ | a < z.re } = { z | a ≤ z.re }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OVar("z_pipe_a_le_z_re")
            results.append((rhs, "Mathlib: Complex_closure_setOf_lt_re"))
        except Exception:
            pass
    return results


def _r0023_closure_setOf_lt_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.closure_setOf_lt_im
    # closure { z : ℂ | a < z.im } = { z | a ≤ z.im }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OVar("z_pipe_a_le_z_im")
            results.append((rhs, "Mathlib: Complex_closure_setOf_lt_im"))
        except Exception:
            pass
    return results


def _r0024_frontier_setOf_re_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.frontier_setOf_re_lt
    # frontier { z : ℂ | z.re < a } = { z | z.re = a }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "frontier", 1)
    if args is not None:
        try:
            rhs = OVar("z_pipe_z_re_eq_a")
            results.append((rhs, "Mathlib: Complex_frontier_setOf_re_lt"))
        except Exception:
            pass
    return results


def _r0025_frontier_setOf_im_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.frontier_setOf_im_lt
    # frontier { z : ℂ | z.im < a } = { z | z.im = a }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "frontier", 1)
    if args is not None:
        try:
            rhs = OVar("z_pipe_z_im_eq_a")
            results.append((rhs, "Mathlib: Complex_frontier_setOf_im_lt"))
        except Exception:
            pass
    return results


def _r0026_frontier_setOf_lt_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.frontier_setOf_lt_re
    # frontier { z : ℂ | a < z.re } = { z | z.re = a }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "frontier", 1)
    if args is not None:
        try:
            rhs = OVar("z_pipe_z_re_eq_a")
            results.append((rhs, "Mathlib: Complex_frontier_setOf_lt_re"))
        except Exception:
            pass
    return results


def _r0027_frontier_setOf_lt_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.frontier_setOf_lt_im
    # frontier { z : ℂ | a < z.im } = { z | z.im = a }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "frontier", 1)
    if args is not None:
        try:
            rhs = OVar("z_pipe_z_im_eq_a")
            results.append((rhs, "Mathlib: Complex_frontier_setOf_lt_im"))
        except Exception:
            pass
    return results


def _r0028_centerMass_smul_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.centerMass_smul_left
    # t.centerMass (c • w) z = t.centerMass w z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "t_centerMass", 2)
    if args is not None:
        try:
            rhs = OOp("t_centerMass", (OVar("w"), args[1],))
            results.append((rhs, "Mathlib: Finset_centerMass_smul_left"))
        except Exception:
            pass
    return results


def _r0029_range_arg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.range_arg
    # Set.range arg = Set.Ioc (-π) π
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_range", 1)
    if args is not None:
        try:
            rhs = OOp("Set_Ioc", (OVar("minus_pi"), OVar("pi"),))
            results.append((rhs, "Mathlib: Complex_range_arg"))
        except Exception:
            pass
    return results


def _r0030_coe_toCircle(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.coe_toCircle
    # (θ.toCircle : ℂ) = θ.cos + θ.sin * I
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "th_toCircle", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("th_cos"), OOp("*", (OVar("th_sin"), OVar("I")))))
            results.append((rhs, "Mathlib: Real_Angle_coe_toCircle"))
        except Exception:
            pass
    return results


def _r0031_toCircle_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.toCircle_add
    # toCircle (θ₁ + θ₂) = toCircle θ₁ * toCircle θ₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toCircle", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("toCircle", (OVar("th_1"),)), OOp("toCircle", (OVar("th_2"),))))
            results.append((rhs, "Mathlib: Real_Angle_toCircle_add"))
        except Exception:
            pass
    return results


def _r0032_range_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.range_exp
    # range exp = Set.Ioi 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OOp("Set_Ioi", (OLit(0),))
            results.append((rhs, "Mathlib: Real_range_exp"))
        except Exception:
            pass
    return results


def _r0033_isLittleO_pow_exp_atTop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.isLittleO_pow_exp_atTop
    # (fun x : ℝ => x ^ n) =o[atTop] Real.exp
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("o_atTop", (OVar("Real_exp"),))
            results.append((rhs, "Mathlib: Real_isLittleO_pow_exp_atTop"))
        except Exception:
            pass
    return results


def _r0034_coe_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.coe_add
    # ↑(x + y : ℝ) = (↑x + ↑y : Angle)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_plus_y_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("x"), OOp("y", (OVar("colon"), OVar("Angle"),))))
            results.append((rhs, "Mathlib: Real_Angle_coe_add"))
    except Exception:
        pass
    return results


def _r0035_coe_nsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.coe_nsmul
    # ↑(n • x : ℝ) = n • (↑x : Angle)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_x_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("n", (OVar("_unknown"), OOp("x", (OVar("colon"), OVar("Angle"),)),))
            results.append((rhs, "Mathlib: Real_Angle_coe_nsmul"))
    except Exception:
        pass
    return results


def _r0036_intCast_mul_eq_zsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.intCast_mul_eq_zsmul
    # ↑((n : ℝ) * x : ℝ) = n • (↑x : Angle)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_colon_star_x_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("n", (OVar("_unknown"), OOp("x", (OVar("colon"), OVar("Angle"),)),))
            results.append((rhs, "Mathlib: Real_Angle_intCast_mul_eq_zsmul"))
    except Exception:
        pass
    return results


def _r0037_two_zsmul_coe_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.two_zsmul_coe_pi
    # (2 : ℤ) • (π : Angle) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_2_colon", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_Angle_two_zsmul_coe_pi"))
        except Exception:
            pass
    return results


def _r0038_coe_pi_add_coe_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.coe_pi_add_coe_pi
    # (π : Real.Angle) + π = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_Angle_coe_pi_add_coe_pi"))
        except Exception:
            pass
    return results


def _r0039_sin_coe_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.sin_coe_pi
    # sin (π : Angle) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_Angle_sin_coe_pi"))
        except Exception:
            pass
    return results


def _r0040_cos_coe_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.cos_coe_pi
    # cos (π : Angle) = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OVar("minus_1")
            results.append((rhs, "Mathlib: Real_Angle_cos_coe_pi"))
        except Exception:
            pass
    return results


def _r0041_coe_toReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.coe_toReal
    # (θ.toReal : Angle) = θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "th_toReal", 2)
    if args is not None:
        try:
            rhs = OVar("th")
            results.append((rhs, "Mathlib: Real_Angle_coe_toReal"))
        except Exception:
            pass
    return results


def _r0042_cos_toReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.cos_toReal
    # Real.cos θ.toReal = cos θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Real_cos", 1)
    if args is not None:
        try:
            rhs = OOp("cos", (OVar("th"),))
            results.append((rhs, "Mathlib: Real_Angle_cos_toReal"))
        except Exception:
            pass
    return results


def _r0043_tan_coe_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.tan_coe_pi
    # tan (π : Angle) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tan", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_Angle_tan_coe_pi"))
        except Exception:
            pass
    return results


def _r0044_tan_toReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.tan_toReal
    # Real.tan θ.toReal = tan θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Real_tan", 1)
    if args is not None:
        try:
            rhs = OOp("tan", (OVar("th"),))
            results.append((rhs, "Mathlib: Real_Angle_tan_toReal"))
        except Exception:
            pass
    return results


def _r0045_tan_eq_of_two_nsmul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.tan_eq_of_two_nsmul_eq
    # tan θ = tan ψ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tan", 1)
    if args is not None:
        try:
            rhs = OOp("tan", (OVar("psi"),))
            results.append((rhs, "Mathlib: Real_Angle_tan_eq_of_two_nsmul_eq"))
        except Exception:
            pass
    return results


def _r0046_sign_coe_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.sign_coe_pi
    # (π : Angle).sign = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pi_colon_Angle_sign")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_Angle_sign_coe_pi"))
    except Exception:
        pass
    return results


def _r0047_sign_pi_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.sign_pi_add
    # ((π : Angle) + θ).sign = -θ.sign
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pi_colon_Angle_plus_th_sign")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_th_sign")
            results.append((rhs, "Mathlib: Real_Angle_sign_pi_add"))
    except Exception:
        pass
    return results


def _r0048_ofColex_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.Colex.ofColex_bot
    # ofColex (⊥ : Colex (Finset α)) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofColex", 1)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Finset_Colex_ofColex_bot"))
        except Exception:
            pass
    return results


def _r0049_largeSchroder_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.largeSchroder_two
    # largeSchroder 2 = 6
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "largeSchroder", 1)
    if args is not None:
        try:
            rhs = OLit(6)
            results.append((rhs, "Mathlib: Nat_largeSchroder_two"))
        except Exception:
            pass
    return results


def _r0050_largeSchroder_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.largeSchroder_succ
    # largeSchroder (n + 1) = largeSchroder n + ∑ i ≤ n, largeSchroder i * largeSchroder (n - i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "largeSchroder", 1)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("+", (OOp("largeSchroder", (OVar("n"),)), OOp("_unknown", (OVar("i"),)))), OOp("*", (OOp("n", (OVar("largeSchroder"), OVar("i"),)), OOp("largeSchroder", (OOp("-", (OVar("n"), OVar("i"))),))))))
            results.append((rhs, "Mathlib: Nat_largeSchroder_succ"))
        except Exception:
            pass
    return results


def _r0051_smallSchroder_succ_eq_largeSchroder_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.smallSchroder_succ_eq_largeSchroder_div_two
    # smallSchroder (n + 1) = largeSchroder n / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "smallSchroder", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("largeSchroder", (OVar("n"),)), OLit(2)))
            results.append((rhs, "Mathlib: Nat_smallSchroder_succ_eq_largeSchroder_div_two"))
        except Exception:
            pass
    return results


def _r0052_stirlingFirst_succ_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.stirlingFirst_succ_left
    # stirlingFirst (n + 1) k = n * stirlingFirst n k + stirlingFirst n (k - 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "stirlingFirst", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("*", (OVar("n"), OOp("stirlingFirst", (OVar("n"), args[1],)))), OOp("stirlingFirst", (OVar("n"), OOp("-", (args[1], OLit(1))),))))
            results.append((rhs, "Mathlib: Nat_stirlingFirst_succ_left"))
        except Exception:
            pass
    return results


def _r0053_stirlingSecond_succ_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.stirlingSecond_succ_left
    # stirlingSecond (n + 1) k = k * stirlingSecond n k + stirlingSecond n (k - 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "stirlingSecond", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("*", (args[1], OOp("stirlingSecond", (OVar("n"), args[1],)))), OOp("stirlingSecond", (OVar("n"), OOp("-", (args[1], OLit(1))),))))
            results.append((rhs, "Mathlib: Nat_stirlingSecond_succ_left"))
        except Exception:
            pass
    return results


def _r0054_eval_pappAck_step_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.Partrec.Code.eval_pappAck_step_succ
    # (pappAck.step c).eval (n + 1) = ((pappAck.step c).eval n).bind c.eval
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pappAck_step_c_eval", 1)
    if args is not None:
        try:
            rhs = OOp("pappAck_step_c_eval_n_bind", (OVar("c_eval"),))
            results.append((rhs, "Mathlib: Nat_Partrec_Code_eval_pappAck_step_succ"))
        except Exception:
            pass
    return results


def _r0055_range_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.range_im
    # range im = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: Complex_range_im"))
        except Exception:
            pass
    return results


def _r0056_rev_castSucc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin2.rev_castSucc
    # rev (castSucc i) = fs (rev i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rev", 1)
    if args is not None:
        try:
            rhs = OOp("fs", (OOp("rev", (OVar("i"),)),))
            results.append((rhs, "Mathlib: Fin2_rev_castSucc"))
        except Exception:
            pass
    return results


def _r0057_toFin_fs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin2.toFin_fs
    # toFin (fs i) = (toFin i).succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFin", 1)
    if args is not None:
        try:
            rhs = OVar("toFin_i_succ")
            results.append((rhs, "Mathlib: Fin2_toFin_fs"))
        except Exception:
            pass
    return results


def _r0058_ofFin_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin2.ofFin_succ
    # ofFin i.succ = fs (ofFin i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofFin", 1)
    if args is not None:
        try:
            rhs = OOp("fs", (OOp("ofFin", (OVar("i"),)),))
            results.append((rhs, "Mathlib: Fin2_ofFin_succ"))
        except Exception:
            pass
    return results


def _r0059_castLE_comp_castSucc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.castLE_comp_castSucc
    # Fin.castLE h ∘ Fin.castSucc = Fin.castLE (Nat.le_of_succ_le h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("Fin_castLE", (OOp("Nat_le_of_succ_le", (OVar("h"),)),))
            results.append((rhs, "Mathlib: Fin_castLE_comp_castSucc"))
        except Exception:
            pass
    return results


def _r0060_range_castLE(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.range_castLE
    # Set.range (castLE h) = { i : Fin k | (i : ℕ) < n }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_range", 1)
    if args is not None:
        try:
            rhs = OVar("i_colon_Fin_k_pipe_i_colon_lt_n")
            results.append((rhs, "Mathlib: Fin_range_castLE"))
        except Exception:
            pass
    return results


def _r0061_univ_unique(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.univ_unique
    # (univ : Finset α) = {default}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "univ_set", 3)
    if args is not None:
        try:
            rhs = OVar("default")
            results.append((rhs, "Mathlib: Finset_univ_unique"))
        except Exception:
            pass
    return results


def _r0062_coe_toList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.coe_toList
    # (s.toList : Multiset α) = s.val
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_toList", 3)
    if args is not None:
        try:
            rhs = OVar("s_val")
            results.append((rhs, "Mathlib: Finset_coe_toList"))
        except Exception:
            pass
    return results


def _r0063_dens_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.dens_image
    # (s.image f).dens = s.dens
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_image_f_dens")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_dens")
            results.append((rhs, "Mathlib: Finset_dens_image"))
    except Exception:
        pass
    return results


def _r0064_sup_insert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.sup_insert
    # (insert b s : Finset β).sup f = f b ⊔ s.sup f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "insert_b_s_colon_Finset_b_sup", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("b"), OVar("_unknown"), OVar("s_sup"), args[0],))
            results.append((rhs, "Mathlib: Finset_sup_insert"))
        except Exception:
            pass
    return results


def _r0065_sup_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.sup_image
    # (s.image f).sup g = s.sup (g ∘ f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_image_f_sup", 1)
    if args is not None:
        try:
            rhs = OOp("s_sup", (OOp("comp", (args[0], OVar("f"))),))
            results.append((rhs, "Mathlib: Finset_sup_image"))
        except Exception:
            pass
    return results


def _r0066_sup_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.sup_sup
    # s.sup (f ⊔ g) = s.sup f ⊔ s.sup g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_sup", 1)
    if args is not None:
        try:
            rhs = OOp("s_sup", (OVar("f"), OVar("_unknown"), OVar("s_sup"), OVar("g"),))
            results.append((rhs, "Mathlib: Finset_sup_sup"))
        except Exception:
            pass
    return results


def _r0067_sup_disjSum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.sup_disjSum
    # (s.disjSum t).sup f = (s.sup fun x ↦ f (.inl x)) ⊔ (t.sup fun x ↦ f (.inr x))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_disjSum_t_sup", 1)
    if args is not None:
        try:
            rhs = OOp("s_sup_fun_x_f_inl_x", (OVar("_unknown"), OOp("t_sup", (OVar("fun"), OVar("x"), OVar("_unknown"), args[0], OOp("inr", (OVar("x"),)),)),))
            results.append((rhs, "Mathlib: Finset_sup_disjSum"))
        except Exception:
            pass
    return results


def _r0068_sup_singleton_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.sup_singleton_apply
    # (s.sup fun b => {f b}) = s.image f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_sup", 4)
    if args is not None:
        try:
            rhs = OOp("s_image", (OVar("f"),))
            results.append((rhs, "Mathlib: Finset_sup_singleton_apply"))
        except Exception:
            pass
    return results


def _r0069_max_insert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.max_insert
    # (insert a s).max = max ↑a s.max
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("insert_a_s_max")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("max", (OVar("a"), OVar("s_max"),))
            results.append((rhs, "Mathlib: Finset_max_insert"))
    except Exception:
        pass
    return results


def _r0070_max_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.max_eq_top
    # s.max = ⊤ ↔ ⊤ ∈ s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_max")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("top"), OOp("in", (OVar("top"), OVar("s")))))
            results.append((rhs, "Mathlib: Finset_max_eq_top"))
    except Exception:
        pass
    return results


def _r0071_min_insert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.min_insert
    # (insert a s).min = min (↑a) s.min
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("insert_a_s_min")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("min", (OVar("a"), OVar("s_min"),))
            results.append((rhs, "Mathlib: Finset_min_insert"))
    except Exception:
        pass
    return results


def _r0072_min_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.min_eq_bot
    # s.min = ⊥ ↔ ⊥ ∈ s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_min")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("bot"), OOp("in", (OVar("bot"), OVar("s")))))
            results.append((rhs, "Mathlib: Finset_min_eq_bot"))
    except Exception:
        pass
    return results


def _r0073_coe_image_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.coe_image₂
    # (image₂ f s t : Set γ) = Set.image2 f s t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image_2", 6)
    if args is not None:
        try:
            rhs = OOp("Set_image2", (args[0], args[1], args[2],))
            results.append((rhs, "Mathlib: Finset_coe_image_2"))
        except Exception:
            pass
    return results


def _r0074_image_2_singleton_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.image₂_singleton_left
    # image₂ f {a} t = t.image fun b => f a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image_2", 3)
    if args is not None:
        try:
            rhs = OOp("t_image", (OVar("fun"), OVar("b"), OVar("eq_gt"), args[0], args[1], OVar("b"),))
            results.append((rhs, "Mathlib: Finset_image_2_singleton_left"))
        except Exception:
            pass
    return results


def _r0075_image_2_singleton_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.image₂_singleton_right
    # image₂ f s {b} = s.image fun a => f a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image_2", 3)
    if args is not None:
        try:
            rhs = OOp("s_image", (OVar("fun"), OVar("a"), OVar("eq_gt"), args[0], OVar("a"), args[2],))
            results.append((rhs, "Mathlib: Finset_image_2_singleton_right"))
        except Exception:
            pass
    return results


def _r0076_image_2_curry(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.image₂_curry
    # image₂ (curry f) s t = (s ×ˢ t).image f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image_2", 3)
    if args is not None:
        try:
            rhs = OOp("s_times_t_image", (OVar("f"),))
            results.append((rhs, "Mathlib: Finset_image_2_curry"))
        except Exception:
            pass
    return results


def _r0077_image_uncurry_product(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.image_uncurry_product
    # (s ×ˢ t).image (uncurry f) = image₂ f s t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_times_t_image", 1)
    if args is not None:
        try:
            rhs = OOp("image_2", (OVar("f"), OVar("s"), OVar("t"),))
            results.append((rhs, "Mathlib: Finset_image_uncurry_product"))
        except Exception:
            pass
    return results


def _r0078_image_2_swap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.image₂_swap
    # image₂ f s t = image₂ (fun a b => f b a) t s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image_2", 3)
    if args is not None:
        try:
            rhs = OOp("image_2", (OOp("fun", (OVar("a"), OVar("b"), OVar("eq_gt"), args[0], OVar("b"), OVar("a"),)), args[2], args[1],))
            results.append((rhs, "Mathlib: Finset_image_2_swap"))
        except Exception:
            pass
    return results


def _r0079_coe_pimage(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.coe_pimage
    # (s.pimage f : Set β) = f.image s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_pimage", 4)
    if args is not None:
        try:
            rhs = OOp("f_image", (OVar("s"),))
            results.append((rhs, "Mathlib: Finset_coe_pimage"))
        except Exception:
            pass
    return results


def _r0080_pimage_some(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.pimage_some
    # (s.pimage fun x => Part.some (f x)) = s.image f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_pimage", 5)
    if args is not None:
        try:
            rhs = OOp("s_image", (OVar("f"),))
            results.append((rhs, "Mathlib: Finset_pimage_some"))
        except Exception:
            pass
    return results


def _r0081_preimage_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.preimage_univ
    # preimage univ f hf = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preimage", 3)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Finset_preimage_univ"))
        except Exception:
            pass
    return results


def _r0082_toFinset_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_range
    # (Multiset.range n).toFinset = .range n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Multiset_range_n_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("range", (OVar("n"),))
            results.append((rhs, "Mathlib: Multiset_toFinset_range"))
    except Exception:
        pass
    return results


def _r0083_coe_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.coe_range
    # (range n : Set ℕ) = Set.Iio n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 4)
    if args is not None:
        try:
            rhs = OOp("Set_Iio", (args[0],))
            results.append((rhs, "Mathlib: Finset_coe_range"))
        except Exception:
            pass
    return results


def _r0084_toLeft_insert_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.toLeft_insert_inr
    # (insert (inr b) u).toLeft = u.toLeft
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("insert_inr_b_u_toLeft")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("u_toLeft")
            results.append((rhs, "Mathlib: Finset_toLeft_insert_inr"))
    except Exception:
        pass
    return results


def _r0085_singleton_sups(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.singleton_sups
    # {a} ⊻ t = t.image (a ⊔ ·)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("t_image", (OOp("a", (args[0], args[0],)),))
            results.append((rhs, "Mathlib: Finset_singleton_sups"))
        except Exception:
            pass
    return results


def _r0086_sups_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.sups_singleton
    # s ⊻ {b} = s.image (· ⊔ b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OOp("s_image", (OOp("_unknown", (args[0], args[1],)),))
            results.append((rhs, "Mathlib: Finset_sups_singleton"))
        except Exception:
            pass
    return results


def _r0087_univ_sups_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.univ_sups_univ
    # (univ : Finset α) ⊻ univ = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "univ_colon_Finset_a", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Finset_univ_sups_univ"))
        except Exception:
            pass
    return results


def _r0088_filter_sups_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.filter_sups_le
    # {b ∈ s ⊻ t | b ≤ a} = {b ∈ s | b ≤ a} ⊻ {b ∈ t | b ≤ a}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("b_in_s_t_pipe_b_le_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("b_in_s_pipe_b_le_a", (OVar("_unknown"), OVar("b_in_t_pipe_b_le_a"),))
            results.append((rhs, "Mathlib: Finset_filter_sups_le"))
    except Exception:
        pass
    return results


def _r0089_equivCongrLeft_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.equivCongrLeft_symm
    # (@equivCongrLeft _ _ M _ f).symm = equivCongrLeft f.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("at_equivCongrLeft_M_f_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("equivCongrLeft", (OVar("f_symm"),))
            results.append((rhs, "Mathlib: Finsupp_equivCongrLeft_symm"))
    except Exception:
        pass
    return results


def _r0090_coe_equivFunOnFinite_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.coe_equivFunOnFinite_symm
    # ⇑(equivFunOnFinite.symm f) = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("equivFunOnFinite_symm_f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Finsupp_coe_equivFunOnFinite_symm"))
    except Exception:
        pass
    return results


def _r0091_unique_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.unique_ext
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: Finsupp_unique_ext"))
    except Exception:
        pass
    return results


def _r0092_toMultiset_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.toMultiset_sum
    # Finsupp.toMultiset (∑ i ∈ s, f i) = ∑ i ∈ s, Finsupp.toMultiset (f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Finsupp_toMultiset", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("Finsupp_toMultiset"), OOp("f", (OVar("i"),)),))))
            results.append((rhs, "Mathlib: Finsupp_toMultiset_sum"))
        except Exception:
            pass
    return results


def _r0093_single_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.single_mul
    # single a (b₁ * b₂) = single a b₁ * single a b₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "single", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("single", (args[0], OVar("b_1"),)), OOp("single", (args[0], OVar("b_2"),))))
            results.append((rhs, "Mathlib: Finsupp_single_mul"))
        except Exception:
            pass
    return results


def _r0094_smul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.smul_apply
    # (b • v) a = b • v a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "b_v", 1)
    if args is not None:
        try:
            rhs = OOp("b", (OVar("_unknown"), OVar("v"), args[0],))
            results.append((rhs, "Mathlib: Finsupp_smul_apply"))
        except Exception:
            pass
    return results


def _r0095_single_eq_update(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.single_eq_update
    # ⇑(single a b) = Function.update (0 : _) a b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("single_a_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Function_update", (OOp("_0", (OVar("colon"), OVar("_unknown"),)), OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Finsupp_single_eq_update"))
    except Exception:
        pass
    return results


def _r0096_toDFinsupp_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.toDFinsupp_add
    # (f + g).toDFinsupp = f.toDFinsupp + g.toDFinsupp
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_plus_g_toDFinsupp")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("f_toDFinsupp"), OVar("g_toDFinsupp")))
            results.append((rhs, "Mathlib: Finsupp_toDFinsupp_add"))
    except Exception:
        pass
    return results


def _r0097_univ_image_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.univ_image_def
    # Finset.univ.image f = (List.ofFn f).toFinset
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Finset_univ_image", 1)
    if args is not None:
        try:
            rhs = OVar("List_ofFn_f_toFinset")
            results.append((rhs, "Mathlib: Fin_univ_image_def"))
        except Exception:
            pass
    return results


def _r0098_card_lex(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.card_lex
    # Fintype.card (Lex α) = Fintype.card α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Fintype_card", 1)
    if args is not None:
        try:
            rhs = OOp("Fintype_card", (OVar("a"),))
            results.append((rhs, "Mathlib: Fintype_card_lex"))
        except Exception:
            pass
    return results


def _r0099_card_fin_lt_of_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.card_fin_lt_of_le
    # Fintype.card {i : Fin n // i < m} = m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Fintype_card", 1)
    if args is not None:
        try:
            rhs = OVar("m")
            results.append((rhs, "Mathlib: Fintype_card_fin_lt_of_le"))
        except Exception:
            pass
    return results


def _r0100_shiftLeft_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.shiftLeft_natCast
    # (m : ℤ) <<< (n : ℤ) = ↑(m <<< n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m_colon", 2)
    if args is not None:
        try:
            rhs = OVar("m_lt_lt_lt_n")
            results.append((rhs, "Mathlib: Int_shiftLeft_natCast"))
        except Exception:
            pass
    return results


def _r0101_cast_pred(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.cast_pred
    # ∀ {n}, 0 < n → ((n - 1 : ℕ) : R) = n - 1   | 0, h =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n_minus_1_colon", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OVar("n"), OOp("_1", (OVar("pipe"), OVar("_0"), OVar("h"), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: Nat_cast_pred"))
        except Exception:
            pass
    return results


def _r0102_pred_eq_pred(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.pred_eq_pred
    # Order.pred = pred
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Order_pred")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("pred")
            results.append((rhs, "Mathlib: Int_pred_eq_pred"))
    except Exception:
        pass
    return results


def _r0103_log2_eq_succ_log2_shiftRight(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.log2_eq_succ_log2_shiftRight
    # n.log2 = (n >>> 1).log2.succ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_log2")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n_gt_gt_gt_1_log2_succ")
            results.append((rhs, "Mathlib: Nat_log2_eq_succ_log2_shiftRight"))
    except Exception:
        pass
    return results


def _r0104_bodd_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.bodd_succ
    # bodd (succ n) = not (bodd n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bodd", 1)
    if args is not None:
        try:
            rhs = OOp("not", (OOp("bodd", (OVar("n"),)),))
            results.append((rhs, "Mathlib: Nat_bodd_succ"))
        except Exception:
            pass
    return results


def _r0105_div2_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.div2_succ
    # div2 (n + 1) = cond (bodd n) (succ (div2 n)) (div2 n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "div2", 1)
    if args is not None:
        try:
            rhs = OOp("cond", (OOp("bodd", (OVar("n"),)), OOp("succ", (OOp("div2", (OVar("n"),)),)), OOp("div2", (OVar("n"),)),))
            results.append((rhs, "Mathlib: Nat_div2_succ"))
        except Exception:
            pass
    return results


def _r0106_image_cast_int_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.image_cast_int_Icc
    # (↑) '' Icc a b = Icc (a : ℤ) b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("a", (OVar("colon"), OVar("_unknown"),)), args[3],))
            results.append((rhs, "Mathlib: Nat_image_cast_int_Icc"))
        except Exception:
            pass
    return results


def _r0107_choose_succ_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.choose_succ_succ
    # choose (succ n) (succ k) = choose n k + choose n (succ k)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "choose", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("choose", (OVar("n"), OVar("k"),)), OOp("choose", (OVar("n"), OOp("succ", (OVar("k"),)),))))
            results.append((rhs, "Mathlib: Nat_choose_succ_succ"))
        except Exception:
            pass
    return results


def _r0108_choose_succ_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.choose_succ_self
    # choose n (succ n) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "choose", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Nat_choose_succ_self"))
        except Exception:
            pass
    return results


def _r0109_triangle_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.triangle_succ
    # (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("*", (OVar("n"), OOp("//", (OOp("-", (OVar("n"), OLit(1))), OLit(2))))), OVar("n")))
            results.append((rhs, "Mathlib: Nat_triangle_succ"))
        except Exception:
            pass
    return results


def _r0110_multichoose_succ_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.multichoose_succ_succ
    # multichoose (n + 1) (k + 1) = multichoose n (k + 1) + multichoose (n + 1) k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "multichoose", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("multichoose", (OVar("n"), OOp("+", (OVar("k"), OLit(1))),)), OOp("multichoose", (OOp("+", (OVar("n"), OLit(1))), OVar("k"),))))
            results.append((rhs, "Mathlib: Nat_multichoose_succ_succ"))
        except Exception:
            pass
    return results


def _r0111_factorial_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.factorial_succ
    # (n + 1)! = (n + 1) * n !
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_plus_1_bang")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OOp("+", (OVar("n"), OLit(1))), OOp("n", (OOp("not", (OVar("_"),)),))))
            results.append((rhs, "Mathlib: Nat_factorial_succ"))
    except Exception:
        pass
    return results


def _r0112_mul_factorial_pred(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.mul_factorial_pred
    # n * (n - 1)! = n !
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("n", (OOp("not", (OVar("_"),)),))
            results.append((rhs, "Mathlib: Nat_mul_factorial_pred"))
        except Exception:
            pass
    return results


def _r0113_superFactorial_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.superFactorial_succ
    # (sf n.succ) = (n + 1)! * sf n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sf", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("n_plus_1_bang"), OOp("sf", (OVar("n"),))))
            results.append((rhs, "Mathlib: Nat_superFactorial_succ"))
        except Exception:
            pass
    return results


def _r0114_prod_range_succ_factorial(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.prod_range_succ_factorial
    # ∀ n : ℕ, ∏ x ∈ range (n + 1), x ! = sf n   | 0 => rfl   | n + 1 =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("sf", (OVar("n"), OVar("pipe"), OLit(0), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("n"),)), OOp("_1", (OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: Nat_prod_range_succ_factorial"))
        except Exception:
            pass
    return results


def _r0115_zeckendorf_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.zeckendorf_succ
    # zeckendorf (n + 1) = greatestFib (n + 1) :: zeckendorf (n + 1 - fib (greatestFib (n + 1)))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "zeckendorf", 1)
    if args is not None:
        try:
            rhs = OOp("greatestFib", (OOp("+", (OVar("n"), OLit(1))), OVar("colon_colon"), OVar("zeckendorf"), OOp("+", (OVar("n"), OOp("-", (OLit(1), OOp("fib", (OOp("greatestFib", (OOp("+", (OVar("n"), OLit(1))),)),)))))),))
            results.append((rhs, "Mathlib: Nat_zeckendorf_succ"))
        except Exception:
            pass
    return results


def _r0116_zeckendorf_of_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.zeckendorf_of_pos
    # ∀ {n}, 0 < n →     zeckendorf n = greatestFib n :: zeckendorf (n - fib (greatestFib n))   | _n + 1, _ => zeckendorf_succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "zeckendorf", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("greatestFib", (args[0], OVar("colon_colon"), OVar("zeckendorf"), OOp("-", (args[0], OOp("fib", (OOp("greatestFib", (args[0],)),)))), OVar("pipe"), args[0],)), OOp("_1", (OVar("_unknown"), OVar("eq_gt"), OVar("zeckendorf_succ"), OVar("lemma"), OVar("isZeckendorfRep_zeckendorf"), OVar("colon"), OVar("forall"), args[0], OVar("zeckendorf_n_IsZeckendorfRep"), OVar("pipe"), OLit(0), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: Nat_zeckendorf_of_pos"))
        except Exception:
            pass
    return results


def _r0117_ppred_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.ppred_succ
    # ppred (succ n) = some n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ppred", 1)
    if args is not None:
        try:
            rhs = OOp("some", (OVar("n"),))
            results.append((rhs, "Mathlib: Nat_ppred_succ"))
        except Exception:
            pass
    return results


def _r0118_psub_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.psub_succ
    # psub m (succ n) = psub m n >>= ppred
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "psub", 2)
    if args is not None:
        try:
            rhs = OOp("psub", (args[0], OVar("n"), OVar("gt_gt_eq"), OVar("ppred"),))
            results.append((rhs, "Mathlib: Nat_psub_succ"))
        except Exception:
            pass
    return results


def _r0119_minFac_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.minFac_two
    # minFac 2 = 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minFac", 1)
    if args is not None:
        try:
            rhs = OLit(2)
            results.append((rhs, "Mathlib: Nat_minFac_two"))
        except Exception:
            pass
    return results


def _r0120_minFac_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.minFac_eq
    # minFac n = if 2 ∣ n then 2 else minFacAux n 3
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minFac", 1)
    if args is not None:
        try:
            rhs = OOp("if", (OLit(2), OVar("_unknown"), args[0], OVar("then"), OLit(2), OVar("else"), OVar("minFacAux"), args[0], OLit(3),))
            results.append((rhs, "Mathlib: Nat_minFac_eq"))
        except Exception:
            pass
    return results


def _r0121_size_bit(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.size_bit
    # size (bit b n) = succ (size n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "size", 1)
    if args is not None:
        try:
            rhs = OOp("succ", (OOp("size", (OVar("n"),)),))
            results.append((rhs, "Mathlib: Nat_size_bit"))
        except Exception:
            pass
    return results


def _r0122_pred_eq_pred(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.pred_eq_pred
    # Order.pred = pred
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Order_pred")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("pred")
            results.append((rhs, "Mathlib: Nat_pred_eq_pred"))
    except Exception:
        pass
    return results


def _r0123_succ_iterate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.succ_iterate
    # ∀ n, succ^[n] a = a + n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succpow_n", 1)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], OVar("n")))
            results.append((rhs, "Mathlib: Nat_succ_iterate"))
        except Exception:
            pass
    return results


def _r0124_le_succ_iff_eq_or_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.le_succ_iff_eq_or_le
    # m ≤ n.succ ↔ m = n.succ ∨ m ≤ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("or", (OVar("n_succ"), args[0])), OVar("n")))
            results.append((rhs, "Mathlib: Nat_le_succ_iff_eq_or_le"))
        except Exception:
            pass
    return results


def _r0125_natPred_succPNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.natPred_succPNat
    # n.succPNat.natPred = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_succPNat_natPred")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Nat_natPred_succPNat"))
    except Exception:
        pass
    return results


def _r0126_succPNat_natPred(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PNat.succPNat_natPred
    # n.natPred.succPNat = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_natPred_succPNat")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: PNat_succPNat_natPred"))
    except Exception:
        pass
    return results


def _r0127_cast_min(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.cast_min
    # (↑(min p q) : K) = min (p : K) (q : K)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "min_p_q", 2)
    if args is not None:
        try:
            rhs = OOp("min", (OOp("p", (args[0], args[1],)), OOp("q", (args[0], args[1],)),))
            results.append((rhs, "Mathlib: Rat_cast_min"))
        except Exception:
            pass
    return results


def _r0128_cast_max(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.cast_max
    # (↑(max p q) : K) = max (p : K) (q : K)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "max_p_q", 2)
    if args is not None:
        try:
            rhs = OOp("max", (OOp("p", (args[0], args[1],)), OOp("q", (args[0], args[1],)),))
            results.append((rhs, "Mathlib: Rat_cast_max"))
        except Exception:
            pass
    return results


def _r0129_preimage_cast_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.preimage_cast_Icc
    # (↑) ⁻¹' Icc (p : K) q = Icc p q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("Icc", (OVar("p"), args[3],))
            results.append((rhs, "Mathlib: Rat_preimage_cast_Icc"))
        except Exception:
            pass
    return results


def _r0130_preimage_cast_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.preimage_cast_Ico
    # (↑) ⁻¹' Ico (p : K) q = Ico p q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("Ico", (OVar("p"), args[3],))
            results.append((rhs, "Mathlib: Rat_preimage_cast_Ico"))
        except Exception:
            pass
    return results


def _r0131_preimage_cast_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.preimage_cast_Ioc
    # (↑) ⁻¹' Ioc (p : K) q = Ioc p q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OVar("p"), args[3],))
            results.append((rhs, "Mathlib: Rat_preimage_cast_Ioc"))
        except Exception:
            pass
    return results


def _r0132_preimage_cast_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.preimage_cast_Ioo
    # (↑) ⁻¹' Ioo (p : K) q = Ioo p q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OVar("p"), args[3],))
            results.append((rhs, "Mathlib: Rat_preimage_cast_Ioo"))
        except Exception:
            pass
    return results


def _r0133_preimage_cast_Ici(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.preimage_cast_Ici
    # (↑) ⁻¹' Ici (q : K) = Ici q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("Ici", (OVar("q"),))
            results.append((rhs, "Mathlib: Rat_preimage_cast_Ici"))
        except Exception:
            pass
    return results


def _r0134_preimage_cast_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.preimage_cast_Iic
    # (↑) ⁻¹' Iic (q : K) = Iic q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("Iic", (OVar("q"),))
            results.append((rhs, "Mathlib: Rat_preimage_cast_Iic"))
        except Exception:
            pass
    return results


def _r0135_preimage_cast_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.preimage_cast_Ioi
    # (↑) ⁻¹' Ioi (q : K) = Ioi q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OVar("q"),))
            results.append((rhs, "Mathlib: Rat_preimage_cast_Ioi"))
        except Exception:
            pass
    return results


def _r0136_preimage_cast_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.preimage_cast_Iio
    # (↑) ⁻¹' Iio (q : K) = Iio q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("Iio", (OVar("q"),))
            results.append((rhs, "Mathlib: Rat_preimage_cast_Iio"))
        except Exception:
            pass
    return results


def _r0137_preimage_cast_uIcc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.preimage_cast_uIcc
    # (↑) ⁻¹' uIcc (p : K) q = uIcc p q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("uIcc", (OVar("p"), args[3],))
            results.append((rhs, "Mathlib: Rat_preimage_cast_uIcc"))
        except Exception:
            pass
    return results


def _r0138_preimage_cast_uIoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.preimage_cast_uIoc
    # (↑) ⁻¹' uIoc (p : K) q = uIoc p q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("uIoc", (OVar("p"), args[3],))
            results.append((rhs, "Mathlib: Rat_preimage_cast_uIoc"))
        except Exception:
            pass
    return results


def _r0139_sInf_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sInf_univ
    # sInf (@Set.univ ℝ) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sInf", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_sInf_univ"))
        except Exception:
            pass
    return results


def _r0140_sym2Mul_apply_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.sym2Mul_apply_mk
    # f.sym2Mul s(a, b) = f a * f b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_sym2Mul", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("f", (OVar("a"),)), OOp("f", (OVar("b"),))))
            results.append((rhs, "Mathlib: Finsupp_sym2Mul_apply_mk"))
        except Exception:
            pass
    return results


def _r0141_algebraMap_eq_gen_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IntermediateField.algebraAdjoinAdjoin.algebraMap_eq_gen_self
    # algebraMap (Algebra.adjoin F {x}) F⟮x⟯ ⟨x, Algebra.self_mem_adjoin_singleton F x⟩ =     AdjoinSimple.gen F x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "algebraMap", 3)
    if args is not None:
        try:
            rhs = OOp("AdjoinSimple_gen", (OVar("F"), OVar("x"),))
            results.append((rhs, "Mathlib: IntermediateField_algebraAdjoinAdjoin_algebraMap_eq_gen_self"))
        except Exception:
            pass
    return results


def _r0142_minpolyX_aeval_X(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RatFunc.minpolyX_aeval_X
    # (f.minpolyX K⟮f⟯).aeval (X : K⟮X⟯) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_minpolyX_K_f_aeval", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: RatFunc_minpolyX_aeval_X"))
        except Exception:
            pass
    return results


def _r0143_cycleRange_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.cycleRange_apply
    # cycleRange i j = if j < i then j + 1 else if j = i then 0 else j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cycleRange", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("<", (OOp("if", (args[1],)), OOp("+", (OOp("i", (OVar("then"), args[1],)), OOp("_1", (OVar("else"), OVar("if"), args[1],)))))), OOp("i", (OVar("then"), OLit(0), OVar("else"), args[1],))))
            results.append((rhs, "Mathlib: Fin_cycleRange_apply"))
        except Exception:
            pass
    return results


def _r0144_succAbove_cycleRange(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.succAbove_cycleRange
    # i.succ.succAbove (i.cycleRange j) = swap 0 i.succ j.succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_succ_succAbove", 1)
    if args is not None:
        try:
            rhs = OOp("swap", (OLit(0), OVar("i_succ"), OVar("j_succ"),))
            results.append((rhs, "Mathlib: Fin_succAbove_cycleRange"))
        except Exception:
            pass
    return results


def _r0145_cycleRange_symm_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.cycleRange_symm_succ
    # i.cycleRange.symm j.succ = i.succAbove j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_cycleRange_symm", 1)
    if args is not None:
        try:
            rhs = OOp("i_succAbove", (OVar("j"),))
            results.append((rhs, "Mathlib: Fin_cycleRange_symm_succ"))
        except Exception:
            pass
    return results


def _r0146_cycleIcc_of_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.cycleIcc_of_lt
    # (cycleIcc i j) k = k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cycleIcc_i_j", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Fin_cycleIcc_of_lt"))
        except Exception:
            pass
    return results


def _r0147_affineCombinationSingleWeights_apply_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.affineCombinationSingleWeights_apply_of_ne
    # affineCombinationSingleWeights k i j = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "affineCombinationSingleWeights", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Finset_affineCombinationSingleWeights_apply_of_ne"))
        except Exception:
            pass
    return results


def _r0148_sum_affineCombinationSingleWeights(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.sum_affineCombinationSingleWeights
    # ∑ j ∈ s, affineCombinationSingleWeights k i j = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Finset_sum_affineCombinationSingleWeights"))
        except Exception:
            pass
    return results


def _r0149_linearEquivFunOnFinite_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.linearEquivFunOnFinite_symm_apply
    # (linearEquivFunOnFinite R M α).symm f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "linearEquivFunOnFinite_R_M_a_symm", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Finsupp_linearEquivFunOnFinite_symm_apply"))
        except Exception:
            pass
    return results


def _r0150_coeFn_toL1(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Integrable.coeFn_toL1
    # hf.toL1 f =ᵐ[μ] f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hf_toL1", 1)
    if args is not None:
        try:
            rhs = OOp("mu", (args[0],))
            results.append((rhs, "Mathlib: Integrable_coeFn_toL1"))
        except Exception:
            pass
    return results


def _r0151_volume_real_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.volume_real_Ico
    # volume.real (Ico a b) = max (b - a) 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "volume_real", 1)
    if args is not None:
        try:
            rhs = OOp("max", (OOp("-", (OVar("b"), OVar("a"))), OLit(0),))
            results.append((rhs, "Mathlib: Real_volume_real_Ico"))
        except Exception:
            pass
    return results


def _r0152_volume_real_Ico_of_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.volume_real_Ico_of_le
    # volume.real (Ico a b) = b - a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "volume_real", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OVar("b"), OVar("a")))
            results.append((rhs, "Mathlib: Real_volume_real_Ico_of_le"))
        except Exception:
            pass
    return results


def _r0153_volume_real_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.volume_real_Icc
    # volume.real (Icc a b) = max (b - a) 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "volume_real", 1)
    if args is not None:
        try:
            rhs = OOp("max", (OOp("-", (OVar("b"), OVar("a"))), OLit(0),))
            results.append((rhs, "Mathlib: Real_volume_real_Icc"))
        except Exception:
            pass
    return results


def _r0154_volume_real_Icc_of_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.volume_real_Icc_of_le
    # volume.real (Icc a b) = b - a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "volume_real", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OVar("b"), OVar("a")))
            results.append((rhs, "Mathlib: Real_volume_real_Icc_of_le"))
        except Exception:
            pass
    return results


def _r0155_volume_real_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.volume_real_Ioo
    # volume.real (Ioo a b) = max (b - a) 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "volume_real", 1)
    if args is not None:
        try:
            rhs = OOp("max", (OOp("-", (OVar("b"), OVar("a"))), OLit(0),))
            results.append((rhs, "Mathlib: Real_volume_real_Ioo"))
        except Exception:
            pass
    return results


def _r0156_volume_real_Ioo_of_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.volume_real_Ioo_of_le
    # volume.real (Ioo a b) = b - a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "volume_real", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OVar("b"), OVar("a")))
            results.append((rhs, "Mathlib: Real_volume_real_Ioo_of_le"))
        except Exception:
            pass
    return results


def _r0157_volume_real_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.volume_real_Ioc
    # volume.real (Ioc a b) = max (b - a) 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "volume_real", 1)
    if args is not None:
        try:
            rhs = OOp("max", (OOp("-", (OVar("b"), OVar("a"))), OLit(0),))
            results.append((rhs, "Mathlib: Real_volume_real_Ioc"))
        except Exception:
            pass
    return results


def _r0158_volume_real_Ioc_of_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.volume_real_Ioc_of_le
    # volume.real (Ioc a b) = b - a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "volume_real", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OVar("b"), OVar("a")))
            results.append((rhs, "Mathlib: Real_volume_real_Ioc_of_le"))
        except Exception:
            pass
    return results


def _r0159_liminf_of_not_isCoboundedUnder(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.liminf_of_not_isCoboundedUnder
    # liminf u f = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "liminf", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_liminf_of_not_isCoboundedUnder"))
        except Exception:
            pass
    return results


def _r0160_liminf_of_not_isBoundedUnder(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.liminf_of_not_isBoundedUnder
    # liminf u f = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "liminf", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_liminf_of_not_isBoundedUnder"))
        except Exception:
            pass
    return results


def _r0161_coe_min(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.coe_min
    # ↑(min a b) = (min a b : ℕ)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("min_a_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("min", (OVar("a"), OVar("b"), OVar("colon"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: Fin_coe_min"))
    except Exception:
        pass
    return results


def _r0162_box_succ_eq_sdiff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.box_succ_eq_sdiff
    # box (n + 1) = Icc (-n.succ : α) n.succ \\ Icc (-n) n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "box", 1)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("minus_n_succ", (OVar("colon"), OVar("a"),)), OVar("n_succ"), OVar("bsl"), OVar("Icc"), OVar("minus_n"), OVar("n"),))
            results.append((rhs, "Mathlib: Finset_box_succ_eq_sdiff"))
        except Exception:
            pass
    return results


def _r0163_box_succ_disjUnion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.box_succ_disjUnion
    # (box (n + 1)).disjUnion (Icc (-n : α) n) (disjoint_box_succ_prod _) =       Icc (-n.succ : α) n.succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "box_n_plus_1_disjUnion", 2)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("minus_n_succ", (OVar("colon"), OVar("a"),)), OVar("n_succ"),))
            results.append((rhs, "Mathlib: Finset_box_succ_disjUnion"))
        except Exception:
            pass
    return results


def _r0164_finsetImage_val_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.finsetImage_val_Ico
    # (Ico a b).image val = Ico (a : ℕ) b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico_a_b_image", 1)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("a", (OVar("colon"), OVar("_unknown"),)), OVar("b"),))
            results.append((rhs, "Mathlib: Fin_finsetImage_val_Ico"))
        except Exception:
            pass
    return results


def _r0165_finsetImage_val_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.finsetImage_val_Ioc
    # (Ioc a b).image val = Ioc (a : ℕ) b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioc_a_b_image", 1)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("a", (OVar("colon"), OVar("_unknown"),)), OVar("b"),))
            results.append((rhs, "Mathlib: Fin_finsetImage_val_Ioc"))
        except Exception:
            pass
    return results


def _r0166_finsetImage_val_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.finsetImage_val_Ioo
    # (Ioo a b).image val = Ioo (a : ℕ) b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioo_a_b_image", 1)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OOp("a", (OVar("colon"), OVar("_unknown"),)), OVar("b"),))
            results.append((rhs, "Mathlib: Fin_finsetImage_val_Ioo"))
        except Exception:
            pass
    return results


def _r0167_finsetImage_val_uIcc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.finsetImage_val_uIcc
    # (uIcc a b).image val = uIcc (a : ℕ) b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "uIcc_a_b_image", 1)
    if args is not None:
        try:
            rhs = OOp("uIcc", (OOp("a", (OVar("colon"), OVar("_unknown"),)), OVar("b"),))
            results.append((rhs, "Mathlib: Fin_finsetImage_val_uIcc"))
        except Exception:
            pass
    return results


def _r0168_finsetImage_val_Ici(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.finsetImage_val_Ici
    # (Ici a).image val = Ico (a : ℕ) n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ici_a_image", 1)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("a", (OVar("colon"), OVar("_unknown"),)), OVar("n"),))
            results.append((rhs, "Mathlib: Fin_finsetImage_val_Ici"))
        except Exception:
            pass
    return results


def _r0169_finsetImage_val_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.finsetImage_val_Ioi
    # (Ioi a).image val = Ioo (a : ℕ) n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioi_a_image", 1)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OOp("a", (OVar("colon"), OVar("_unknown"),)), OVar("n"),))
            results.append((rhs, "Mathlib: Fin_finsetImage_val_Ioi"))
        except Exception:
            pass
    return results


def _r0170_finsetImage_val_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.finsetImage_val_Iic
    # (Iic a).image val = Iic (a : ℕ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iic_a_image", 1)
    if args is not None:
        try:
            rhs = OOp("Iic", (OOp("a", (OVar("colon"), OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: Fin_finsetImage_val_Iic"))
        except Exception:
            pass
    return results


def _r0171_finsetImage_val_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.finsetImage_val_Iio
    # (Iio b).image val = Iio (b : ℕ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iio_b_image", 1)
    if args is not None:
        try:
            rhs = OOp("Iio", (OOp("b", (OVar("colon"), OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: Fin_finsetImage_val_Iio"))
        except Exception:
            pass
    return results


def _r0172_intervalGapsWithin_succ_fst_of_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.intervalGapsWithin_succ_fst_of_lt
    # (F.intervalGapsWithin h a b (j.succ)).1 = (F.orderEmbOfFin (α := α ×ₗ α) h ⟨j, hj⟩).2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("F_intervalGapsWithin_h_a_b_j_succ_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("F_orderEmbOfFin_a_colon_eq_a_times_a_h_j_hj_2")
            results.append((rhs, "Mathlib: Finset_intervalGapsWithin_succ_fst_of_lt"))
    except Exception:
        pass
    return results


def _r0173_preimage_val_Ici_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_val_Ici_val
    # (↑) ⁻¹' Ici (i : ℕ) = Ici i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("Ici", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_val_Ici_val"))
        except Exception:
            pass
    return results


def _r0174_preimage_val_Ioi_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_val_Ioi_val
    # (↑) ⁻¹' Ioi (i : ℕ) = Ioi i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_val_Ioi_val"))
        except Exception:
            pass
    return results


def _r0175_preimage_val_Iic_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_val_Iic_val
    # (↑) ⁻¹' Iic (i : ℕ) = Iic i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("Iic", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_val_Iic_val"))
        except Exception:
            pass
    return results


def _r0176_preimage_val_Iio_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_val_Iio_val
    # (↑) ⁻¹' Iio (i : ℕ) = Iio i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("Iio", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_val_Iio_val"))
        except Exception:
            pass
    return results


def _r0177_preimage_val_Icc_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_val_Icc_val
    # (↑) ⁻¹' Icc (i : ℕ) j = Icc i j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("Icc", (OVar("i"), args[3],))
            results.append((rhs, "Mathlib: Fin_preimage_val_Icc_val"))
        except Exception:
            pass
    return results


def _r0178_preimage_val_Ico_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_val_Ico_val
    # (↑) ⁻¹' Ico (i : ℕ) j = Ico i j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("Ico", (OVar("i"), args[3],))
            results.append((rhs, "Mathlib: Fin_preimage_val_Ico_val"))
        except Exception:
            pass
    return results


def _r0179_preimage_val_Ioc_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_val_Ioc_val
    # (↑) ⁻¹' Ioc (i : ℕ) j = Ioc i j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OVar("i"), args[3],))
            results.append((rhs, "Mathlib: Fin_preimage_val_Ioc_val"))
        except Exception:
            pass
    return results


def _r0180_preimage_val_Ioo_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_val_Ioo_val
    # (↑) ⁻¹' Ioo (i : ℕ) j = Ioo i j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OVar("i"), args[3],))
            results.append((rhs, "Mathlib: Fin_preimage_val_Ioo_val"))
        except Exception:
            pass
    return results


def _r0181_preimage_val_uIcc_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_val_uIcc_val
    # (↑) ⁻¹' uIcc (i : ℕ) j = uIcc i j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("uIcc", (OVar("i"), args[3],))
            results.append((rhs, "Mathlib: Fin_preimage_val_uIcc_val"))
        except Exception:
            pass
    return results


def _r0182_preimage_val_uIoc_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_val_uIoc_val
    # (↑) ⁻¹' uIoc (i : ℕ) j = uIoc i j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("uIoc", (OVar("i"), args[3],))
            results.append((rhs, "Mathlib: Fin_preimage_val_uIoc_val"))
        except Exception:
            pass
    return results


def _r0183_preimage_val_uIoo_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_val_uIoo_val
    # (↑) ⁻¹' uIoo (i : ℕ) j = uIoo i j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("uIoo", (OVar("i"), args[3],))
            results.append((rhs, "Mathlib: Fin_preimage_val_uIoo_val"))
        except Exception:
            pass
    return results


def _r0184_image_val_Ici(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_val_Ici
    # (↑) '' Ici i = Ico (i : ℕ) n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("i", (OVar("colon"), OVar("_unknown"),)), OVar("n"),))
            results.append((rhs, "Mathlib: Fin_image_val_Ici"))
        except Exception:
            pass
    return results


def _r0185_image_val_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_val_Iic
    # (↑) '' Iic i = Iic (i : ℕ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("Iic", (OOp("i", (OVar("colon"), OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: Fin_image_val_Iic"))
        except Exception:
            pass
    return results


def _r0186_image_val_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_val_Iio
    # (↑) '' Iio i = Iio (i : ℕ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("Iio", (OOp("i", (OVar("colon"), OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: Fin_image_val_Iio"))
        except Exception:
            pass
    return results


def _r0187_image_val_uIoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_val_uIoc
    # (↑) '' uIoc i j = uIoc (i : ℕ) j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("uIoc", (OOp("i", (OVar("colon"), OVar("_unknown"),)), args[3],))
            results.append((rhs, "Mathlib: Fin_image_val_uIoc"))
        except Exception:
            pass
    return results


def _r0188_image_val_uIoo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_val_uIoo
    # (↑) '' uIoo i j = uIoo (i : ℕ) j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("uIoo", (OOp("i", (OVar("colon"), OVar("_unknown"),)), args[3],))
            results.append((rhs, "Mathlib: Fin_image_val_uIoo"))
        except Exception:
            pass
    return results


def _r0189_preimage_castLE_Ici_castLE(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_castLE_Ici_castLE
    # castLE h ⁻¹' Ici (castLE h i) = Ici i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castLE", 4)
    if args is not None:
        try:
            rhs = OOp("Ici", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_castLE_Ici_castLE"))
        except Exception:
            pass
    return results


def _r0190_image_castLE_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_castLE_Iio
    # castLE h '' Iio i = Iio (castLE h i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castLE", 4)
    if args is not None:
        try:
            rhs = OOp("Iio", (OOp("castLE", (args[0], args[3],)),))
            results.append((rhs, "Mathlib: Fin_image_castLE_Iio"))
        except Exception:
            pass
    return results


def _r0191_image_castLE_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_castLE_Icc
    # castLE h '' Icc i j = Icc (castLE h i) (castLE h j)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castLE", 5)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("castLE", (args[0], args[3],)), OOp("castLE", (args[0], args[4],)),))
            results.append((rhs, "Mathlib: Fin_image_castLE_Icc"))
        except Exception:
            pass
    return results


def _r0192_preimage_castAdd_Ici_castAdd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_castAdd_Ici_castAdd
    # castAdd m ⁻¹' Ici (castAdd m i) = Ici i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castAdd", 4)
    if args is not None:
        try:
            rhs = OOp("Ici", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_castAdd_Ici_castAdd"))
        except Exception:
            pass
    return results


def _r0193_preimage_castAdd_Ioi_castAdd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_castAdd_Ioi_castAdd
    # castAdd m ⁻¹' Ioi (castAdd m i) = Ioi i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castAdd", 4)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_castAdd_Ioi_castAdd"))
        except Exception:
            pass
    return results


def _r0194_preimage_castAdd_Iic_castAdd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_castAdd_Iic_castAdd
    # castAdd m ⁻¹' Iic (castAdd m i) = Iic i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castAdd", 4)
    if args is not None:
        try:
            rhs = OOp("Iic", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_castAdd_Iic_castAdd"))
        except Exception:
            pass
    return results


def _r0195_preimage_castAdd_Iio_castAdd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_castAdd_Iio_castAdd
    # castAdd m ⁻¹' Iio (castAdd m i) = Iio i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castAdd", 4)
    if args is not None:
        try:
            rhs = OOp("Iio", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_castAdd_Iio_castAdd"))
        except Exception:
            pass
    return results


def _r0196_preimage_castAdd_Icc_castAdd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_castAdd_Icc_castAdd
    # castAdd m ⁻¹' Icc (castAdd m i) (castAdd m j) = Icc i j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castAdd", 5)
    if args is not None:
        try:
            rhs = OOp("Icc", (OVar("i"), OVar("j"),))
            results.append((rhs, "Mathlib: Fin_preimage_castAdd_Icc_castAdd"))
        except Exception:
            pass
    return results


def _r0197_image_castAdd_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_castAdd_Iio
    # castAdd m '' Iio i = Iio (castAdd m i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castAdd", 4)
    if args is not None:
        try:
            rhs = OOp("Iio", (OOp("castAdd", (args[0], args[3],)),))
            results.append((rhs, "Mathlib: Fin_image_castAdd_Iio"))
        except Exception:
            pass
    return results


def _r0198_image_castAdd_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_castAdd_Icc
    # castAdd m '' Icc i j = Icc (castAdd m i) (castAdd m j)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castAdd", 5)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("castAdd", (args[0], args[3],)), OOp("castAdd", (args[0], args[4],)),))
            results.append((rhs, "Mathlib: Fin_image_castAdd_Icc"))
        except Exception:
            pass
    return results


def _r0199_preimage_cast_Ici(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_cast_Ici
    # .cast h ⁻¹' Ici i = Ici (i.cast h.symm)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cast", 4)
    if args is not None:
        try:
            rhs = OOp("Ici", (OOp("i_cast", (OVar("h_symm"),)),))
            results.append((rhs, "Mathlib: Fin_preimage_cast_Ici"))
        except Exception:
            pass
    return results


def _r0200_preimage_cast_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_cast_Ioi
    # .cast h ⁻¹' Ioi i = Ioi (i.cast h.symm)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cast", 4)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OOp("i_cast", (OVar("h_symm"),)),))
            results.append((rhs, "Mathlib: Fin_preimage_cast_Ioi"))
        except Exception:
            pass
    return results


def _r0201_preimage_cast_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_cast_Iic
    # .cast h ⁻¹' Iic i = Iic (i.cast h.symm)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cast", 4)
    if args is not None:
        try:
            rhs = OOp("Iic", (OOp("i_cast", (OVar("h_symm"),)),))
            results.append((rhs, "Mathlib: Fin_preimage_cast_Iic"))
        except Exception:
            pass
    return results


def _r0202_preimage_cast_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_cast_Iio
    # .cast h ⁻¹' Iio i = Iio (i.cast h.symm)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cast", 4)
    if args is not None:
        try:
            rhs = OOp("Iio", (OOp("i_cast", (OVar("h_symm"),)),))
            results.append((rhs, "Mathlib: Fin_preimage_cast_Iio"))
        except Exception:
            pass
    return results


def _r0203_preimage_cast_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_cast_Icc
    # .cast h ⁻¹' Icc i j = Icc (i.cast h.symm) (j.cast h.symm)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cast", 5)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("i_cast", (OVar("h_symm"),)), OOp("j_cast", (OVar("h_symm"),)),))
            results.append((rhs, "Mathlib: Fin_preimage_cast_Icc"))
        except Exception:
            pass
    return results


def _r0204_preimage_castSucc_Ioi_castSucc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_castSucc_Ioi_castSucc
    # castSucc ⁻¹' Ioi i.castSucc = Ioi i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castSucc", 3)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_castSucc_Ioi_castSucc"))
        except Exception:
            pass
    return results


def _r0205_preimage_castSucc_Iic_castSucc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_castSucc_Iic_castSucc
    # castSucc ⁻¹' Iic i.castSucc = Iic i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castSucc", 3)
    if args is not None:
        try:
            rhs = OOp("Iic", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_castSucc_Iic_castSucc"))
        except Exception:
            pass
    return results


def _r0206_preimage_castSucc_Iio_castSucc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_castSucc_Iio_castSucc
    # castSucc ⁻¹' Iio i.castSucc = Iio i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castSucc", 3)
    if args is not None:
        try:
            rhs = OOp("Iio", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_castSucc_Iio_castSucc"))
        except Exception:
            pass
    return results


def _r0207_preimage_castSucc_Icc_castSucc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_castSucc_Icc_castSucc
    # castSucc ⁻¹' Icc i.castSucc j.castSucc = Icc i j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castSucc", 4)
    if args is not None:
        try:
            rhs = OOp("Icc", (OVar("i"), OVar("j"),))
            results.append((rhs, "Mathlib: Fin_preimage_castSucc_Icc_castSucc"))
        except Exception:
            pass
    return results


def _r0208_image_castSucc_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_castSucc_Iic
    # castSucc '' Iic i = Iic i.castSucc
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castSucc", 3)
    if args is not None:
        try:
            rhs = OOp("Iic", (OVar("i_castSucc"),))
            results.append((rhs, "Mathlib: Fin_image_castSucc_Iic"))
        except Exception:
            pass
    return results


def _r0209_image_castSucc_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_castSucc_Iio
    # castSucc '' Iio i = Iio i.castSucc
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castSucc", 3)
    if args is not None:
        try:
            rhs = OOp("Iio", (OVar("i_castSucc"),))
            results.append((rhs, "Mathlib: Fin_image_castSucc_Iio"))
        except Exception:
            pass
    return results


def _r0210_image_castSucc_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_castSucc_Icc
    # castSucc '' Icc i j = Icc i.castSucc j.castSucc
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castSucc", 4)
    if args is not None:
        try:
            rhs = OOp("Icc", (OVar("i_castSucc"), OVar("j_castSucc"),))
            results.append((rhs, "Mathlib: Fin_image_castSucc_Icc"))
        except Exception:
            pass
    return results


def _r0211_image_castSucc_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_castSucc_Ico
    # castSucc '' Ico i j = Ico i.castSucc j.castSucc
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castSucc", 4)
    if args is not None:
        try:
            rhs = OOp("Ico", (OVar("i_castSucc"), OVar("j_castSucc"),))
            results.append((rhs, "Mathlib: Fin_image_castSucc_Ico"))
        except Exception:
            pass
    return results


def _r0212_image_castSucc_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_castSucc_Ioc
    # castSucc '' Ioc i j = Ioc i.castSucc j.castSucc
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castSucc", 4)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OVar("i_castSucc"), OVar("j_castSucc"),))
            results.append((rhs, "Mathlib: Fin_image_castSucc_Ioc"))
        except Exception:
            pass
    return results


def _r0213_image_castSucc_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_castSucc_Ioo
    # castSucc '' Ioo i j = Ioo i.castSucc j.castSucc
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castSucc", 4)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OVar("i_castSucc"), OVar("j_castSucc"),))
            results.append((rhs, "Mathlib: Fin_image_castSucc_Ioo"))
        except Exception:
            pass
    return results


def _r0214_image_castSucc_uIcc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_castSucc_uIcc
    # castSucc '' uIcc i j = uIcc i.castSucc j.castSucc
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castSucc", 4)
    if args is not None:
        try:
            rhs = OOp("uIcc", (OVar("i_castSucc"), OVar("j_castSucc"),))
            results.append((rhs, "Mathlib: Fin_image_castSucc_uIcc"))
        except Exception:
            pass
    return results


def _r0215_image_castSucc_uIoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_castSucc_uIoc
    # castSucc '' uIoc i j = uIoc i.castSucc j.castSucc
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castSucc", 4)
    if args is not None:
        try:
            rhs = OOp("uIoc", (OVar("i_castSucc"), OVar("j_castSucc"),))
            results.append((rhs, "Mathlib: Fin_image_castSucc_uIoc"))
        except Exception:
            pass
    return results


def _r0216_image_castSucc_uIoo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_castSucc_uIoo
    # castSucc '' uIoo i j = uIoo i.castSucc j.castSucc
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castSucc", 4)
    if args is not None:
        try:
            rhs = OOp("uIoo", (OVar("i_castSucc"), OVar("j_castSucc"),))
            results.append((rhs, "Mathlib: Fin_image_castSucc_uIoo"))
        except Exception:
            pass
    return results


def _r0217_preimage_natAdd_Ioi_natAdd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_natAdd_Ioi_natAdd
    # natAdd m ⁻¹' Ioi (natAdd m i) = Ioi i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "natAdd", 4)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_natAdd_Ioi_natAdd"))
        except Exception:
            pass
    return results


def _r0218_preimage_natAdd_Iic_natAdd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_natAdd_Iic_natAdd
    # natAdd m ⁻¹' Iic (natAdd m i) = Iic i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "natAdd", 4)
    if args is not None:
        try:
            rhs = OOp("Iic", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_natAdd_Iic_natAdd"))
        except Exception:
            pass
    return results


def _r0219_preimage_natAdd_Iio_natAdd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_natAdd_Iio_natAdd
    # natAdd m ⁻¹' Iio (natAdd m i) = Iio i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "natAdd", 4)
    if args is not None:
        try:
            rhs = OOp("Iio", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_natAdd_Iio_natAdd"))
        except Exception:
            pass
    return results


def _r0220_preimage_natAdd_Icc_natAdd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_natAdd_Icc_natAdd
    # natAdd m ⁻¹' Icc (natAdd m i) (natAdd m j) = Icc i j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "natAdd", 5)
    if args is not None:
        try:
            rhs = OOp("Icc", (OVar("i"), OVar("j"),))
            results.append((rhs, "Mathlib: Fin_preimage_natAdd_Icc_natAdd"))
        except Exception:
            pass
    return results


def _r0221_preimage_addNat_Ioi_addNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_addNat_Ioi_addNat
    # (addNat · m) ⁻¹' Ioi (i.addNat m) = Ioi i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "addNat_m", 3)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_addNat_Ioi_addNat"))
        except Exception:
            pass
    return results


def _r0222_preimage_addNat_Iic_addNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_addNat_Iic_addNat
    # (addNat · m) ⁻¹' Iic (i.addNat m) = Iic i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "addNat_m", 3)
    if args is not None:
        try:
            rhs = OOp("Iic", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_addNat_Iic_addNat"))
        except Exception:
            pass
    return results


def _r0223_preimage_addNat_Iio_addNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_addNat_Iio_addNat
    # (addNat · m) ⁻¹' Iio (i.addNat m) = Iio i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "addNat_m", 3)
    if args is not None:
        try:
            rhs = OOp("Iio", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_addNat_Iio_addNat"))
        except Exception:
            pass
    return results


def _r0224_preimage_addNat_Icc_addNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_addNat_Icc_addNat
    # (addNat · m) ⁻¹' Icc (i.addNat m) (j.addNat m) = Icc i j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "addNat_m", 4)
    if args is not None:
        try:
            rhs = OOp("Icc", (OVar("i"), OVar("j"),))
            results.append((rhs, "Mathlib: Fin_preimage_addNat_Icc_addNat"))
        except Exception:
            pass
    return results


def _r0225_preimage_succ_Ioi_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_succ_Ioi_succ
    # succ ⁻¹' Ioi i.succ = Ioi i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 3)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_succ_Ioi_succ"))
        except Exception:
            pass
    return results


def _r0226_preimage_succ_Iic_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_succ_Iic_succ
    # succ ⁻¹' Iic i.succ = Iic i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 3)
    if args is not None:
        try:
            rhs = OOp("Iic", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_succ_Iic_succ"))
        except Exception:
            pass
    return results


def _r0227_preimage_succ_Iio_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_succ_Iio_succ
    # succ ⁻¹' Iio i.succ = Iio i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 3)
    if args is not None:
        try:
            rhs = OOp("Iio", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_preimage_succ_Iio_succ"))
        except Exception:
            pass
    return results


def _r0228_preimage_succ_Icc_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_succ_Icc_succ
    # succ ⁻¹' Icc i.succ j.succ = Icc i j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 4)
    if args is not None:
        try:
            rhs = OOp("Icc", (OVar("i"), OVar("j"),))
            results.append((rhs, "Mathlib: Fin_preimage_succ_Icc_succ"))
        except Exception:
            pass
    return results


def _r0229_preimage_succ_Ico_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_succ_Ico_succ
    # succ ⁻¹' Ico i.succ j.succ = Ico i j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 4)
    if args is not None:
        try:
            rhs = OOp("Ico", (OVar("i"), OVar("j"),))
            results.append((rhs, "Mathlib: Fin_preimage_succ_Ico_succ"))
        except Exception:
            pass
    return results


def _r0230_preimage_succ_Ioc_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_succ_Ioc_succ
    # succ ⁻¹' Ioc i.succ j.succ = Ioc i j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 4)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OVar("i"), OVar("j"),))
            results.append((rhs, "Mathlib: Fin_preimage_succ_Ioc_succ"))
        except Exception:
            pass
    return results


def _r0231_preimage_succ_Ioo_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_succ_Ioo_succ
    # succ ⁻¹' Ioo i.succ j.succ = Ioo i j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 4)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OVar("i"), OVar("j"),))
            results.append((rhs, "Mathlib: Fin_preimage_succ_Ioo_succ"))
        except Exception:
            pass
    return results


def _r0232_preimage_succ_uIcc_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_succ_uIcc_succ
    # succ ⁻¹' uIcc i.succ j.succ = uIcc i j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 4)
    if args is not None:
        try:
            rhs = OOp("uIcc", (OVar("i"), OVar("j"),))
            results.append((rhs, "Mathlib: Fin_preimage_succ_uIcc_succ"))
        except Exception:
            pass
    return results


def _r0233_preimage_succ_uIoc_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_succ_uIoc_succ
    # succ ⁻¹' uIoc i.succ j.succ = uIoc i j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 4)
    if args is not None:
        try:
            rhs = OOp("uIoc", (OVar("i"), OVar("j"),))
            results.append((rhs, "Mathlib: Fin_preimage_succ_uIoc_succ"))
        except Exception:
            pass
    return results


def _r0234_preimage_succ_uIoo_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_succ_uIoo_succ
    # succ ⁻¹' uIoo i.succ j.succ = uIoo i j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 4)
    if args is not None:
        try:
            rhs = OOp("uIoo", (OVar("i"), OVar("j"),))
            results.append((rhs, "Mathlib: Fin_preimage_succ_uIoo_succ"))
        except Exception:
            pass
    return results


def _r0235_image_succ_Ici(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_succ_Ici
    # succ '' Ici i = Ici i.succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 3)
    if args is not None:
        try:
            rhs = OOp("Ici", (OVar("i_succ"),))
            results.append((rhs, "Mathlib: Fin_image_succ_Ici"))
        except Exception:
            pass
    return results


def _r0236_image_succ_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_succ_Ioi
    # succ '' Ioi i = Ioi i.succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 3)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OVar("i_succ"),))
            results.append((rhs, "Mathlib: Fin_image_succ_Ioi"))
        except Exception:
            pass
    return results


def _r0237_image_succ_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_succ_Iic
    # succ '' Iic i = Ioc 0 i.succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 3)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OLit(0), OVar("i_succ"),))
            results.append((rhs, "Mathlib: Fin_image_succ_Iic"))
        except Exception:
            pass
    return results


def _r0238_image_succ_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_succ_Ico
    # succ '' Ico i j = Ico i.succ j.succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 4)
    if args is not None:
        try:
            rhs = OOp("Ico", (OVar("i_succ"), OVar("j_succ"),))
            results.append((rhs, "Mathlib: Fin_image_succ_Ico"))
        except Exception:
            pass
    return results


def _r0239_image_succ_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_succ_Ioc
    # succ '' Ioc i j = Ioc i.succ j.succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 4)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OVar("i_succ"), OVar("j_succ"),))
            results.append((rhs, "Mathlib: Fin_image_succ_Ioc"))
        except Exception:
            pass
    return results


def _r0240_image_succ_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_succ_Ioo
    # succ '' Ioo i j = Ioo i.succ j.succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 4)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OVar("i_succ"), OVar("j_succ"),))
            results.append((rhs, "Mathlib: Fin_image_succ_Ioo"))
        except Exception:
            pass
    return results


def _r0241_image_succ_uIcc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_succ_uIcc
    # succ '' uIcc i j = uIcc i.succ j.succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 4)
    if args is not None:
        try:
            rhs = OOp("uIcc", (OVar("i_succ"), OVar("j_succ"),))
            results.append((rhs, "Mathlib: Fin_image_succ_uIcc"))
        except Exception:
            pass
    return results


def _r0242_image_succ_uIoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_succ_uIoc
    # succ '' uIoc i j = uIoc i.succ j.succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 4)
    if args is not None:
        try:
            rhs = OOp("uIoc", (OVar("i_succ"), OVar("j_succ"),))
            results.append((rhs, "Mathlib: Fin_image_succ_uIoc"))
        except Exception:
            pass
    return results


def _r0243_image_succ_uIoo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_succ_uIoo
    # succ '' uIoo i j = uIoo i.succ j.succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 4)
    if args is not None:
        try:
            rhs = OOp("uIoo", (OVar("i_succ"), OVar("j_succ"),))
            results.append((rhs, "Mathlib: Fin_image_succ_uIoo"))
        except Exception:
            pass
    return results


def _r0244_image_rev(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.image_rev
    # rev '' s = rev ⁻¹' s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rev", 2)
    if args is not None:
        try:
            rhs = OOp("rev", (OVar("inv_prime"), args[1],))
            results.append((rhs, "Mathlib: Fin_image_rev"))
        except Exception:
            pass
    return results


def _r0245_preimage_rev_Ici(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_rev_Ici
    # rev ⁻¹' Ici i = Iic i.rev
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rev", 3)
    if args is not None:
        try:
            rhs = OOp("Iic", (OVar("i_rev"),))
            results.append((rhs, "Mathlib: Fin_preimage_rev_Ici"))
        except Exception:
            pass
    return results


def _r0246_preimage_rev_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_rev_Ioi
    # rev ⁻¹' Ioi i = Iio i.rev
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rev", 3)
    if args is not None:
        try:
            rhs = OOp("Iio", (OVar("i_rev"),))
            results.append((rhs, "Mathlib: Fin_preimage_rev_Ioi"))
        except Exception:
            pass
    return results


def _r0247_preimage_rev_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_rev_Iic
    # rev ⁻¹' Iic i = Ici i.rev
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rev", 3)
    if args is not None:
        try:
            rhs = OOp("Ici", (OVar("i_rev"),))
            results.append((rhs, "Mathlib: Fin_preimage_rev_Iic"))
        except Exception:
            pass
    return results


def _r0248_preimage_rev_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_rev_Iio
    # rev ⁻¹' Iio i = Ioi i.rev
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rev", 3)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OVar("i_rev"),))
            results.append((rhs, "Mathlib: Fin_preimage_rev_Iio"))
        except Exception:
            pass
    return results


def _r0249_preimage_rev_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_rev_Icc
    # rev ⁻¹' Icc i j = Icc j.rev i.rev
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rev", 4)
    if args is not None:
        try:
            rhs = OOp("Icc", (OVar("j_rev"), OVar("i_rev"),))
            results.append((rhs, "Mathlib: Fin_preimage_rev_Icc"))
        except Exception:
            pass
    return results


def _r0250_preimage_rev_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_rev_Ioo
    # rev ⁻¹' Ioo i j = Ioo j.rev i.rev
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rev", 4)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OVar("j_rev"), OVar("i_rev"),))
            results.append((rhs, "Mathlib: Fin_preimage_rev_Ioo"))
        except Exception:
            pass
    return results


def _r0251_preimage_rev_uIcc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_rev_uIcc
    # rev ⁻¹' uIcc i j = uIcc i.rev j.rev
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rev", 4)
    if args is not None:
        try:
            rhs = OOp("uIcc", (OVar("i_rev"), OVar("j_rev"),))
            results.append((rhs, "Mathlib: Fin_preimage_rev_uIcc"))
        except Exception:
            pass
    return results


def _r0252_preimage_rev_uIoo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.preimage_rev_uIoo
    # rev ⁻¹' uIoo i j = uIoo i.rev j.rev
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rev", 4)
    if args is not None:
        try:
            rhs = OOp("uIoo", (OVar("i_rev"), OVar("j_rev"),))
            results.append((rhs, "Mathlib: Fin_preimage_rev_uIoo"))
        except Exception:
            pass
    return results


def _r0253_eq_pow_of_mul_eq_pow_odd_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.eq_pow_of_mul_eq_pow_odd_left
    # ∃ d, a = d ^ k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], OVar("k")))
            results.append((rhs, "Mathlib: Int_eq_pow_of_mul_eq_pow_odd_left"))
        except Exception:
            pass
    return results


def _r0254_emultiplicity_natAbs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.emultiplicity_natAbs
    # emultiplicity a b.natAbs = emultiplicity (a : ℤ) b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "emultiplicity", 2)
    if args is not None:
        try:
            rhs = OOp("emultiplicity", (OOp("a", (OVar("colon"), OVar("_unknown"),)), OVar("b"),))
            results.append((rhs, "Mathlib: Int_emultiplicity_natAbs"))
        except Exception:
            pass
    return results


def _r0255_dens_eq_sum_dens_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.dens_eq_sum_dens_image
    # t.dens = ∑ a ∈ t.image f, {b ∈ t | f b = a}.dens
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("t_dens")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("a"),)), OOp("t_image", (OVar("f"), OVar("b_in_t_pipe_f_b_eq_a_dens"),))))
            results.append((rhs, "Mathlib: Finset_dens_eq_sum_dens_image"))
    except Exception:
        pass
    return results


def _r0256_prod_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_range
    # ∏ i ∈ Finset.range n, f i = ∏ i : Fin n, f i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), OVar("colon"), OVar("Fin"), OVar("n"), OVar("f"), OVar("i"),))
            results.append((rhs, "Mathlib: Finset_prod_range"))
        except Exception:
            pass
    return results


def _r0257_prod_univ_succAbove(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.prod_univ_succAbove
    # ∏ i, f i = f x * ∏ i : Fin n, f (x.succAbove i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("f", (OVar("x"),)), OOp("_unknown", (args[2], OVar("colon"), OVar("Fin"), OVar("n"), args[1], OOp("x_succAbove", (args[2],)),))))
            results.append((rhs, "Mathlib: Fin_prod_univ_succAbove"))
        except Exception:
            pass
    return results


def _r0258_prod_univ_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.prod_univ_succ
    # ∏ i, f i = f 0 * ∏ i : Fin n, f i.succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("f", (OLit(0),)), OOp("_unknown", (args[2], OVar("colon"), OVar("Fin"), OVar("n"), args[1], OVar("i_succ"),))))
            results.append((rhs, "Mathlib: Fin_prod_univ_succ"))
        except Exception:
            pass
    return results


def _r0259_prod_univ_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.prod_univ_getElem
    # ∏ i : Fin l.length, l[i.1] = l.prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 5)
    if args is not None:
        try:
            rhs = OVar("l_prod")
            results.append((rhs, "Mathlib: Fin_prod_univ_getElem"))
        except Exception:
            pass
    return results


def _r0260_prod_fintype(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.prod_fintype
    # f.prod g = ∏ i, g i (f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_prod", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), args[0], OVar("i"), OOp("f", (OVar("i"),)),))
            results.append((rhs, "Mathlib: Finsupp_prod_fintype"))
        except Exception:
            pass
    return results


def _r0261_sum_ite_self_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.sum_ite_self_eq
    # (f.sum fun x v => ite (a = x) v 0) = f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_sum", 8)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("a"),))
            results.append((rhs, "Mathlib: Finsupp_sum_ite_self_eq"))
        except Exception:
            pass
    return results


def _r0262_prod_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.prod_pow
    # (f.prod fun a b => g a ^ b) = ∏ a, g a ^ f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("_unknown", (OVar("a"), OVar("g"), OVar("a"),)), OOp("f", (OVar("a"),))))
            results.append((rhs, "Mathlib: Finsupp_prod_pow"))
        except Exception:
            pass
    return results


def _r0263_onFinset_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.onFinset_prod
    # (onFinset s f hf).prod g = ∏ a ∈ s, g a (f a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "onFinset_s_f_hf_prod", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("a"),)), OOp("s", (args[0], OVar("a"), OOp("f", (OVar("a"),)),))))
            results.append((rhs, "Mathlib: Finsupp_onFinset_prod"))
        except Exception:
            pass
    return results


def _r0264_mul_prod_erase(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.mul_prod_erase
    # g y (f y) * (erase y f).prod g = f.prod g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("f_prod", (OVar("g"),))
            results.append((rhs, "Mathlib: Finsupp_mul_prod_erase"))
        except Exception:
            pass
    return results


def _r0265_prod_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.prod_congr
    # f.prod g1 = f.prod g2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_prod", 1)
    if args is not None:
        try:
            rhs = OOp("f_prod", (OVar("g2"),))
            results.append((rhs, "Mathlib: Finsupp_prod_congr"))
        except Exception:
            pass
    return results


def _r0266_prod_eq_single(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.prod_eq_single
    # f.prod g = g a (f a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_prod", 1)
    if args is not None:
        try:
            rhs = OOp("g", (OVar("a"), OOp("f", (OVar("a"),)),))
            results.append((rhs, "Mathlib: Finsupp_prod_eq_single"))
        except Exception:
            pass
    return results


def _r0267_prod_unique(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.prod_unique
    # f.prod g = g default (f default)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_prod", 1)
    if args is not None:
        try:
            rhs = OOp("g", (OVar("default"), OOp("f", (OVar("default"),)),))
            results.append((rhs, "Mathlib: Finsupp_prod_unique"))
        except Exception:
            pass
    return results


def _r0268_single_multiset_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.single_multiset_sum
    # single a s.sum = (s.map (single a)).sum
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "single", 2)
    if args is not None:
        try:
            rhs = OVar("s_map_single_a_sum")
            results.append((rhs, "Mathlib: Finsupp_single_multiset_sum"))
        except Exception:
            pass
    return results


def _r0269_single_finset_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.single_finset_sum
    # single a (∑ b ∈ s, f b) = ∑ b ∈ s, single a (f b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "single", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("b"),)), OOp("s", (OVar("single"), args[0], OOp("f", (OVar("b"),)),))))
            results.append((rhs, "Mathlib: Finsupp_single_finset_sum"))
        except Exception:
            pass
    return results


def _r0270_single_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.single_sum
    # single a (s.sum f) = s.sum fun d c => single a (f d c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "single", 2)
    if args is not None:
        try:
            rhs = OOp("s_sum", (OVar("fun"), OVar("d"), OVar("c"), OVar("eq_gt"), OVar("single"), args[0], OOp("f", (OVar("d"), OVar("c"),)),))
            results.append((rhs, "Mathlib: Finsupp_single_sum"))
        except Exception:
            pass
    return results


def _r0271_finset_sum_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.finset_sum_apply
    # (∑ i ∈ S, f i) a = ∑ i ∈ S, f i a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_in_S_f_i", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("S", (OVar("f"), OVar("i"), args[0],))))
            results.append((rhs, "Mathlib: Finsupp_finset_sum_apply"))
        except Exception:
            pass
    return results


def _r0272_sum_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.sum_apply
    # (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_sum_g", 1)
    if args is not None:
        try:
            rhs = OOp("f_sum", (OVar("fun"), OVar("a_1"), OVar("b"), OVar("eq_gt"), OVar("g"), OVar("a_1"), OVar("b"), args[0],))
            results.append((rhs, "Mathlib: Finsupp_sum_apply"))
        except Exception:
            pass
    return results


def _r0273_coe_finset_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.coe_finset_sum
    # ⇑(∑ i ∈ S, f i) = ∑ i ∈ S, ⇑(f i)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("i_in_S_f_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("S", (OVar("f_i"),))))
            results.append((rhs, "Mathlib: Finsupp_coe_finset_sum"))
    except Exception:
        pass
    return results


def _r0274_prod_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.prod_mul
    # (f.prod fun a b => h₁ a b * h₂ a b) = f.prod h₁ * f.prod h₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("f_prod", (OVar("h_1"),)), OOp("f_prod", (OVar("h_2"),))))
            results.append((rhs, "Mathlib: Finsupp_prod_mul"))
        except Exception:
            pass
    return results


def _r0275_liftAddHom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.liftAddHom_apply
    # (liftAddHom (α := α) (M := M) (N := N)) F f = f.sum fun x => F x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "liftAddHom_a_colon_eq_a_M_colon_eq_M_N_colon_eq_N", 2)
    if args is not None:
        try:
            rhs = OOp("f_sum", (OVar("fun"), OVar("x"), OVar("eq_gt"), args[0], OVar("x"),))
            results.append((rhs, "Mathlib: Finsupp_liftAddHom_apply"))
        except Exception:
            pass
    return results


def _r0276_liftAddHom_symm_apply_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.liftAddHom_symm_apply_apply
    # (liftAddHom (α := α) (M := M) (N := N)).symm F x y = F (single x y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "liftAddHom_a_colon_eq_a_M_colon_eq_M_N_colon_eq_N_symm", 3)
    if args is not None:
        try:
            rhs = OOp("F", (OOp("single", (args[1], args[2],)),))
            results.append((rhs, "Mathlib: Finsupp_liftAddHom_symm_apply_apply"))
        except Exception:
            pass
    return results


def _r0277_sum_single(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.sum_single
    # f.sum single = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_sum", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Finsupp_sum_single"))
        except Exception:
            pass
    return results


def _r0278_univ_sum_single(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.univ_sum_single
    # ∑ a : α, single a (f a) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 6)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Finsupp_univ_sum_single"))
        except Exception:
            pass
    return results


def _r0279_univ_sum_single_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.univ_sum_single_apply
    # ∑ j : α, single i m j = m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 7)
    if args is not None:
        try:
            rhs = args[5]
            results.append((rhs, "Mathlib: Finsupp_univ_sum_single_apply"))
        except Exception:
            pass
    return results


def _r0280_sum_single_add_single(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.sum_single_add_single
    # sum (single f₁ g₁ + single f₂ g₂) F = F f₁ g₁ + F f₂ g₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sum", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("F", (OVar("f_1"), OVar("g_1"),)), OOp("F", (OVar("f_2"), OVar("g_2"),))))
            results.append((rhs, "Mathlib: Finsupp_sum_single_add_single"))
        except Exception:
            pass
    return results


def _r0281_equivFunOnFinite_symm_eq_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.equivFunOnFinite_symm_eq_sum
    # equivFunOnFinite.symm f = ∑ a, single a (f a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "equivFunOnFinite_symm", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("a"), OVar("single"), OVar("a"), OOp("f", (OVar("a"),)),))
            results.append((rhs, "Mathlib: Finsupp_equivFunOnFinite_symm_eq_sum"))
        except Exception:
            pass
    return results


def _r0282_coe_univ_sum_single(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.coe_univ_sum_single
    # ⇑(∑ a : α, single a (f a)) = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_colon_a_single_a_f_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Finsupp_coe_univ_sum_single"))
    except Exception:
        pass
    return results


def _r0283_equivFunOnFinite_symm_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.equivFunOnFinite_symm_sum
    # ((equivFunOnFinite.symm f).sum fun _ n ↦ n) = ∑ a, f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "equivFunOnFinite_symm_f_sum", 5)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("a"), OVar("f"), OVar("a"),))
            results.append((rhs, "Mathlib: Finsupp_equivFunOnFinite_symm_sum"))
        except Exception:
            pass
    return results


def _r0284_liftAddHom_apply_single(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.liftAddHom_apply_single
    # (liftAddHom (α := α) (M := M) (N := N)) f (single a b) = f a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "liftAddHom_a_colon_eq_a_M_colon_eq_M_N_colon_eq_N", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Finsupp_liftAddHom_apply_single"))
        except Exception:
            pass
    return results


def _r0285_prod_embDomain(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.prod_embDomain
    # (v.embDomain f).prod g = v.prod fun a b => g (f a) b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "v_embDomain_f_prod", 1)
    if args is not None:
        try:
            rhs = OOp("v_prod", (OVar("fun"), OVar("a"), OVar("b"), OVar("eq_gt"), args[0], OOp("f", (OVar("a"),)), OVar("b"),))
            results.append((rhs, "Mathlib: Finsupp_prod_embDomain"))
        except Exception:
            pass
    return results


def _r0286_multiset_sum_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.multiset_sum_sum
    # Multiset.sum (f.sum h) = f.sum fun a b => Multiset.sum (h a b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sum", 1)
    if args is not None:
        try:
            rhs = OOp("f_sum", (OVar("fun"), OVar("a"), OVar("b"), OVar("eq_gt"), OVar("Multiset_sum"), OOp("h", (OVar("a"), OVar("b"),)),))
            results.append((rhs, "Mathlib: Finsupp_multiset_sum_sum"))
        except Exception:
            pass
    return results


def _r0287_sum_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.sum_mul
    # s.sum f * b = s.sum fun a c => f a c * b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("s_sum", (OVar("fun"), OVar("a"), OVar("c"), OVar("eq_gt"), OVar("f"), OVar("a"), OVar("c"),)), args[1]))
            results.append((rhs, "Mathlib: Finsupp_sum_mul"))
        except Exception:
            pass
    return results


def _r0288_mul_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.mul_sum
    # b * s.sum f = s.sum fun a c => b * f a c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("s_sum", (OVar("fun"), OVar("a"), OVar("c"), OVar("eq_gt"), args[0],)), OOp("f", (OVar("a"), OVar("c"),))))
            results.append((rhs, "Mathlib: Finsupp_mul_sum"))
        except Exception:
            pass
    return results


def _r0289_ofSupportFinite_fin_two_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.ofSupportFinite_fin_two_eq
    # ofSupportFinite ![n 0, n 1] (Set.toFinite _) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofSupportFinite", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Finsupp_ofSupportFinite_fin_two_eq"))
        except Exception:
            pass
    return results


def _r0290_prod_unique(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.prod_unique
    # ∏ x : ι, f x = f default
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 5)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("default"),))
            results.append((rhs, "Mathlib: Fintype_prod_unique"))
        except Exception:
            pass
    return results


def _r0291_prod_eq_prod_range_intervalGapsWithin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_eq_prod_range_intervalGapsWithin
    # ∏ z ∈ F, f z.1 z.2 = ∏ i ∈ range k,       f (F.intervalGapsWithin h a b i).2 (F.intervalGapsWithin h a b i.succ).1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("range", (OVar("k"), OVar("f"), OVar("F_intervalGapsWithin_h_a_b_i_2"), OVar("F_intervalGapsWithin_h_a_b_i_succ_1"),))))
            results.append((rhs, "Mathlib: Finset_prod_eq_prod_range_intervalGapsWithin"))
        except Exception:
            pass
    return results


def _r0292_prod_Icc_succ_eq_mul_endpoints(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_Icc_succ_eq_mul_endpoints
    # ∏ m ∈ Icc (-(N + 1) : ℤ) (N + 1), f m =     f (N + 1) * f (-(N + 1) : ℤ) * ∏ m ∈ Icc (-N : ℤ) N, f m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("f", (OOp("+", (OVar("N"), OLit(1))),)), OOp("*", (OOp("f", (OOp("minus_N_plus_1", (OVar("colon"), OVar("_unknown"),)),)), OOp("in", (OOp("_unknown", (OVar("m"),)), OOp("Icc", (OOp("minus_N", (OVar("colon"), OVar("_unknown"),)), OVar("N"), OVar("f"), OVar("m"),))))))))
            results.append((rhs, "Mathlib: Finset_prod_Icc_succ_eq_mul_endpoints"))
        except Exception:
            pass
    return results


def _r0293_prod_pi_mulSingle(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_pi_mulSingle
    # (∏ a' ∈ s, Pi.mulSingle a' (f a') a) = if a ∈ s then f a else 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("if", (OVar("a"),)), OOp("s", (OVar("then"), OVar("f"), OVar("a"), OVar("else"), OLit(1),))))
            results.append((rhs, "Mathlib: Finset_prod_pi_mulSingle"))
        except Exception:
            pass
    return results


def _r0294_prod_pow_boole(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_pow_boole
    # (∏ x ∈ s, f x ^ ite (a = x) 1 0) = ite (a ∈ s) (f a) 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("ite", (OOp("in", (OVar("a"), OVar("s"))), OOp("f", (OVar("a"),)), OLit(1),))
            results.append((rhs, "Mathlib: Finset_prod_pow_boole"))
        except Exception:
            pass
    return results


def _r0295_prod_pi_mulSingle(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.prod_pi_mulSingle
    # ∏ j, Pi.mulSingle j (f j) i = f i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 5)
    if args is not None:
        try:
            rhs = OOp("f", (args[4],))
            results.append((rhs, "Mathlib: Fintype_prod_pi_mulSingle"))
        except Exception:
            pass
    return results


def _r0296_prod_preimage(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_preimage
    # ∏ x ∈ s.preimage f hf, g (f x) = ∏ x ∈ s, g x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("s", (OVar("g"), OVar("x"),))))
            results.append((rhs, "Mathlib: Finset_prod_preimage"))
        except Exception:
            pass
    return results


def _r0297_prod_boole(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_boole
    # ∏ i ∈ s, (ite (p i) 1 0 : M₀) = ite (∀ i ∈ s, p i) 1 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("ite", (OOp("in", (OOp("forall", (OVar("i"),)), OOp("s", (OVar("p"), OVar("i"),)))), OLit(1), OLit(0),))
            results.append((rhs, "Mathlib: Finset_prod_boole"))
        except Exception:
            pass
    return results


def _r0298_prod_boole(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.prod_boole
    # ∏ i, (ite (p i) 1 0 : M₀) = ite (∀ i, p i) 1 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 2)
    if args is not None:
        try:
            rhs = OOp("ite", (OOp("forall", (args[0], OVar("p"), args[0],)), OLit(1), OLit(0),))
            results.append((rhs, "Mathlib: Fintype_prod_boole"))
        except Exception:
            pass
    return results


def _r0299_prod_Ico_succ_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_Ico_succ_top
    # (∏ k ∈ Ico a (b + 1), f k) = (∏ k ∈ Ico a b, f k) * f b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("in", (OOp("_unknown", (OVar("k"),)), OOp("Ico", (OVar("a"), OVar("b"), OVar("f"), OVar("k"),)))), OOp("f", (OVar("b"),))))
            results.append((rhs, "Mathlib: Finset_prod_Ico_succ_top"))
        except Exception:
            pass
    return results


def _r0300_prod_Ioc_succ_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_Ioc_succ_top
    # (∏ k ∈ Ioc a (b + 1), f k) = (∏ k ∈ Ioc a b, f k) * f (b + 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("in", (OOp("_unknown", (OVar("k"),)), OOp("Ioc", (OVar("a"), OVar("b"), OVar("f"), OVar("k"),)))), OOp("f", (OOp("+", (OVar("b"), OLit(1))),))))
            results.append((rhs, "Mathlib: Finset_prod_Ioc_succ_top"))
        except Exception:
            pass
    return results


def _r0301_prod_Icc_succ_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_Icc_succ_top
    # (∏ k ∈ Icc a (b + 1), f k) = (∏ k ∈ Icc a b, f k) * f (b + 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("in", (OOp("_unknown", (OVar("k"),)), OOp("Icc", (OVar("a"), OVar("b"), OVar("f"), OVar("k"),)))), OOp("f", (OOp("+", (OVar("b"), OLit(1))),))))
            results.append((rhs, "Mathlib: Finset_prod_Icc_succ_top"))
        except Exception:
            pass
    return results


def _r0302_prod_Ico_reflect(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_Ico_reflect
    # (∏ j ∈ Ico k m, f (n - j)) = ∏ j ∈ Ico (n + 1 - m) (n + 1 - k), f j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("j"),)), OOp("Ico", (OOp("+", (OVar("n"), OOp("-", (OLit(1), OVar("m"))))), OVar("n_plus_1_minus_k"), OVar("f"), OVar("j"),))))
            results.append((rhs, "Mathlib: Finset_prod_Ico_reflect"))
        except Exception:
            pass
    return results


def _r0303_sum_Ico_reflect(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.sum_Ico_reflect
    # (∑ j ∈ Ico k m, f (n - j)) = ∑ j ∈ Ico (n + 1 - m) (n + 1 - k), f j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("j"),)), OOp("Ico", (OOp("+", (OVar("n"), OOp("-", (OLit(1), OVar("m"))))), OVar("n_plus_1_minus_k"), OVar("f"), OVar("j"),))))
            results.append((rhs, "Mathlib: Finset_sum_Ico_reflect"))
        except Exception:
            pass
    return results


def _r0304_prod_range_reflect(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_range_reflect
    # (∏ j ∈ range n, f (n - 1 - j)) = ∏ j ∈ range n, f j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("j"),)), OOp("range", (OVar("n"), OVar("f"), OVar("j"),))))
            results.append((rhs, "Mathlib: Finset_prod_range_reflect"))
        except Exception:
            pass
    return results


def _r0305_sum_range_reflect(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.sum_range_reflect
    # (∑ j ∈ range n, f (n - 1 - j)) = ∑ j ∈ range n, f j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("j"),)), OOp("range", (OVar("n"), OVar("f"), OVar("j"),))))
            results.append((rhs, "Mathlib: Finset_sum_range_reflect"))
        except Exception:
            pass
    return results


def _r0306_prod_Iic_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.prod_Iic_div
    # ∏ i ∈ Iic a, (f i.succ / f i.castSucc) = f a.succ / f 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("f", (OVar("a_succ"),)), OOp("f", (OLit(0),))))
            results.append((rhs, "Mathlib: Fin_prod_Iic_div"))
        except Exception:
            pass
    return results


def _r0307_prod_Icc_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.prod_Icc_div
    # ∏ i ∈ Icc a b, (f i.succ / f i.castSucc) = f b.succ / f a.castSucc
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("f", (OVar("b_succ"),)), OOp("f", (OVar("a_castSucc"),))))
            results.append((rhs, "Mathlib: Fin_prod_Icc_div"))
        except Exception:
            pass
    return results


def _r0308_sum_range_by_parts(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.sum_range_by_parts
    # ∑ i ∈ range n, f i • g i =       f (n - 1) • G n - ∑ i ∈ range (n - 1), (f (i + 1) - f i) • G (i + 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("f", (OOp("-", (OVar("n"), OLit(1))), OVar("_unknown"), OVar("G"), OVar("n"),)), OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("range", (OVar("n_minus_1"), OOp("-", (OOp("f", (OOp("+", (OVar("i"), OLit(1))),)), OOp("f", (OVar("i"),)))), OVar("_unknown"), OVar("G"), OOp("+", (OVar("i"), OLit(1))),))))))
            results.append((rhs, "Mathlib: Finset_sum_range_by_parts"))
        except Exception:
            pass
    return results


def _r0309_prod_antidiagonal_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.Nat.prod_antidiagonal_succ
    # (∏ p ∈ antidiagonal (n + 1), f p)       = f (0, n + 1) * ∏ p ∈ antidiagonal n, f (p.1 + 1, p.2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("f", (OOp("+", (OOp("_0", (OVar("n"),)), OLit(1))),)), OOp("in", (OOp("_unknown", (OVar("p"),)), OOp("antidiagonal", (OVar("n"), OVar("f"), OOp("+", (OVar("p_1"), OOp("_1", (OVar("p_2"),)))),))))))
            results.append((rhs, "Mathlib: Finset_Nat_prod_antidiagonal_succ"))
        except Exception:
            pass
    return results


def _r0310_sum_antidiagonal_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.Nat.sum_antidiagonal_succ
    # (∑ p ∈ antidiagonal (n + 1), f p) = f (0, n + 1) + ∑ p ∈ antidiagonal n, f (p.1 + 1, p.2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("f", (OOp("+", (OOp("_0", (OVar("n"),)), OLit(1))),)), OOp("in", (OOp("_unknown", (OVar("p"),)), OOp("antidiagonal", (OVar("n"), OVar("f"), OOp("+", (OVar("p_1"), OOp("_1", (OVar("p_2"),)))),))))))
            results.append((rhs, "Mathlib: Finset_Nat_sum_antidiagonal_succ"))
        except Exception:
            pass
    return results


def _r0311_prod_antidiagonal_eq_prod_range_succ_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.Nat.prod_antidiagonal_eq_prod_range_succ_mk
    # ∏ ij ∈ antidiagonal n, f ij = ∏ k ∈ range n.succ, f (k, n - k)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("k"),)), OOp("range", (OVar("n_succ"), OVar("f"), OOp("-", (OOp("k", (OVar("n"),)), OVar("k"))),))))
            results.append((rhs, "Mathlib: Finset_Nat_prod_antidiagonal_eq_prod_range_succ_mk"))
        except Exception:
            pass
    return results


def _r0312_prod_antidiagonal_eq_prod_range_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.Nat.prod_antidiagonal_eq_prod_range_succ
    # ∏ ij ∈ antidiagonal n, f ij.1 ij.2 = ∏ k ∈ range n.succ, f k (n - k)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("k"),)), OOp("range", (OVar("n_succ"), OVar("f"), OVar("k"), OOp("-", (OVar("n"), OVar("k"))),))))
            results.append((rhs, "Mathlib: Finset_Nat_prod_antidiagonal_eq_prod_range_succ"))
        except Exception:
            pass
    return results


def _r0313_univ_prod_mulSingle(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.univ_prod_mulSingle
    # (∏ i, Pi.mulSingle i (f i)) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Finset_univ_prod_mulSingle"))
        except Exception:
            pass
    return results


def _r0314_sum_boole(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.sum_boole
    # (∑ x ∈ s, if p x then 1 else 0 : R) = #{x ∈ s | p x}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OVar("hash_x_in_s_pipe_p_x")
            results.append((rhs, "Mathlib: Finset_sum_boole"))
        except Exception:
            pass
    return results


def _r0315_coe_to_intFractPair(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GenContFract.IntFractPair.coe_to_intFractPair
    # (↑(IntFractPair.mk b fr) : IntFractPair β) = IntFractPair.mk b (↑fr : β)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IntFractPair_mk_b_fr", 3)
    if args is not None:
        try:
            rhs = OOp("IntFractPair_mk", (args[2], OOp("fr", (args[0], args[2],)),))
            results.append((rhs, "Mathlib: GenContFract_IntFractPair_coe_to_intFractPair"))
        except Exception:
            pass
    return results


def _r0316_stream_succ_of_some(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GenContFract.IntFractPair.stream_succ_of_some
    # IntFractPair.stream v (n + 1) = some (IntFractPair.of p.fr⁻¹)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IntFractPair_stream", 2)
    if args is not None:
        try:
            rhs = OOp("some", (OOp("IntFractPair_of", (OVar("p_frinv"),)),))
            results.append((rhs, "Mathlib: GenContFract_IntFractPair_stream_succ_of_some"))
        except Exception:
            pass
    return results


def _r0317_stream_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GenContFract.IntFractPair.stream_succ
    # IntFractPair.stream v (n + 1) = IntFractPair.stream (Int.fract v)⁻¹ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IntFractPair_stream", 2)
    if args is not None:
        try:
            rhs = OOp("IntFractPair_stream", (OVar("Int_fract_v_inv"), OVar("n"),))
            results.append((rhs, "Mathlib: GenContFract_IntFractPair_stream_succ"))
        except Exception:
            pass
    return results


def _r0318_seq1_fst_eq_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GenContFract.IntFractPair.seq1_fst_eq_of
    # (IntFractPair.seq1 v).fst = IntFractPair.of v
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("IntFractPair_seq1_v_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("IntFractPair_of", (OVar("v"),))
            results.append((rhs, "Mathlib: GenContFract_IntFractPair_seq1_fst_eq_of"))
    except Exception:
        pass
    return results


def _r0319_toFreeAbelianGroup_toFinsupp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.toFreeAbelianGroup_toFinsupp
    # Finsupp.toFreeAbelianGroup (FreeAbelianGroup.toFinsupp x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Finsupp_toFreeAbelianGroup", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Finsupp_toFreeAbelianGroup_toFinsupp"))
        except Exception:
            pass
    return results


def _r0320_lcm_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.lcm_image
    # (s.image g).lcm f = s.lcm (f ∘ g)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_image_g_lcm", 1)
    if args is not None:
        try:
            rhs = OOp("s_lcm", (OOp("comp", (args[0], OVar("g"))),))
            results.append((rhs, "Mathlib: Finset_lcm_image"))
        except Exception:
            pass
    return results


def _r0321_apply_single(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.apply_single
    # e (single i m b) = single i (e m) b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 1)
    if args is not None:
        try:
            rhs = OOp("single", (OVar("i"), OOp("e", (OVar("m"),)), OVar("b"),))
            results.append((rhs, "Mathlib: Finsupp_apply_single"))
        except Exception:
            pass
    return results


def _r0322_range_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.range_add
    # range (a + b) = range a ∪ (range b).map (addLeftEmbedding a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OOp("union", (OOp("range", (OVar("a"),)), OOp("range_b_map", (OOp("addLeftEmbedding", (OVar("a"),)),))))
            results.append((rhs, "Mathlib: Finset_range_add"))
        except Exception:
            pass
    return results


def _r0323_smul_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.smul_def
    # s • t = (s ×ˢ t).image fun p : α × β => p.1 • p.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OOp("product", (OOp("s_times_t_image", (OVar("fun"), OVar("p"), OVar("colon"), OVar("a"),)), OOp("b", (OVar("eq_gt"), OVar("p_1"), args[0], OVar("p_2"),))))
            results.append((rhs, "Mathlib: Finset_smul_def"))
        except Exception:
            pass
    return results


def _r0324_image_smul_product(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.image_smul_product
    # ((s ×ˢ t).image fun x : α × β => x.fst • x.snd) = s • t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "product", 2)
    if args is not None:
        try:
            rhs = OOp("s", (OVar("_unknown"), OVar("t"),))
            results.append((rhs, "Mathlib: Finset_image_smul_product"))
        except Exception:
            pass
    return results


def _r0325_smul_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.smul_singleton
    # s • ({b} : Finset β) = s.image (· • b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OOp("s_image", (OOp("_unknown", (args[0], OVar("b"),)),))
            results.append((rhs, "Mathlib: Finset_smul_singleton"))
        except Exception:
            pass
    return results


def _r0326_zmultiples_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.zmultiples_one
    # AddSubgroup.zmultiples (1 : ℤ) = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "AddSubgroup_zmultiples", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Int_zmultiples_one"))
        except Exception:
            pass
    return results


def _r0327_zmultiples_natAbs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.zmultiples_natAbs
    # AddSubgroup.zmultiples (a.natAbs : ℤ) = AddSubgroup.zmultiples a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "AddSubgroup_zmultiples", 1)
    if args is not None:
        try:
            rhs = OOp("AddSubgroup_zmultiples", (OVar("a"),))
            results.append((rhs, "Mathlib: Int_zmultiples_natAbs"))
        except Exception:
            pass
    return results


def _r0328_range_castAddHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.range_castAddHom
    # (castAddHom A).range = zmultiples 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("castAddHom_A_range")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("zmultiples", (OLit(1),))
            results.append((rhs, "Mathlib: Int_range_castAddHom"))
    except Exception:
        pass
    return results


def _r0329_range_nsmulAddMonoidHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.range_nsmulAddMonoidHom
    # (nsmulAddMonoidHom n).range = zmultiples (n : ℤ)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("nsmulAddMonoidHom_n_range")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("zmultiples", (OOp("n", (OVar("colon"), OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: Int_range_nsmulAddMonoidHom"))
    except Exception:
        pass
    return results


def _r0330_sum_single_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.sum_single_smul
    # ∑ i, (Pi.single (M := fun _ ↦ R) i₀ r i) • f i = r • f i₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 5)
    if args is not None:
        try:
            rhs = OOp("r", (args[2], args[3], OVar("i_0"),))
            results.append((rhs, "Mathlib: Fintype_sum_single_smul"))
        except Exception:
            pass
    return results


def _r0331_prod_eq_prod_Ico_succ_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_eq_prod_Ico_succ_bot
    # ∏ k ∈ Ico a b, f k = f a * ∏ k ∈ Ico (a + 1) b, f k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("f", (OVar("a"),)), OOp("in", (OOp("_unknown", (OVar("k"),)), OOp("Ico", (OOp("+", (OVar("a"), OLit(1))), OVar("b"), OVar("f"), OVar("k"),))))))
            results.append((rhs, "Mathlib: Finset_prod_eq_prod_Ico_succ_bot"))
        except Exception:
            pass
    return results


def _r0332_length_pure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Interval.length_pure
    # (pure a).length = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pure_a_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Interval_length_pure"))
    except Exception:
        pass
    return results


def _r0333_length_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Interval.length_zero
    # (0 : Interval α).length = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_Interval_a_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Interval_length_zero"))
    except Exception:
        pass
    return results


def _r0334_length_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Interval.length_bot
    # (⊥ : Interval α).length = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("bot_colon_Interval_a_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Interval_length_bot"))
    except Exception:
        pass
    return results


def _r0335_map_add_left_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.map_add_left_Icc
    # (Icc a b).map (addLeftEmbedding c) = Icc (c + a) (c + b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Icc_a_b_map", 1)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("+", (OVar("c"), OVar("a"))), OOp("+", (OVar("c"), OVar("b"))),))
            results.append((rhs, "Mathlib: Finset_map_add_left_Icc"))
        except Exception:
            pass
    return results


def _r0336_map_add_left_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.map_add_left_Ico
    # (Ico a b).map (addLeftEmbedding c) = Ico (c + a) (c + b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico_a_b_map", 1)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("+", (OVar("c"), OVar("a"))), OOp("+", (OVar("c"), OVar("b"))),))
            results.append((rhs, "Mathlib: Finset_map_add_left_Ico"))
        except Exception:
            pass
    return results


def _r0337_map_add_left_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.map_add_left_Ioc
    # (Ioc a b).map (addLeftEmbedding c) = Ioc (c + a) (c + b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioc_a_b_map", 1)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("+", (OVar("c"), OVar("a"))), OOp("+", (OVar("c"), OVar("b"))),))
            results.append((rhs, "Mathlib: Finset_map_add_left_Ioc"))
        except Exception:
            pass
    return results


def _r0338_map_add_left_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.map_add_left_Ioo
    # (Ioo a b).map (addLeftEmbedding c) = Ioo (c + a) (c + b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioo_a_b_map", 1)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OOp("+", (OVar("c"), OVar("a"))), OOp("+", (OVar("c"), OVar("b"))),))
            results.append((rhs, "Mathlib: Finset_map_add_left_Ioo"))
        except Exception:
            pass
    return results


def _r0339_image_add_left_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.image_add_left_Icc
    # (Icc a b).image (c + ·) = Icc (c + a) (c + b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Icc_a_b_image", 1)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("+", (OVar("c"), OVar("a"))), OOp("+", (OVar("c"), OVar("b"))),))
            results.append((rhs, "Mathlib: Finset_image_add_left_Icc"))
        except Exception:
            pass
    return results


def _r0340_mul_sup_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.mul_sup₀
    # a * s.sup f = s.sup (a * f ·)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("s_sup", (OOp("*", (args[0], OOp("f", (OVar("_unknown"),)))),))
            results.append((rhs, "Mathlib: Finset_mul_sup_0"))
        except Exception:
            pass
    return results


def _r0341_sup_mul_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.sup_mul₀
    # s.sup f * a = s.sup (f · * a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("s_sup", (OOp("*", (OOp("f", (OVar("_unknown"),)), args[1])),))
            results.append((rhs, "Mathlib: Finset_sup_mul_0"))
        except Exception:
            pass
    return results


def _r0342_exists_add_mul_eq_of_gcd_dvd_of_mul_pred(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le
    # ∃ a b : ℕ, a * p + b * q = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Nat_exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le"))
        except Exception:
            pass
    return results


def _r0343_mk_add_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.FiniteElement.mk_add_mk
    # .mk x hx + .mk y hy = FiniteElement.mk (x + y) ((le_min hx hy).trans <| min_le_mk_add ..)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("FiniteElement_mk", (OOp("+", (OVar("x"), OVar("y"))), OOp("le_min_hx_hy_trans", (OVar("lt_pipe"), OVar("min_le_mk_add"), OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: ArchimedeanClass_FiniteElement_mk_add_mk"))
        except Exception:
            pass
    return results


def _r0344_geomSum_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.geomSum_eq
    # ∑ k ∈ range n, m ^ k = (m ^ n - 1) / (m - 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("-", (OOp("**", (OVar("m"), OVar("n"))), OLit(1))), OOp("-", (OVar("m"), OLit(1)))))
            results.append((rhs, "Mathlib: Nat_geomSum_eq"))
        except Exception:
            pass
    return results


def _r0345_natCast_pow_pred(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.natCast_pow_pred
    # ((b ^ p - 1 : ℕ) : ℤ) = (b : ℤ) ^ p - 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "b_pow_p_minus_1_colon", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("**", (OOp("b", (args[0], args[1],)), OVar("p"))), OLit(1)))
            results.append((rhs, "Mathlib: Int_natCast_pow_pred"))
        except Exception:
            pass
    return results


def _r0346_coe_nat_two_pow_pred(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.coe_nat_two_pow_pred
    # ((2 ^ p - 1 : ℕ) : ℤ) = (2 ^ p - 1 : ℤ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_2_pow_p_minus_1_colon", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("**", (OLit(2), OVar("p"))), OOp("_1", (args[0], args[1],))))
            results.append((rhs, "Mathlib: Int_coe_nat_two_pow_pred"))
        except Exception:
            pass
    return results


def _r0347_mod_two_add_succ_mod_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.mod_two_add_succ_mod_two
    # m % 2 + (m + 1) % 2 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Nat_mod_two_add_succ_mod_two"))
        except Exception:
            pass
    return results


def _r0348_trop_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.trop_inf
    # trop (s.inf f) = ∑ i ∈ s, trop (f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "trop", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("trop"), OOp("f", (OVar("i"),)),))))
            results.append((rhs, "Mathlib: Finset_trop_inf"))
        except Exception:
            pass
    return results


def _r0349_sum_integral_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BoxIntegral.Integrable.sum_integral_congr
    # ∑ J ∈ π₁.boxes, integral J l f vol = ∑ J ∈ π₂.boxes, integral J l f vol
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("J"),)), OOp("pi_2_boxes", (OVar("integral"), OVar("J"), OVar("l"), OVar("f"), OVar("vol"),))))
            results.append((rhs, "Mathlib: BoxIntegral_Integrable_sum_integral_congr"))
        except Exception:
            pass
    return results


def _r0350_isCauSeq_norm_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.isCauSeq_norm_exp
    # IsCauSeq abs fun n => ∑ m ∈ range n, ‖z ^ m / m.factorial‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsCauSeq", 3)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("in", (OOp("gt", (OVar("_unknown"), OVar("m"),)), OOp("**", (OOp("range", (args[2], OVar("z"),)), OVar("m"))))), OVar("m_factorial")))
            results.append((rhs, "Mathlib: Complex_isCauSeq_norm_exp"))
        except Exception:
            pass
    return results


def _r0351_isCauSeq_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.isCauSeq_exp
    # IsCauSeq (‖·‖) fun n => ∑ m ∈ range n, z ^ m / m.factorial
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsCauSeq", 3)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("in", (OOp("gt", (args[0], OVar("m"),)), OOp("**", (OOp("range", (args[2], OVar("z"),)), OVar("m"))))), OVar("m_factorial")))
            results.append((rhs, "Mathlib: Complex_isCauSeq_exp"))
        except Exception:
            pass
    return results


def _r0352_exp_multiset_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.exp_multiset_sum
    # exp s.sum = (s.map exp).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exp", 1)
    if args is not None:
        try:
            rhs = OVar("s_map_exp_prod")
            results.append((rhs, "Mathlib: Complex_exp_multiset_sum"))
        except Exception:
            pass
    return results


def _r0353_integerComplement_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.integerComplement_eq
    # ℂ_ℤ = {z : ℂ | ¬ ∃ (n : ℤ), n = z}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_unknown")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("z_colon_pipe_not_exists_n_colon_n_eq_z")
            results.append((rhs, "Mathlib: Complex_integerComplement_eq"))
    except Exception:
        pass
    return results


def _r0354_mem_integerComplement_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.mem_integerComplement_iff
    # x ∈ ℂ_ℤ ↔ ¬ ∃ (n : ℤ), n = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Complex_mem_integerComplement_iff"))
        except Exception:
            pass
    return results


def _r0355_upperHalfPlane_inter_integerComplement(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.upperHalfPlane_inter_integerComplement
    # {z : ℂ | 0 < z.im} ∩ ℂ_ℤ = {z : ℂ | 0 < z.im}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Complex_upperHalfPlane_inter_integerComplement"))
        except Exception:
            pass
    return results


def _r0356_lt_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.lt_def
    # z < w ↔ z.re < w.re ∧ z.im = w.im
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OVar("w_im")
            results.append((rhs, "Mathlib: Complex_lt_def"))
        except Exception:
            pass
    return results


def _r0357_interior_preimage_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.interior_preimage_re
    # interior (re ⁻¹' s) = re ⁻¹' interior s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "interior", 1)
    if args is not None:
        try:
            rhs = OOp("re", (OVar("inv_prime"), OVar("interior"), OVar("s"),))
            results.append((rhs, "Mathlib: Complex_interior_preimage_re"))
        except Exception:
            pass
    return results


def _r0358_interior_preimage_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.interior_preimage_im
    # interior (im ⁻¹' s) = im ⁻¹' interior s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "interior", 1)
    if args is not None:
        try:
            rhs = OOp("im", (OVar("inv_prime"), OVar("interior"), OVar("s"),))
            results.append((rhs, "Mathlib: Complex_interior_preimage_im"))
        except Exception:
            pass
    return results


def _r0359_closure_preimage_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.closure_preimage_re
    # closure (re ⁻¹' s) = re ⁻¹' closure s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OOp("re", (OVar("inv_prime"), OVar("closure"), OVar("s"),))
            results.append((rhs, "Mathlib: Complex_closure_preimage_re"))
        except Exception:
            pass
    return results


def _r0360_closure_preimage_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.closure_preimage_im
    # closure (im ⁻¹' s) = im ⁻¹' closure s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OOp("im", (OVar("inv_prime"), OVar("closure"), OVar("s"),))
            results.append((rhs, "Mathlib: Complex_closure_preimage_im"))
        except Exception:
            pass
    return results


def _r0361_frontier_preimage_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.frontier_preimage_re
    # frontier (re ⁻¹' s) = re ⁻¹' frontier s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "frontier", 1)
    if args is not None:
        try:
            rhs = OOp("re", (OVar("inv_prime"), OVar("frontier"), OVar("s"),))
            results.append((rhs, "Mathlib: Complex_frontier_preimage_re"))
        except Exception:
            pass
    return results


def _r0362_frontier_preimage_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.frontier_preimage_im
    # frontier (im ⁻¹' s) = im ⁻¹' frontier s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "frontier", 1)
    if args is not None:
        try:
            rhs = OOp("im", (OVar("inv_prime"), OVar("frontier"), OVar("s"),))
            results.append((rhs, "Mathlib: Complex_frontier_preimage_im"))
        except Exception:
            pass
    return results


def _r0363_tsum_eq_tsum_fourier(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.tsum_eq_tsum_fourier
    # ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 (f : ℝ → ℂ) n * fourier n (x : UnitAddCircle)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prime", 5)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("prime", (args[0], args[1], args[2], args[2], OOp("implies", (OOp("f", (args[1], args[2],)), args[2])), args[0],)), OOp("fourier", (args[0], OOp("x", (args[1], OVar("UnitAddCircle"),)),))))
            results.append((rhs, "Mathlib: Real_tsum_eq_tsum_fourier"))
        except Exception:
            pass
    return results


def _r0364_tsum_eq_tsum_fourier_of_rpow_decay_of_su(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    # ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 f n * fourier n (x : UnitAddCircle)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prime", 5)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("prime", (args[0], args[1], args[2], args[2], args[3], args[0],)), OOp("fourier", (args[0], OOp("x", (args[1], OVar("UnitAddCircle"),)),))))
            results.append((rhs, "Mathlib: Real_tsum_eq_tsum_fourier_of_rpow_decay_of_summable"))
        except Exception:
            pass
    return results


def _r0365_tsum_eq_tsum_fourier_of_rpow_decay(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.tsum_eq_tsum_fourier_of_rpow_decay
    # ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 f n * fourier n (x : UnitAddCircle)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prime", 5)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("prime", (args[0], args[1], args[2], args[2], args[3], args[0],)), OOp("fourier", (args[0], OOp("x", (args[1], OVar("UnitAddCircle"),)),))))
            results.append((rhs, "Mathlib: Real_tsum_eq_tsum_fourier_of_rpow_decay"))
        except Exception:
            pass
    return results


def _r0366_sum_inner(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.sum_inner
    # ⟪l.sum v, x⟫ = l.sum fun (i : ι) (a : M) ↦ ⟪v i a, x⟫
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_sum", 2)
    if args is not None:
        try:
            rhs = OOp("l_sum", (OVar("fun"), OOp("i", (OVar("colon"), OVar("i"),)), OOp("a", (OVar("colon"), OVar("M"),)), OVar("_unknown"), args[0], OVar("i"), OVar("a"), args[1],))
            results.append((rhs, "Mathlib: Finsupp_sum_inner"))
        except Exception:
            pass
    return results


def _r0367_inner_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.inner_sum
    # ⟪x, l.sum v⟫ = l.sum fun (i : ι) (a : M) ↦ ⟪x, v i a⟫
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 2)
    if args is not None:
        try:
            rhs = OOp("l_sum", (OVar("fun"), OOp("i", (OVar("colon"), OVar("i"),)), OOp("a", (OVar("colon"), OVar("M"),)), OVar("_unknown"), OVar("x"), args[1], OVar("i"), OVar("a"),))
            results.append((rhs, "Mathlib: Finsupp_inner_sum"))
        except Exception:
            pass
    return results


def _r0368_ofDigits_eq_sum_add_ofDigits(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.ofDigits_eq_sum_add_ofDigits
    # ofDigits a = (∑ i ∈ Finset.range n, ofDigitsTerm a i) +       ((b : ℝ) ^ n)⁻¹ * ofDigits (fun i ↦ a (i + n))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofDigits", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("range", (OVar("n"), OVar("ofDigitsTerm"), args[0], OVar("i"),)))), OOp("*", (OVar("b_colon_pow_n_inv"), OOp("ofDigits", (OOp("fun", (OVar("i"), OVar("_unknown"), args[0], OOp("+", (OVar("i"), OVar("n"))),)),))))))
            results.append((rhs, "Mathlib: Real_ofDigits_eq_sum_add_ofDigits"))
        except Exception:
            pass
    return results


def _r0369_ofDigits_digits_sum_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.ofDigits_digits_sum_eq
    # b ^ n * ∑ i ∈ Finset.range n, ofDigitsTerm (digits x b) i = ⌊b ^ n * x⌋₊
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("b"), OVar("n"))), OVar("x")))
            results.append((rhs, "Mathlib: Real_ofDigits_digits_sum_eq"))
        except Exception:
            pass
    return results


def _r0370_W_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Wallis.W_succ
    # W (k + 1) = W k * ((2 * k + 2) / (2 * k + 1) * ((2 * k + 2) / (2 * k + 3)))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "W", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("W", (OVar("k"),)), OOp("*", (OOp("//", (OOp("+", (OOp("*", (OLit(2), OVar("k"))), OLit(2))), OOp("+", (OOp("*", (OLit(2), OVar("k"))), OLit(1))))), OOp("//", (OOp("+", (OOp("*", (OLit(2), OVar("k"))), OLit(2))), OOp("+", (OOp("*", (OLit(2), OVar("k"))), OLit(3)))))))))
            results.append((rhs, "Mathlib: Real_Wallis_W_succ"))
        except Exception:
            pass
    return results


def _r0371_isLittleO_log_re_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.IsExpCmpFilter.isLittleO_log_re_re
    # (fun z => Real.log z.re) =o[l] re
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun", 4)
    if args is not None:
        try:
            rhs = OOp("o_l", (OVar("re"),))
            results.append((rhs, "Mathlib: Complex_IsExpCmpFilter_isLittleO_log_re_re"))
        except Exception:
            pass
    return results


def _r0372_isLittleO_im_pow_exp_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.IsExpCmpFilter.isLittleO_im_pow_exp_re
    # (fun z : ℂ => z.im ^ n) =o[l] fun z => Real.exp z.re
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("o_l", (OVar("fun"), OVar("z"), OVar("eq_gt"), OVar("Real_exp"), OVar("z_re"),))
            results.append((rhs, "Mathlib: Complex_IsExpCmpFilter_isLittleO_im_pow_exp_re"))
        except Exception:
            pass
    return results


def _r0373_abs_im_pow_eventuallyLE_exp_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.IsExpCmpFilter.abs_im_pow_eventuallyLE_exp_re
    # (fun z : ℂ => |z.im| ^ n) ≤ᶠ[l] fun z => Real.exp z.re
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_z_colon_eq_gt_pipe_z_impipe_pow_n", 3)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("Real_exp"), OVar("z_re"),))
            results.append((rhs, "Mathlib: Complex_IsExpCmpFilter_abs_im_pow_eventuallyLE_exp_re"))
        except Exception:
            pass
    return results


def _r0374_isLittleO_log_norm_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.IsExpCmpFilter.isLittleO_log_norm_re
    # (fun z => Real.log ‖z‖) =o[l] re
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun", 4)
    if args is not None:
        try:
            rhs = OOp("o_l", (OVar("re"),))
            results.append((rhs, "Mathlib: Complex_IsExpCmpFilter_isLittleO_log_norm_re"))
        except Exception:
            pass
    return results


def _r0375_isTheta_cpow_exp_re_mul_log(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.IsExpCmpFilter.isTheta_cpow_exp_re_mul_log
    # (· ^ a) =Θ[l] fun z ↦ Real.exp (re a * Real.log ‖z‖)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("l", (OVar("fun"), OVar("z"), args[0], OVar("Real_exp"), OOp("*", (OOp("re", (args[1],)), OOp("Real_log", (OVar("z"),)))),))
            results.append((rhs, "Mathlib: Complex_IsExpCmpFilter_isTheta_cpow_exp_re_mul_log"))
        except Exception:
            pass
    return results


def _r0376_isLittleO_cpow_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.IsExpCmpFilter.isLittleO_cpow_exp
    # (fun z => z ^ a) =o[l] fun z => exp (b * z)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("o_l", (OVar("fun"), OVar("z"), OVar("eq_gt"), OVar("exp"), OOp("*", (OVar("b"), OVar("z"))),))
            results.append((rhs, "Mathlib: Complex_IsExpCmpFilter_isLittleO_cpow_exp"))
        except Exception:
            pass
    return results


def _r0377_isLittleO_cpow_mul_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.IsExpCmpFilter.isLittleO_cpow_mul_exp
    # (fun z => z ^ a₁ * exp (b₁ * z)) =o[l] fun z => z ^ a₂ * exp (b₂ * z)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OOp("o_l", (OVar("fun"), OVar("z"), OVar("eq_gt"), OVar("z"),)), OVar("a_2"))), OOp("exp", (OOp("*", (OVar("b_2"), OVar("z"))),))))
            results.append((rhs, "Mathlib: Complex_IsExpCmpFilter_isLittleO_cpow_mul_exp"))
        except Exception:
            pass
    return results


def _r0378_isLittleO_exp_cpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.IsExpCmpFilter.isLittleO_exp_cpow
    # (fun z => exp (b * z)) =o[l] fun z => z ^ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun", 4)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("o_l", (OVar("fun"), args[0], args[1], args[0],)), OVar("a")))
            results.append((rhs, "Mathlib: Complex_IsExpCmpFilter_isLittleO_exp_cpow"))
        except Exception:
            pass
    return results


def _r0379_isLittleO_pow_mul_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.IsExpCmpFilter.isLittleO_pow_mul_exp
    # (fun z => z ^ m * exp (b₁ * z)) =o[l] fun z => z ^ n * exp (b₂ * z)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OOp("o_l", (OVar("fun"), OVar("z"), OVar("eq_gt"), OVar("z"),)), OVar("n"))), OOp("exp", (OOp("*", (OVar("b_2"), OVar("z"))),))))
            results.append((rhs, "Mathlib: Complex_IsExpCmpFilter_isLittleO_pow_mul_exp"))
        except Exception:
            pass
    return results


def _r0380_isLittleO_zpow_mul_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.IsExpCmpFilter.isLittleO_zpow_mul_exp
    # (fun z => z ^ m * exp (b₁ * z)) =o[l] fun z => z ^ n * exp (b₂ * z)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OOp("o_l", (OVar("fun"), OVar("z"), OVar("eq_gt"), OVar("z"),)), OVar("n"))), OOp("exp", (OOp("*", (OVar("b_2"), OVar("z"))),))))
            results.append((rhs, "Mathlib: Complex_IsExpCmpFilter_isLittleO_zpow_mul_exp"))
        except Exception:
            pass
    return results


def _r0381_range_exp_mul_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.range_exp_mul_I
    # (Set.range fun x : ℝ => exp (x * I)) = Metric.sphere 0 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_range", 7)
    if args is not None:
        try:
            rhs = OOp("Metric_sphere", (OLit(0), OLit(1),))
            results.append((rhs, "Mathlib: Complex_range_exp_mul_I"))
        except Exception:
            pass
    return results


def _r0382_arg_eq_pi_iff_lt_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_eq_pi_iff_lt_zero
    # arg z = π ↔ z < 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("iff", (OVar("pi"), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: Complex_arg_eq_pi_iff_lt_zero"))
        except Exception:
            pass
    return results


def _r0383_image_exp_Ioc_eq_sphere(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.image_exp_Ioc_eq_sphere
    # (fun θ : ℝ ↦ exp (θ * I)) '' Set.Ioc (-π) π = sphere 0 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_th_colon_exp_th_star_I", 4)
    if args is not None:
        try:
            rhs = OOp("sphere", (OLit(0), OLit(1),))
            results.append((rhs, "Mathlib: Complex_image_exp_Ioc_eq_sphere"))
        except Exception:
            pass
    return results


def _r0384_arg_lt_pi_div_two_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_lt_pi_div_two_iff
    # arg z < π / 2 ↔ 0 < re z ∨ im z < 0 ∨ z = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_arg_lt_pi_div_two_iff"))
        except Exception:
            pass
    return results


def _r0385_abs_arg_lt_pi_div_two_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.abs_arg_lt_pi_div_two_iff
    # |arg z| < π / 2 ↔ 0 < re z ∨ z = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_abs_arg_lt_pi_div_two_iff"))
        except Exception:
            pass
    return results


def _r0386_toCircle_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.toCircle_coe
    # toCircle x = .exp x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toCircle", 1)
    if args is not None:
        try:
            rhs = OOp("exp", (args[0],))
            results.append((rhs, "Mathlib: Real_Angle_toCircle_coe"))
        except Exception:
            pass
    return results


def _r0387_arg_toCircle(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.arg_toCircle
    # (arg θ.toCircle : Angle) = θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 3)
    if args is not None:
        try:
            rhs = OVar("th")
            results.append((rhs, "Mathlib: Real_Angle_arg_toCircle"))
        except Exception:
            pass
    return results


def _r0388_range_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.range_exp
    # Set.range exp = {0}ᶜ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_range", 1)
    if args is not None:
        try:
            rhs = OVar("_0")
            results.append((rhs, "Mathlib: Complex_range_exp"))
        except Exception:
            pass
    return results


def _r0389_exp_inj_of_neg_pi_lt_of_le_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.exp_inj_of_neg_pi_lt_of_le_pi
    # x = y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("y")
            results.append((rhs, "Mathlib: Complex_exp_inj_of_neg_pi_lt_of_le_pi"))
    except Exception:
        pass
    return results


def _r0390_logTaylor_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.logTaylor_succ
    # logTaylor (n + 1) = logTaylor n + (fun z : ℂ ↦ (-1) ^ (n + 1) * z ^ n / n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logTaylor", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("logTaylor", (OVar("n"),)), OOp("*", (OOp("**", (OOp("fun", (OVar("z"), OVar("colon"), OVar("_unknown"), OVar("_unknown"), OVar("minus_1"),)), OOp("+", (OVar("n"), OLit(1))))), OOp("//", (OOp("**", (OVar("z"), OVar("n"))), OVar("n")))))))
            results.append((rhs, "Mathlib: Complex_logTaylor_succ"))
        except Exception:
            pass
    return results


def _r0391_exp_sub_sum_range_isBigO_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.exp_sub_sum_range_isBigO_pow
    # (fun x ↦ exp x - ∑ i ∈ Finset.range n, x ^ i / i !) =O[𝓝 0] (· ^ n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("O_0", (OOp("**", (OVar("_unknown"), OVar("n"))),))
            results.append((rhs, "Mathlib: Complex_exp_sub_sum_range_isBigO_pow"))
        except Exception:
            pass
    return results


def _r0392_exp_sub_sum_range_succ_isLittleO_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.exp_sub_sum_range_succ_isLittleO_pow
    # (fun x ↦ exp x - ∑ i ∈ Finset.range (n + 1), x ^ i / i !) =o[𝓝 0] (· ^ n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("o_0", (OOp("**", (OVar("_unknown"), OVar("n"))),))
            results.append((rhs, "Mathlib: Complex_exp_sub_sum_range_succ_isLittleO_pow"))
        except Exception:
            pass
    return results


def _r0393_exp_sub_sum_range_succ_isLittleO_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.exp_sub_sum_range_succ_isLittleO_pow
    # (fun x ↦ exp x - ∑ i ∈ Finset.range (n + 1), x ^ i / i !) =o[𝓝 0] (· ^ n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("o_0", (OOp("**", (OVar("_unknown"), OVar("n"))),))
            results.append((rhs, "Mathlib: Real_exp_sub_sum_range_succ_isLittleO_pow"))
        except Exception:
            pass
    return results


def _r0394_betaIntegral_eval_nat_add_one_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.betaIntegral_eval_nat_add_one_right
    # betaIntegral u (n + 1) = n ! / ∏ j ∈ Finset.range (n + 1), (u + j)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "betaIntegral", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("n", (OOp("not", (OVar("_"),)),)), OOp("in", (OOp("_unknown", (OVar("j"),)), OOp("range", (OVar("n_plus_1"), OOp("+", (args[0], OVar("j"))),))))))
            results.append((rhs, "Mathlib: Complex_betaIntegral_eval_nat_add_one_right"))
        except Exception:
            pass
    return results


def _r0395_GammaSeq_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.GammaSeq_mul
    # GammaSeq z n * GammaSeq (1 - z) n =       n / (n + ↑1 - z) * (↑1 / (z * ∏ j ∈ Finset.range n, (↑1 - z ^ 2 / ((j : ℂ) + 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("//", (OVar("n"), OOp("+", (OVar("n"), OOp("-", (OVar("_1"), OVar("z"))))))), OOp("//", (OVar("_1"), OOp("*", (OVar("z"), OOp("in", (OOp("_unknown", (OVar("j"),)), OOp("range", (OVar("n"), OOp("-", (OVar("_1"), OOp("//", (OOp("**", (OVar("z"), OLit(2))), OOp("**", (OOp("+", (OOp("j", (OVar("colon"), OVar("_unknown"),)), OLit(1))), OLit(2))))))),))))))))))
            results.append((rhs, "Mathlib: Complex_GammaSeq_mul"))
        except Exception:
            pass
    return results


def _r0396_range_logb(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.range_logb
    # range (logb b) = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: Real_range_logb"))
        except Exception:
            pass
    return results


def _r0397_range_log(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.range_log
    # range log = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: Real_range_log"))
        except Exception:
            pass
    return results


def _r0398_leftDeriv_mul_log(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.leftDeriv_mul_log
    # derivWithin (fun x ↦ x * log x) (Set.Iio x) x = log x + 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "derivWithin", 3)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("log", (args[2],)), OLit(1)))
            results.append((rhs, "Mathlib: Real_leftDeriv_mul_log"))
        except Exception:
            pass
    return results


def _r0399_posLog_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.posLog_def
    # log⁺ x = max 0 (log x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logpos", 1)
    if args is not None:
        try:
            rhs = OOp("max", (OLit(0), OOp("log", (args[0],)),))
            results.append((rhs, "Mathlib: Real_posLog_def"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_nat_order rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("*", "**", "+", "-", "//", "<", "<=", "==", "AddSubgroup_zmultiples", "Algebra_adjoin", "F", "Fin_castLE", "Finset", "Finset_univ_image", "Finsupp_toFreeAbelianGroup", "Finsupp_toMultiset", "Fintype_card", "FreeAbelianGroup_toFinsupp", "GammaSeq", "Icc", "Icc_a_b_image", "Icc_a_b_map", "Ici_a_image", "Ico", "Ico_a_b_image", "Ico_a_b_map", "Iic", "Iic_a_image", "Iio_b_image", "IntFractPair_mk_b_fr", "IntFractPair_stream", "Ioc", "Ioc_a_b_image", "Ioc_a_b_map", "Ioi_a_image", "Ioo", "Ioo_a_b_image", "Ioo_a_b_map", "IsCauSeq", "Lex", "M", "Pi_single", "Real_cos", "Real_tan", "Set_Iio", "Set_range", "Set_toFinite", "W", "X", "_1",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_nat_order axioms."""
    if recognizes(term):
        return 0.8
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_nat_order rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_prod_univ_fun_getElem(term, ctx))
    results.extend(_r0001_coe_sum(term, ctx))
    results.extend(_r0002_sum_multiset_singleton(term, ctx))
    results.extend(_r0003_toFreeAbelianGroup_single(term, ctx))
    results.extend(_r0004_e_succ(term, ctx))
    results.extend(_r0005_length_add_le(term, ctx))
    results.extend(_r0006_image_add_left_Ico(term, ctx))
    results.extend(_r0007_image_add_left_Ioc(term, ctx))
    results.extend(_r0008_image_add_left_Ioo(term, ctx))
    results.extend(_r0009_image_add_right_Icc(term, ctx))
    results.extend(_r0010_image_add_right_Ico(term, ctx))
    results.extend(_r0011_image_add_right_Ioc(term, ctx))
    results.extend(_r0012_image_add_right_Ioo(term, ctx))
    results.extend(_r0013_cast_finsetSup(term, ctx))
    results.extend(_r0014_val_add(term, ctx))
    results.extend(_r0015_val_mul(term, ctx))
    results.extend(_r0016_ext(term, ctx))
    results.extend(_r0017_succ_mod_two_add_mod_two(term, ctx))
    results.extend(_r0018_expNear_succ(term, ctx))
    results.extend(_r0019_range_normSq(term, ctx))
    results.extend(_r0020_closure_setOf_re_lt(term, ctx))
    results.extend(_r0021_closure_setOf_im_lt(term, ctx))
    results.extend(_r0022_closure_setOf_lt_re(term, ctx))
    results.extend(_r0023_closure_setOf_lt_im(term, ctx))
    results.extend(_r0024_frontier_setOf_re_lt(term, ctx))
    results.extend(_r0025_frontier_setOf_im_lt(term, ctx))
    results.extend(_r0026_frontier_setOf_lt_re(term, ctx))
    results.extend(_r0027_frontier_setOf_lt_im(term, ctx))
    results.extend(_r0028_centerMass_smul_left(term, ctx))
    results.extend(_r0029_range_arg(term, ctx))
    results.extend(_r0030_coe_toCircle(term, ctx))
    results.extend(_r0031_toCircle_add(term, ctx))
    results.extend(_r0032_range_exp(term, ctx))
    results.extend(_r0033_isLittleO_pow_exp_atTop(term, ctx))
    results.extend(_r0034_coe_add(term, ctx))
    results.extend(_r0035_coe_nsmul(term, ctx))
    results.extend(_r0036_intCast_mul_eq_zsmul(term, ctx))
    results.extend(_r0037_two_zsmul_coe_pi(term, ctx))
    results.extend(_r0038_coe_pi_add_coe_pi(term, ctx))
    results.extend(_r0039_sin_coe_pi(term, ctx))
    results.extend(_r0040_cos_coe_pi(term, ctx))
    results.extend(_r0041_coe_toReal(term, ctx))
    results.extend(_r0042_cos_toReal(term, ctx))
    results.extend(_r0043_tan_coe_pi(term, ctx))
    results.extend(_r0044_tan_toReal(term, ctx))
    results.extend(_r0045_tan_eq_of_two_nsmul_eq(term, ctx))
    results.extend(_r0046_sign_coe_pi(term, ctx))
    results.extend(_r0047_sign_pi_add(term, ctx))
    results.extend(_r0048_ofColex_bot(term, ctx))
    results.extend(_r0049_largeSchroder_two(term, ctx))
    results.extend(_r0050_largeSchroder_succ(term, ctx))
    results.extend(_r0051_smallSchroder_succ_eq_largeSchroder_div(term, ctx))
    results.extend(_r0052_stirlingFirst_succ_left(term, ctx))
    results.extend(_r0053_stirlingSecond_succ_left(term, ctx))
    results.extend(_r0054_eval_pappAck_step_succ(term, ctx))
    results.extend(_r0055_range_im(term, ctx))
    results.extend(_r0056_rev_castSucc(term, ctx))
    results.extend(_r0057_toFin_fs(term, ctx))
    results.extend(_r0058_ofFin_succ(term, ctx))
    results.extend(_r0059_castLE_comp_castSucc(term, ctx))
    results.extend(_r0060_range_castLE(term, ctx))
    results.extend(_r0061_univ_unique(term, ctx))
    results.extend(_r0062_coe_toList(term, ctx))
    results.extend(_r0063_dens_image(term, ctx))
    results.extend(_r0064_sup_insert(term, ctx))
    results.extend(_r0065_sup_image(term, ctx))
    results.extend(_r0066_sup_sup(term, ctx))
    results.extend(_r0067_sup_disjSum(term, ctx))
    results.extend(_r0068_sup_singleton_apply(term, ctx))
    results.extend(_r0069_max_insert(term, ctx))
    results.extend(_r0070_max_eq_top(term, ctx))
    results.extend(_r0071_min_insert(term, ctx))
    results.extend(_r0072_min_eq_bot(term, ctx))
    results.extend(_r0073_coe_image_2(term, ctx))
    results.extend(_r0074_image_2_singleton_left(term, ctx))
    results.extend(_r0075_image_2_singleton_right(term, ctx))
    results.extend(_r0076_image_2_curry(term, ctx))
    results.extend(_r0077_image_uncurry_product(term, ctx))
    results.extend(_r0078_image_2_swap(term, ctx))
    results.extend(_r0079_coe_pimage(term, ctx))
    results.extend(_r0080_pimage_some(term, ctx))
    results.extend(_r0081_preimage_univ(term, ctx))
    results.extend(_r0082_toFinset_range(term, ctx))
    results.extend(_r0083_coe_range(term, ctx))
    results.extend(_r0084_toLeft_insert_inr(term, ctx))
    results.extend(_r0085_singleton_sups(term, ctx))
    results.extend(_r0086_sups_singleton(term, ctx))
    results.extend(_r0087_univ_sups_univ(term, ctx))
    results.extend(_r0088_filter_sups_le(term, ctx))
    results.extend(_r0089_equivCongrLeft_symm(term, ctx))
    results.extend(_r0090_coe_equivFunOnFinite_symm(term, ctx))
    results.extend(_r0091_unique_ext(term, ctx))
    results.extend(_r0092_toMultiset_sum(term, ctx))
    results.extend(_r0093_single_mul(term, ctx))
    results.extend(_r0094_smul_apply(term, ctx))
    results.extend(_r0095_single_eq_update(term, ctx))
    results.extend(_r0096_toDFinsupp_add(term, ctx))
    results.extend(_r0097_univ_image_def(term, ctx))
    results.extend(_r0098_card_lex(term, ctx))
    results.extend(_r0099_card_fin_lt_of_le(term, ctx))
    results.extend(_r0100_shiftLeft_natCast(term, ctx))
    results.extend(_r0101_cast_pred(term, ctx))
    results.extend(_r0102_pred_eq_pred(term, ctx))
    results.extend(_r0103_log2_eq_succ_log2_shiftRight(term, ctx))
    results.extend(_r0104_bodd_succ(term, ctx))
    results.extend(_r0105_div2_succ(term, ctx))
    results.extend(_r0106_image_cast_int_Icc(term, ctx))
    results.extend(_r0107_choose_succ_succ(term, ctx))
    results.extend(_r0108_choose_succ_self(term, ctx))
    results.extend(_r0109_triangle_succ(term, ctx))
    results.extend(_r0110_multichoose_succ_succ(term, ctx))
    results.extend(_r0111_factorial_succ(term, ctx))
    results.extend(_r0112_mul_factorial_pred(term, ctx))
    results.extend(_r0113_superFactorial_succ(term, ctx))
    results.extend(_r0114_prod_range_succ_factorial(term, ctx))
    results.extend(_r0115_zeckendorf_succ(term, ctx))
    results.extend(_r0116_zeckendorf_of_pos(term, ctx))
    results.extend(_r0117_ppred_succ(term, ctx))
    results.extend(_r0118_psub_succ(term, ctx))
    results.extend(_r0119_minFac_two(term, ctx))
    results.extend(_r0120_minFac_eq(term, ctx))
    results.extend(_r0121_size_bit(term, ctx))
    results.extend(_r0122_pred_eq_pred(term, ctx))
    results.extend(_r0123_succ_iterate(term, ctx))
    results.extend(_r0124_le_succ_iff_eq_or_le(term, ctx))
    results.extend(_r0125_natPred_succPNat(term, ctx))
    results.extend(_r0126_succPNat_natPred(term, ctx))
    results.extend(_r0127_cast_min(term, ctx))
    results.extend(_r0128_cast_max(term, ctx))
    results.extend(_r0129_preimage_cast_Icc(term, ctx))
    results.extend(_r0130_preimage_cast_Ico(term, ctx))
    results.extend(_r0131_preimage_cast_Ioc(term, ctx))
    results.extend(_r0132_preimage_cast_Ioo(term, ctx))
    results.extend(_r0133_preimage_cast_Ici(term, ctx))
    results.extend(_r0134_preimage_cast_Iic(term, ctx))
    results.extend(_r0135_preimage_cast_Ioi(term, ctx))
    results.extend(_r0136_preimage_cast_Iio(term, ctx))
    results.extend(_r0137_preimage_cast_uIcc(term, ctx))
    results.extend(_r0138_preimage_cast_uIoc(term, ctx))
    results.extend(_r0139_sInf_univ(term, ctx))
    results.extend(_r0140_sym2Mul_apply_mk(term, ctx))
    results.extend(_r0141_algebraMap_eq_gen_self(term, ctx))
    results.extend(_r0142_minpolyX_aeval_X(term, ctx))
    results.extend(_r0143_cycleRange_apply(term, ctx))
    results.extend(_r0144_succAbove_cycleRange(term, ctx))
    results.extend(_r0145_cycleRange_symm_succ(term, ctx))
    results.extend(_r0146_cycleIcc_of_lt(term, ctx))
    results.extend(_r0147_affineCombinationSingleWeights_apply_of(term, ctx))
    results.extend(_r0148_sum_affineCombinationSingleWeights(term, ctx))
    results.extend(_r0149_linearEquivFunOnFinite_symm_apply(term, ctx))
    results.extend(_r0150_coeFn_toL1(term, ctx))
    results.extend(_r0151_volume_real_Ico(term, ctx))
    results.extend(_r0152_volume_real_Ico_of_le(term, ctx))
    results.extend(_r0153_volume_real_Icc(term, ctx))
    results.extend(_r0154_volume_real_Icc_of_le(term, ctx))
    results.extend(_r0155_volume_real_Ioo(term, ctx))
    results.extend(_r0156_volume_real_Ioo_of_le(term, ctx))
    results.extend(_r0157_volume_real_Ioc(term, ctx))
    results.extend(_r0158_volume_real_Ioc_of_le(term, ctx))
    results.extend(_r0159_liminf_of_not_isCoboundedUnder(term, ctx))
    results.extend(_r0160_liminf_of_not_isBoundedUnder(term, ctx))
    results.extend(_r0161_coe_min(term, ctx))
    results.extend(_r0162_box_succ_eq_sdiff(term, ctx))
    results.extend(_r0163_box_succ_disjUnion(term, ctx))
    results.extend(_r0164_finsetImage_val_Ico(term, ctx))
    results.extend(_r0165_finsetImage_val_Ioc(term, ctx))
    results.extend(_r0166_finsetImage_val_Ioo(term, ctx))
    results.extend(_r0167_finsetImage_val_uIcc(term, ctx))
    results.extend(_r0168_finsetImage_val_Ici(term, ctx))
    results.extend(_r0169_finsetImage_val_Ioi(term, ctx))
    results.extend(_r0170_finsetImage_val_Iic(term, ctx))
    results.extend(_r0171_finsetImage_val_Iio(term, ctx))
    results.extend(_r0172_intervalGapsWithin_succ_fst_of_lt(term, ctx))
    results.extend(_r0173_preimage_val_Ici_val(term, ctx))
    results.extend(_r0174_preimage_val_Ioi_val(term, ctx))
    results.extend(_r0175_preimage_val_Iic_val(term, ctx))
    results.extend(_r0176_preimage_val_Iio_val(term, ctx))
    results.extend(_r0177_preimage_val_Icc_val(term, ctx))
    results.extend(_r0178_preimage_val_Ico_val(term, ctx))
    results.extend(_r0179_preimage_val_Ioc_val(term, ctx))
    results.extend(_r0180_preimage_val_Ioo_val(term, ctx))
    results.extend(_r0181_preimage_val_uIcc_val(term, ctx))
    results.extend(_r0182_preimage_val_uIoc_val(term, ctx))
    results.extend(_r0183_preimage_val_uIoo_val(term, ctx))
    results.extend(_r0184_image_val_Ici(term, ctx))
    results.extend(_r0185_image_val_Iic(term, ctx))
    results.extend(_r0186_image_val_Iio(term, ctx))
    results.extend(_r0187_image_val_uIoc(term, ctx))
    results.extend(_r0188_image_val_uIoo(term, ctx))
    results.extend(_r0189_preimage_castLE_Ici_castLE(term, ctx))
    results.extend(_r0190_image_castLE_Iio(term, ctx))
    results.extend(_r0191_image_castLE_Icc(term, ctx))
    results.extend(_r0192_preimage_castAdd_Ici_castAdd(term, ctx))
    results.extend(_r0193_preimage_castAdd_Ioi_castAdd(term, ctx))
    results.extend(_r0194_preimage_castAdd_Iic_castAdd(term, ctx))
    results.extend(_r0195_preimage_castAdd_Iio_castAdd(term, ctx))
    results.extend(_r0196_preimage_castAdd_Icc_castAdd(term, ctx))
    results.extend(_r0197_image_castAdd_Iio(term, ctx))
    results.extend(_r0198_image_castAdd_Icc(term, ctx))
    results.extend(_r0199_preimage_cast_Ici(term, ctx))
    results.extend(_r0200_preimage_cast_Ioi(term, ctx))
    results.extend(_r0201_preimage_cast_Iic(term, ctx))
    results.extend(_r0202_preimage_cast_Iio(term, ctx))
    results.extend(_r0203_preimage_cast_Icc(term, ctx))
    results.extend(_r0204_preimage_castSucc_Ioi_castSucc(term, ctx))
    results.extend(_r0205_preimage_castSucc_Iic_castSucc(term, ctx))
    results.extend(_r0206_preimage_castSucc_Iio_castSucc(term, ctx))
    results.extend(_r0207_preimage_castSucc_Icc_castSucc(term, ctx))
    results.extend(_r0208_image_castSucc_Iic(term, ctx))
    results.extend(_r0209_image_castSucc_Iio(term, ctx))
    results.extend(_r0210_image_castSucc_Icc(term, ctx))
    results.extend(_r0211_image_castSucc_Ico(term, ctx))
    results.extend(_r0212_image_castSucc_Ioc(term, ctx))
    results.extend(_r0213_image_castSucc_Ioo(term, ctx))
    results.extend(_r0214_image_castSucc_uIcc(term, ctx))
    results.extend(_r0215_image_castSucc_uIoc(term, ctx))
    results.extend(_r0216_image_castSucc_uIoo(term, ctx))
    results.extend(_r0217_preimage_natAdd_Ioi_natAdd(term, ctx))
    results.extend(_r0218_preimage_natAdd_Iic_natAdd(term, ctx))
    results.extend(_r0219_preimage_natAdd_Iio_natAdd(term, ctx))
    results.extend(_r0220_preimage_natAdd_Icc_natAdd(term, ctx))
    results.extend(_r0221_preimage_addNat_Ioi_addNat(term, ctx))
    results.extend(_r0222_preimage_addNat_Iic_addNat(term, ctx))
    results.extend(_r0223_preimage_addNat_Iio_addNat(term, ctx))
    results.extend(_r0224_preimage_addNat_Icc_addNat(term, ctx))
    results.extend(_r0225_preimage_succ_Ioi_succ(term, ctx))
    results.extend(_r0226_preimage_succ_Iic_succ(term, ctx))
    results.extend(_r0227_preimage_succ_Iio_succ(term, ctx))
    results.extend(_r0228_preimage_succ_Icc_succ(term, ctx))
    results.extend(_r0229_preimage_succ_Ico_succ(term, ctx))
    results.extend(_r0230_preimage_succ_Ioc_succ(term, ctx))
    results.extend(_r0231_preimage_succ_Ioo_succ(term, ctx))
    results.extend(_r0232_preimage_succ_uIcc_succ(term, ctx))
    results.extend(_r0233_preimage_succ_uIoc_succ(term, ctx))
    results.extend(_r0234_preimage_succ_uIoo_succ(term, ctx))
    results.extend(_r0235_image_succ_Ici(term, ctx))
    results.extend(_r0236_image_succ_Ioi(term, ctx))
    results.extend(_r0237_image_succ_Iic(term, ctx))
    results.extend(_r0238_image_succ_Ico(term, ctx))
    results.extend(_r0239_image_succ_Ioc(term, ctx))
    results.extend(_r0240_image_succ_Ioo(term, ctx))
    results.extend(_r0241_image_succ_uIcc(term, ctx))
    results.extend(_r0242_image_succ_uIoc(term, ctx))
    results.extend(_r0243_image_succ_uIoo(term, ctx))
    results.extend(_r0244_image_rev(term, ctx))
    results.extend(_r0245_preimage_rev_Ici(term, ctx))
    results.extend(_r0246_preimage_rev_Ioi(term, ctx))
    results.extend(_r0247_preimage_rev_Iic(term, ctx))
    results.extend(_r0248_preimage_rev_Iio(term, ctx))
    results.extend(_r0249_preimage_rev_Icc(term, ctx))
    results.extend(_r0250_preimage_rev_Ioo(term, ctx))
    results.extend(_r0251_preimage_rev_uIcc(term, ctx))
    results.extend(_r0252_preimage_rev_uIoo(term, ctx))
    results.extend(_r0253_eq_pow_of_mul_eq_pow_odd_left(term, ctx))
    results.extend(_r0254_emultiplicity_natAbs(term, ctx))
    results.extend(_r0255_dens_eq_sum_dens_image(term, ctx))
    results.extend(_r0256_prod_range(term, ctx))
    results.extend(_r0257_prod_univ_succAbove(term, ctx))
    results.extend(_r0258_prod_univ_succ(term, ctx))
    results.extend(_r0259_prod_univ_getElem(term, ctx))
    results.extend(_r0260_prod_fintype(term, ctx))
    results.extend(_r0261_sum_ite_self_eq(term, ctx))
    results.extend(_r0262_prod_pow(term, ctx))
    results.extend(_r0263_onFinset_prod(term, ctx))
    results.extend(_r0264_mul_prod_erase(term, ctx))
    results.extend(_r0265_prod_congr(term, ctx))
    results.extend(_r0266_prod_eq_single(term, ctx))
    results.extend(_r0267_prod_unique(term, ctx))
    results.extend(_r0268_single_multiset_sum(term, ctx))
    results.extend(_r0269_single_finset_sum(term, ctx))
    results.extend(_r0270_single_sum(term, ctx))
    results.extend(_r0271_finset_sum_apply(term, ctx))
    results.extend(_r0272_sum_apply(term, ctx))
    results.extend(_r0273_coe_finset_sum(term, ctx))
    results.extend(_r0274_prod_mul(term, ctx))
    results.extend(_r0275_liftAddHom_apply(term, ctx))
    results.extend(_r0276_liftAddHom_symm_apply_apply(term, ctx))
    results.extend(_r0277_sum_single(term, ctx))
    results.extend(_r0278_univ_sum_single(term, ctx))
    results.extend(_r0279_univ_sum_single_apply(term, ctx))
    results.extend(_r0280_sum_single_add_single(term, ctx))
    results.extend(_r0281_equivFunOnFinite_symm_eq_sum(term, ctx))
    results.extend(_r0282_coe_univ_sum_single(term, ctx))
    results.extend(_r0283_equivFunOnFinite_symm_sum(term, ctx))
    results.extend(_r0284_liftAddHom_apply_single(term, ctx))
    results.extend(_r0285_prod_embDomain(term, ctx))
    results.extend(_r0286_multiset_sum_sum(term, ctx))
    results.extend(_r0287_sum_mul(term, ctx))
    results.extend(_r0288_mul_sum(term, ctx))
    results.extend(_r0289_ofSupportFinite_fin_two_eq(term, ctx))
    results.extend(_r0290_prod_unique(term, ctx))
    results.extend(_r0291_prod_eq_prod_range_intervalGapsWithin(term, ctx))
    results.extend(_r0292_prod_Icc_succ_eq_mul_endpoints(term, ctx))
    results.extend(_r0293_prod_pi_mulSingle(term, ctx))
    results.extend(_r0294_prod_pow_boole(term, ctx))
    results.extend(_r0295_prod_pi_mulSingle(term, ctx))
    results.extend(_r0296_prod_preimage(term, ctx))
    results.extend(_r0297_prod_boole(term, ctx))
    results.extend(_r0298_prod_boole(term, ctx))
    results.extend(_r0299_prod_Ico_succ_top(term, ctx))
    results.extend(_r0300_prod_Ioc_succ_top(term, ctx))
    results.extend(_r0301_prod_Icc_succ_top(term, ctx))
    results.extend(_r0302_prod_Ico_reflect(term, ctx))
    results.extend(_r0303_sum_Ico_reflect(term, ctx))
    results.extend(_r0304_prod_range_reflect(term, ctx))
    results.extend(_r0305_sum_range_reflect(term, ctx))
    results.extend(_r0306_prod_Iic_div(term, ctx))
    results.extend(_r0307_prod_Icc_div(term, ctx))
    results.extend(_r0308_sum_range_by_parts(term, ctx))
    results.extend(_r0309_prod_antidiagonal_succ(term, ctx))
    results.extend(_r0310_sum_antidiagonal_succ(term, ctx))
    results.extend(_r0311_prod_antidiagonal_eq_prod_range_succ_mk(term, ctx))
    results.extend(_r0312_prod_antidiagonal_eq_prod_range_succ(term, ctx))
    results.extend(_r0313_univ_prod_mulSingle(term, ctx))
    results.extend(_r0314_sum_boole(term, ctx))
    results.extend(_r0315_coe_to_intFractPair(term, ctx))
    results.extend(_r0316_stream_succ_of_some(term, ctx))
    results.extend(_r0317_stream_succ(term, ctx))
    results.extend(_r0318_seq1_fst_eq_of(term, ctx))
    results.extend(_r0319_toFreeAbelianGroup_toFinsupp(term, ctx))
    results.extend(_r0320_lcm_image(term, ctx))
    results.extend(_r0321_apply_single(term, ctx))
    results.extend(_r0322_range_add(term, ctx))
    results.extend(_r0323_smul_def(term, ctx))
    results.extend(_r0324_image_smul_product(term, ctx))
    results.extend(_r0325_smul_singleton(term, ctx))
    results.extend(_r0326_zmultiples_one(term, ctx))
    results.extend(_r0327_zmultiples_natAbs(term, ctx))
    results.extend(_r0328_range_castAddHom(term, ctx))
    results.extend(_r0329_range_nsmulAddMonoidHom(term, ctx))
    results.extend(_r0330_sum_single_smul(term, ctx))
    results.extend(_r0331_prod_eq_prod_Ico_succ_bot(term, ctx))
    results.extend(_r0332_length_pure(term, ctx))
    results.extend(_r0333_length_zero(term, ctx))
    results.extend(_r0334_length_bot(term, ctx))
    results.extend(_r0335_map_add_left_Icc(term, ctx))
    results.extend(_r0336_map_add_left_Ico(term, ctx))
    results.extend(_r0337_map_add_left_Ioc(term, ctx))
    results.extend(_r0338_map_add_left_Ioo(term, ctx))
    results.extend(_r0339_image_add_left_Icc(term, ctx))
    results.extend(_r0340_mul_sup_0(term, ctx))
    results.extend(_r0341_sup_mul_0(term, ctx))
    results.extend(_r0342_exists_add_mul_eq_of_gcd_dvd_of_mul_pred(term, ctx))
    results.extend(_r0343_mk_add_mk(term, ctx))
    results.extend(_r0344_geomSum_eq(term, ctx))
    results.extend(_r0345_natCast_pow_pred(term, ctx))
    results.extend(_r0346_coe_nat_two_pow_pred(term, ctx))
    results.extend(_r0347_mod_two_add_succ_mod_two(term, ctx))
    results.extend(_r0348_trop_inf(term, ctx))
    results.extend(_r0349_sum_integral_congr(term, ctx))
    results.extend(_r0350_isCauSeq_norm_exp(term, ctx))
    results.extend(_r0351_isCauSeq_exp(term, ctx))
    results.extend(_r0352_exp_multiset_sum(term, ctx))
    results.extend(_r0353_integerComplement_eq(term, ctx))
    results.extend(_r0354_mem_integerComplement_iff(term, ctx))
    results.extend(_r0355_upperHalfPlane_inter_integerComplement(term, ctx))
    results.extend(_r0356_lt_def(term, ctx))
    results.extend(_r0357_interior_preimage_re(term, ctx))
    results.extend(_r0358_interior_preimage_im(term, ctx))
    results.extend(_r0359_closure_preimage_re(term, ctx))
    results.extend(_r0360_closure_preimage_im(term, ctx))
    results.extend(_r0361_frontier_preimage_re(term, ctx))
    results.extend(_r0362_frontier_preimage_im(term, ctx))
    results.extend(_r0363_tsum_eq_tsum_fourier(term, ctx))
    results.extend(_r0364_tsum_eq_tsum_fourier_of_rpow_decay_of_su(term, ctx))
    results.extend(_r0365_tsum_eq_tsum_fourier_of_rpow_decay(term, ctx))
    results.extend(_r0366_sum_inner(term, ctx))
    results.extend(_r0367_inner_sum(term, ctx))
    results.extend(_r0368_ofDigits_eq_sum_add_ofDigits(term, ctx))
    results.extend(_r0369_ofDigits_digits_sum_eq(term, ctx))
    results.extend(_r0370_W_succ(term, ctx))
    results.extend(_r0371_isLittleO_log_re_re(term, ctx))
    results.extend(_r0372_isLittleO_im_pow_exp_re(term, ctx))
    results.extend(_r0373_abs_im_pow_eventuallyLE_exp_re(term, ctx))
    results.extend(_r0374_isLittleO_log_norm_re(term, ctx))
    results.extend(_r0375_isTheta_cpow_exp_re_mul_log(term, ctx))
    results.extend(_r0376_isLittleO_cpow_exp(term, ctx))
    results.extend(_r0377_isLittleO_cpow_mul_exp(term, ctx))
    results.extend(_r0378_isLittleO_exp_cpow(term, ctx))
    results.extend(_r0379_isLittleO_pow_mul_exp(term, ctx))
    results.extend(_r0380_isLittleO_zpow_mul_exp(term, ctx))
    results.extend(_r0381_range_exp_mul_I(term, ctx))
    results.extend(_r0382_arg_eq_pi_iff_lt_zero(term, ctx))
    results.extend(_r0383_image_exp_Ioc_eq_sphere(term, ctx))
    results.extend(_r0384_arg_lt_pi_div_two_iff(term, ctx))
    results.extend(_r0385_abs_arg_lt_pi_div_two_iff(term, ctx))
    results.extend(_r0386_toCircle_coe(term, ctx))
    results.extend(_r0387_arg_toCircle(term, ctx))
    results.extend(_r0388_range_exp(term, ctx))
    results.extend(_r0389_exp_inj_of_neg_pi_lt_of_le_pi(term, ctx))
    results.extend(_r0390_logTaylor_succ(term, ctx))
    results.extend(_r0391_exp_sub_sum_range_isBigO_pow(term, ctx))
    results.extend(_r0392_exp_sub_sum_range_succ_isLittleO_pow(term, ctx))
    results.extend(_r0393_exp_sub_sum_range_succ_isLittleO_pow(term, ctx))
    results.extend(_r0394_betaIntegral_eval_nat_add_one_right(term, ctx))
    results.extend(_r0395_GammaSeq_mul(term, ctx))
    results.extend(_r0396_range_logb(term, ctx))
    results.extend(_r0397_range_log(term, ctx))
    results.extend(_r0398_leftDeriv_mul_log(term, ctx))
    results.extend(_r0399_posLog_def(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_nat_order rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("Fin_prod_snoc", "i_colon_Fin_n_succ_snoc_f_x_colon_Fin_n_succ_to_M_i_eq_i_colon_Fin_n_f_i_star_x", "Not an equality or iff proposition"),
    ("Finsupp_prod_ite_eq", "_unknown", "Empty proposition"),
    ("Finsupp_sum_ite_self_eq", "_unknown", "Empty proposition"),
    ("Finsupp_mul_prod_erase", "_unknown", "Empty proposition"),
    ("Finsupp_univ_sum_single_apply", "_unknown", "Empty proposition"),
    ("Finsupp_sum_apply", "_unknown", "Empty proposition"),
    ("Finsupp_sum_apply", "_unknown", "Empty proposition"),
    ("Int_natAbs_sum_le", "i_in_s_f_i_natAbs_le_i_in_s_f_i_natAbs", "Not an equality or iff proposition"),
    ("Finset_prod_pi_mulSingle", "_unknown", "Empty proposition"),
    ("Fintype_prod_pi_mulSingle", "_unknown", "Empty proposition"),
    ("Finset_prod_preimage", "_unknown", "Empty proposition"),
    ("Finset_Nat_prod_antidiagonal_succ", "_unknown", "Empty proposition"),
    ("Finset_Nat_sum_antidiagonal_succ", "_unknown", "Empty proposition"),
    ("GenContFract_IntFractPair_nth_stream_fr_nonneg_lt_one", "_0_le_ifp_n_fr_and_ifp_n_fr_lt_1", "Not an equality or iff proposition"),
    ("GenContFract_IntFractPair_nth_stream_fr_lt_one", "ifp_n_fr_lt_1", "Not an equality or iff proposition"),
    ("GenContFract_IntFractPair_one_le_succ_nth_stream_b", "_1_le_ifp_succ_n_b", "Not an equality or iff proposition"),
    ("GenContFract_IntFractPair_succ_nth_stream_b_le_nth_stream_fr_inv", "ifp_succ_n_b_colon_K_le_ifp_n_frinv", "Not an equality or iff proposition"),
    ("Nat_even_mul_succ_self", "Even_n_star_n_plus_1", "Not an equality or iff proposition"),
    ("Nat_even_mul_pred_self", "Even_n_star_n_minus_1", "Not an equality or iff proposition"),
    ("Finset_disjoint_range_addLeftEmbedding", "Disjoint_range_a_map_addLeftEmbedding_a_s", "Not an equality or iff proposition"),
    ("Finset_sup", "_unknown", "Empty proposition"),
    ("Finset_inf", "_unknown", "Empty proposition"),
    ("Finset_max", "_unknown", "Empty proposition"),
    ("Finset_min", "_unknown", "Empty proposition"),
    ("FinitePresentation_of_isBaseChange", "Module_FinitePresentation_A_N", "Not an equality or iff proposition"),
    ("FiniteMulArchimedeanClass_min_le_mk_mul", "min_mk_a_ha_mk_b_hb_le_mk_a_star_b_hab", "Not an equality or iff proposition"),
    ("Finset_expect_le_expect", "i_in_s_f_i_le_i_in_s_g_i", "Not an equality or iff proposition"),
    ("Finset_expect_le", "i_in_s_f_i_le_a", "Not an equality or iff proposition"),
    ("Finset_le_expect", "a_le_i_in_s_f_i", "Not an equality or iff proposition"),
    ("Finset_le_prod_nonempty_of_submultiplicative_on_pred", "f_i_in_s_g_i_le_i_in_s_f_g_i", "Not an equality or iff proposition"),
    ("Finset_le_prod_nonempty_of_submultiplicative", "f_i_in_s_g_i_le_i_in_s_f_g_i", "Not an equality or iff proposition"),
    ("Finset_le_prod_of_submultiplicative_on_pred", "f_i_in_s_g_i_le_i_in_s_f_g_i", "Not an equality or iff proposition"),
    ("Finset_le_prod_of_submultiplicative", "f_i_in_s_g_i_le_i_in_s_f_g_i", "Not an equality or iff proposition"),
    ("Finset_prod_le_prod", "_unknown", "Empty proposition"),
    ("Finset_single_le_prod", "_unknown", "Empty proposition"),
    ("Finset_mul_le_prod", "f_i_star_f_j_le_k_in_s_f_k", "Not an equality or iff proposition"),
    ("Finset_prod_image_le_of_one_le", "u_in_s_image_g_f_u_le_u_in_s_f_g_u", "Not an equality or iff proposition"),
    ("Finset_prod_le_prod", "i_in_s_f_i_le_i_in_s_g_i", "Not an equality or iff proposition"),
    ("Int_le_ceil", "a_le_a", "Not an equality or iff proposition"),
    ("Int_lt_succ_floor", "a_lt_a_succ", "Not an equality or iff proposition"),
    ("Int_preimage_floor_singleton", "floor_colon_R_to_inv_prime_m_eq_Ico_m_colon_R_m_plus_1", "Not an equality or iff proposition"),
    ("Nat_ceil_lt_add_one_of_gt_neg_one", "a_lt_a_plus_1", "Not an equality or iff proposition"),
    ("Nat_lt_succ_floor", "a_lt_a_succ", "Not an equality or iff proposition"),
    ("Finset_inf", "_unknown", "Empty proposition"),
    ("Finset_sup", "_unknown", "Empty proposition"),
    ("Finset_sup", "_unknown", "Empty proposition"),
    ("Finset_mul_sup", "_unknown", "Empty proposition"),
    ("Finset_sum_le_sum_Ioc", "x_in_s_x_le_x_in_Ioc_c_minus_hash_s_c_x", "Not an equality or iff proposition"),
    ("Finset_sum_le_sum_range", "x_in_s_x_le_n_in_range_hash_s_c_minus_n", "Not an equality or iff proposition"),
    ("Finset_sum_Ico_le_sum", "x_in_Ico_c_c_plus_hash_s_x_le_x_in_s_x", "Not an equality or iff proposition"),
    ("Finset_sum_range_le_sum", "n_in_range_hash_s_c_plus_n_le_x_in_s_x", "Not an equality or iff proposition"),
    ("Nat_pow_left_strictMono", "StrictMono_pow_n_colon_to", "Not an equality or iff proposition"),
    ("Int_natAbs_le_self_sq", "Int_natAbs_a_colon_le_a_pow_2", "Not an equality or iff proposition"),
    ("Int_le_self_sq", "b_le_b_pow_2", "Not an equality or iff proposition"),
    ("Finset_sup", "_unknown", "Empty proposition"),
    ("Finset_inf", "_unknown", "Empty proposition"),
    ("Interval_length_sub_le", "s_minus_t_length_le_s_length_plus_t_length", "Not an equality or iff proposition"),
    ("Interval_length_sum_le", "i_in_s_f_i_length_le_i_in_s_f_i_length", "Not an equality or iff proposition"),
    ("FiniteArchimedeanClass_ball_lt_closedBall", "ball_K_c_lt_closedBall_K_c", "Not an equality or iff proposition"),
    ("Finset_sup", "_unknown", "Empty proposition"),
    ("Int_le_abs_of_dvd", "a_le_pipe_bpipe", "Not an equality or iff proposition"),
    ("Nat_cast_finsetSup", "_unknown", "Empty proposition"),
    ("Nat_cast_finsetInf", "_unknown", "Empty proposition"),
    ("Nat_pred_mul_geom_sum_le", "b_minus_1_star_i_in_range_n_succ_a_slash_b_pow_i_le_a_star_b_minus_a_slash_b_pow_n", "Not an equality or iff proposition"),
    ("Nat_geom_sum_le", "i_in_range_n_a_slash_b_pow_i_le_a_star_b_slash_b_minus_1", "Not an equality or iff proposition"),
    ("Nat_geom_sum_Ico_le", "i_in_Ico_1_n_a_slash_b_pow_i_le_a_slash_b_minus_1", "Not an equality or iff proposition"),
    ("Nat_geomSum_lt", "k_in_s_m_pow_k_lt_m_pow_n", "Not an equality or iff proposition"),
    ("Int_Odd_of_mul_left", "Odd_m", "Not an equality or iff proposition"),
    ("Int_even_mul_succ_self", "Even_n_star_n_plus_1", "Not an equality or iff proposition"),
    ("Int_even_mul_pred_self", "Even_n_star_n_minus_1", "Not an equality or iff proposition"),
    ("Nat_Odd_of_mul_left", "Odd_m", "Not an equality or iff proposition"),
    ("BoxIntegral_Integrable_hasIntegral", "HasIntegral_I_l_f_vol_integral_I_l_f_vol", "Not an equality or iff proposition"),
    ("BoxIntegral_Integrable_mono", "Integrable_I_l_prime_f_vol", "Not an equality or iff proposition"),
    ("BoxIntegral_Integrable_add", "Integrable_I_l_f_plus_g_vol", "Not an equality or iff proposition"),
    ("BoxIntegral_Integrable_smul", "Integrable_I_l_c_f_vol", "Not an equality or iff proposition"),
    ("BoxIntegral_Integrable_of_smul", "Integrable_I_l_f_vol", "Not an equality or iff proposition"),
    ("BoxIntegral_Integrable_convergenceR_cond", "l_RCond_h_convergenceR_e_c", "Not an equality or iff proposition"),
    ("BoxIntegral_Integrable_tendsto_integralSum_toFilter_prod_self_inf_iUnion_eq_uniformity", "Tendsto_fun_pi_colon_TaggedPrepartition_I_times_TaggedPrepartition_I_eq_gt_integralS", "Not an equality or iff proposition"),
    ("BoxIntegral_Integrable_cauchy_map_integralSum_toFilteriUnion", "Cauchy_l_toFilteriUnion_I_pi_0_map_integralSum_f_vol", "Not an equality or iff proposition"),
    ("BoxIntegral_Integrable_to_subbox_aux", "exists_y_colon_F_HasIntegral_J_l_f_vol_y_and_Tendsto_integralSum_f_vol_l_toFilter", "Not an equality or iff proposition"),
    ("BoxIntegral_Integrable_tendsto_integralSum_toFilteriUnion_single", "Tendsto_integralSum_f_vol_l_toFilteriUnion_I_Prepartition_single_I_J_hJ", "Not an equality or iff proposition"),
    ("BoxIntegral_Integrable_tendsto_integralSum_sum_integral", "Tendsto_integralSum_f_vol_l_toFilteriUnion_I_pi_0_lt_pipe_J_in_pi_0_boxes", "Not an equality or iff proposition"),
    ("BoxIntegral_IntegrationParams_henstock_le_riemann", "Henstock_le_Riemann", "Not an equality or iff proposition"),
    ("BoxIntegral_IntegrationParams_henstock_le_mcShane", "Henstock_le_McShane", "Not an equality or iff proposition"),
    ("BoxIntegral_IntegrationParams_gp_le", "GP_le_l", "Not an equality or iff proposition"),
    ("BoxIntegral_IntegrationParams_tendsto_embedBox_toFilteriUnion_top", "Tendsto_TaggedPrepartition_embedBox_I_J_h_l_toFilteriUnion_I_top_l_toFi", "Not an equality or iff proposition"),
    ("BoxIntegral_IntegrationParams_eventually_isPartition", "forall_pi_in_l_toFilteriUnion_I_top_TaggedPrepartition_IsPartition_pi", "Not an equality or iff proposition"),
    ("Complex_nhdsWithin_lt_le_nhdsWithin_stolzSet", "lt_1_map_ofReal_le_stolzSet_M_1", "Not an equality or iff proposition"),
    ("Real_tendsto_tsum_powerSeries_nhdsWithin_lt", "Tendsto_fun_x_prime_n_f_n_star_x_pow_n_lt_1_l", "Not an equality or iff proposition"),
    ("Complex_isClosed_range_intCast", "IsClosed_Set_range_colon_to", "Not an equality or iff proposition"),
    ("Complex_isAddQuotientCoveringMap_exp", "IsAddQuotientCoveringMap_fun_z_colon_z_exp_ne_zero_colon_z_colon_slash_slash_z_ne_0", "Not an equality or iff proposition"),
    ("Real_sum_le_exp_of_nonneg", "i_in_range_n_x_pow_i_slash_i_bang_le_exp_x", "Not an equality or iff proposition"),
    ("Real_exp_abs_le", "exp_pipe_xpipe_le_exp_x_plus_exp_minus_x", "Not an equality or iff proposition"),
    ("Real_exp_lt_exp_of_lt", "exp_x_lt_exp_y", "Not an equality or iff proposition"),
    ("Real_exp_le_exp_of_le", "exp_x_le_exp_y", "Not an equality or iff proposition"),
    ("Complex_sum_div_factorial_le", "m_in_range_j_with_n_le_m_1_slash_m_factorial_colon_a_le_n_succ_slash_n_factorial_star_n", "Not an equality or iff proposition"),
    ("Complex_exp_bound", "exp_x_minus_m_in_range_n_x_pow_m_slash_m_factorial_le_x_pow_n_star_n_succ_colon_star", "Not an equality or iff proposition"),
    ("Complex_norm_exp_sub_sum_le_exp_norm_sub_sum", "exp_x_minus_m_in_range_n_x_pow_m_slash_m_factorial_le_Real_exp_x_minus_m_in_range", "Not an equality or iff proposition"),
    ("Complex_norm_exp_sub_sum_le_norm_mul_exp", "exp_x_minus_m_in_range_n_x_pow_m_slash_m_factorial_le_x_pow_n_star_Real_exp_x", "Not an equality or iff proposition"),
    ("Real_exp_approx_succ", "pipe_exp_x_minus_expNear_n_x_a_1pipe_le_pipe_xpipe_pow_n_slash_n_factorial_star_b_1", "Not an equality or iff proposition"),
    ("Real_exp_1_approx_succ_eq", "pipe_exp_1_minus_expNear_n_1_a_1pipe_le_pipe_1pipe_pow_n_slash_n_factorial_star_b_1", "Not an equality or iff proposition"),
    ("Real_log_two_gt_d9", "_0_6931471803_lt_log_2", "Not an equality or iff proposition"),
    ("Real_log_two_lt_d9", "log_2_lt_0_6931471808", "Not an equality or iff proposition"),
    ("Complex_HadamardThreeLines_norm_lt_sSupNormIm_eps", "f_z_lt_e_plus_sSupNormIm_f_z_re", "Not an equality or iff proposition"),
    ("Complex_HadamardThreeLines_F_edge_le_one", "F_f_e_z_le_1", "Not an equality or iff proposition"),
    ("Complex_isOpen_re_lt_EReal", "IsOpen_z_colon_pipe_z_re_lt_x", "Not an equality or iff proposition"),
    ("Complex_isOpen_re_gt_EReal", "IsOpen_z_colon_pipe_x_lt_z_re", "Not an equality or iff proposition"),
    ("Complex_isOpen_im_lt_EReal", "IsOpen_z_colon_pipe_z_im_lt_x", "Not an equality or iff proposition"),
    ("Complex_isOpen_im_gt_EReal", "IsOpen_z_colon_pipe_x_lt_z_im", "Not an equality or iff proposition"),
    ("UpperHalfPlane_coe_mem_integerComplement", "z_in", "Not an equality or iff proposition"),
    ("Complex_integerComplement_ne_zero", "x_ne_0", "Not an equality or iff proposition"),
    ("Complex_integerComplement_add_ne_zero", "x_plus_a_colon_ne_0", "Not an equality or iff proposition"),
    ("Complex_integerComplement_ne_one", "x_ne_1", "Not an equality or iff proposition"),
    ("Complex_integerComplement_pow_two_ne_pow_two", "x_pow_2_ne_n_pow_2", "Not an equality or iff proposition"),
    ("UpperHalfPlane_int_div_mem_integerComplement", "n_slash_z_colon_in", "Not an equality or iff proposition"),
    ("Complex_norm_cderiv_lt", "cderiv_r_f_z_lt_M_slash_r", "Not an equality or iff proposition"),
    ("Complex_norm_cderiv_sub_lt", "cderiv_r_f_z_minus_cderiv_r_g_z_lt_M_slash_r", "Not an equality or iff proposition"),
    ("Complex_range_norm", "range_colon_to_eq_Set_Ici_0", "Not an equality or iff proposition"),
    ("Real_sinh_lt_cosh", "sinh_x_lt_cosh_x", "Not an equality or iff proposition"),
    ("Real_sin_pos_of_pos_of_le_two", "_0_lt_sin_x", "Not an equality or iff proposition"),
    ("Complex_UnitDisc_norm_lt_one", "z_colon_lt_1", "Not an equality or iff proposition"),
    ("Complex_UnitDisc_sq_norm_lt_one", "z_colon_pow_2_lt_1", "Not an equality or iff proposition"),
    ("Complex_UnitDisc_normSq_lt_one", "normSq_z_lt_1", "Not an equality or iff proposition"),
    ("Real_exp_mul_le_cosh_add_mul_sinh", "exp_t_star_x_le_cosh_x_plus_t_star_sinh_x", "Not an equality or iff proposition"),
    ("Integrable_integrable_convolution", "Integrable_f_L_mu_g_mu", "Not an equality or iff proposition"),
    ("Real_pow_mul_norm_iteratedFDeriv_fourier_le", "w_pow_n_star_iteratedFDeriv_k_f_w_le_2_star_pi_pow_k_star_2_star_k_plus_2_pow_n_star", "Not an equality or iff proposition"),
    ("Real_geom_mean_le_arith_mean_weighted", "i_in_s_z_i_pow_w_i_le_i_in_s_w_i_star_z_i", "Not an equality or iff proposition"),
    ("Real_geom_mean_le_arith_mean", "i_in_s_z_i_pow_w_i_pow_i_in_s_w_i_inv_le_i_in_s_w_i_star_z_i_slash_i_in_s_w_i", "Not an equality or iff proposition"),
    ("Real_geom_mean_le_arith_mean2_weighted", "p_1_pow_w_1_star_p_2_pow_w_2_le_w_1_star_p_1_plus_w_2_star_p_2", "Not an equality or iff proposition"),
    ("Real_geom_mean_le_arith_mean3_weighted", "p_1_pow_w_1_star_p_2_pow_w_2_star_p_3_pow_w_3_le_w_1_star_p_1_plus_w_2_star_p_2_plus_w_3_star_p_3", "Not an equality or iff proposition"),
    ("Real_geom_mean_le_arith_mean4_weighted", "p_1_pow_w_1_star_p_2_pow_w_2_star_p_3_pow_w_3_star_p_4_pow_w_4_le_w_1_star_p_1_plus_w_2_star_p_2_plus_w_3_star_p_3_plus_w_4_star_p_4", "Not an equality or iff proposition"),
    ("Real_harm_mean_le_geom_mean_weighted", "i_in_s_w_i_slash_z_i_inv_le_i_in_s_z_i_pow_w_i", "Not an equality or iff proposition"),
    ("Real_harm_mean_le_geom_mean", "i_in_s_w_i_slash_i_in_s_w_i_slash_z_i_le_i_in_s_z_i_pow_w_i_pow_i_in_s_w_i_inv", "Not an equality or iff proposition"),
    ("Real_Lr_rpow_le_Lp_mul_Lq", "i_in_s_pipe_f_i_star_g_ipipe_pow_r_le_i_in_s_pipe_f_ipipe_pow_p_pow_r_slash_p_star_i_in_s_pipe_g_ipipe_pow_q", "Not an equality or iff proposition"),
    ("Real_inner_le_Lp_mul_Lq", "i_in_s_f_i_star_g_i_le_i_in_s_pipe_f_ipipe_pow_p_pow_1_slash_p_star_i_in_s_pipe_g_ipipe_pow_q_pow_1", "Not an equality or iff proposition"),
    ("Real_Lp_add_le", "i_in_s_pipe_f_i_plus_g_ipipe_pow_p_pow_1_slash_p_le_i_in_s_pipe_f_ipipe_pow_p_pow_1_slash_p_plus", "Not an equality or iff proposition"),
    ("Real_pow_arith_mean_le_arith_mean_pow", "i_in_s_w_i_star_z_i_pow_n_le_i_in_s_w_i_star_z_i_pow_n", "Not an equality or iff proposition"),
    ("Real_pow_arith_mean_le_arith_mean_pow_of_even", "i_in_s_w_i_star_z_i_pow_n_le_i_in_s_w_i_star_z_i_pow_n", "Not an equality or iff proposition"),
    ("Real_rpow_arith_mean_le_arith_mean_rpow", "i_in_s_w_i_star_z_i_pow_p_le_i_in_s_w_i_star_z_i_pow_p", "Not an equality or iff proposition"),
    ("Real_arith_mean_le_rpow_mean", "i_in_s_w_i_star_z_i_le_i_in_s_w_i_star_z_i_pow_p_pow_1_slash_p", "Not an equality or iff proposition"),
    ("Real_add_rpow_le_rpow_add", "a_pow_p_plus_b_pow_p_le_a_plus_b_pow_p", "Not an equality or iff proposition"),
    ("Real_rpow_add_rpow_le_add", "a_pow_p_plus_b_pow_p_pow_1_slash_p_le_a_plus_b", "Not an equality or iff proposition"),
    ("Real_rpow_add_rpow_le", "a_pow_q_plus_b_pow_q_pow_1_slash_q_le_a_pow_p_plus_b_pow_p_pow_1_slash_p", "Not an equality or iff proposition"),
    ("Real_rpow_add_le_add_rpow", "a_plus_b_pow_p_le_a_pow_p_plus_b_pow_p", "Not an equality or iff proposition"),
    ("Finset_le_sum_schlomilch", "_unknown", "Empty proposition"),
    ("Finset_le_sum_condensed", "_unknown", "Empty proposition"),
    ("Finset_le_sum_schlomilch", "k_in_range_u_n_f_k_le_k_in_range_u_0_f_k_plus_k_in_range_n_u_k_plus", "Not an equality or iff proposition"),
    ("Finset_le_sum_condensed", "k_in_range_2_pow_n_f_k_le_f_0_plus_k_in_range_n_2_pow_k_f_2_pow_k", "Not an equality or iff proposition"),
    ("Finset_sum_schlomilch_le", "_unknown", "Empty proposition"),
    ("Finset_sum_condensed_le", "_unknown", "Empty proposition"),
    ("Finset_sum_schlomilch_le", "k_in_range_n_plus_1_u_k_plus_1_minus_u_k_f_u_k_le_u_1_minus_u_0_f_u_0_plus_C", "Not an equality or iff proposition"),
    ("Finset_sum_condensed_le", "k_in_range_n_plus_1_2_pow_k_f_2_pow_k_le_f_1_plus_2_k_in_Ico_2_2_pow_n_plus_1_f", "Not an equality or iff proposition"),
    ("Real_ofDigitsTerm_le", "ofDigitsTerm_digits_n_le_b_minus_1_star_b_colon_pow_n_plus_1_inv", "Not an equality or iff proposition"),
    ("Real_le_sum_ofDigitsTerm_digits", "x_minus_binv_colon_pow_n_le_i_in_Finset_range_n_ofDigitsTerm_digits_x_b_i", "Not an equality or iff proposition"),
    ("Real_sum_ofDigitsTerm_digits_le", "i_in_Finset_range_n_ofDigitsTerm_digits_x_b_i_le_x", "Not an equality or iff proposition"),
    ("Real_pi_gt_sqrtTwoAddSeries", "_2_pow_n_plus_1_star_2_minus_sqrtTwoAddSeries_0_n_lt_pi", "Not an equality or iff proposition"),
    ("Real_pi_lt_sqrtTwoAddSeries", "pi_lt_2_pow_n_plus_1_star_2_minus_sqrtTwoAddSeries_0_n_plus_1_slash_4_pow_n", "Not an equality or iff proposition"),
    ("Real_Wallis_W_le", "W_k_le_pi_slash_2", "Not an equality or iff proposition"),
    ("Real_Wallis_le_W", "_2_colon_star_k_plus_1_slash_2_star_k_plus_2_star_pi_slash_2_le_W_k", "Not an equality or iff proposition"),
    ("Real_artanh_le_artanh", "artanh_x_le_artanh_y", "Not an equality or iff proposition"),
    ("Real_artanh_lt_artanh", "artanh_x_lt_artanh_y", "Not an equality or iff proposition"),
    ("Real_binEntropy_le_log_two", "binEntropy_p_le_log_2", "Not an equality or iff proposition"),
    ("Complex_IsExpCmpFilter_of_isBigO_im_re_rpow", "IsExpCmpFilter_l", "Not an equality or iff proposition"),
    ("Complex_IsExpCmpFilter_of_isBigO_im_re_pow", "IsExpCmpFilter_l", "Not an equality or iff proposition"),
    ("Complex_IsExpCmpFilter_of_boundedUnder_abs_im", "IsExpCmpFilter_l", "Not an equality or iff proposition"),
    ("Complex_IsExpCmpFilter_of_boundedUnder_im", "IsExpCmpFilter_l", "Not an equality or iff proposition"),
    ("Complex_IsExpCmpFilter_eventually_ne", "forall_w_colon_in_l_w_ne_0", "Not an equality or iff proposition"),
    ("Complex_IsExpCmpFilter_tendsto_abs_re", "Tendsto_fun_z_colon_eq_gt_pipe_z_repipe_l_atTop", "Not an equality or iff proposition"),
    ("Complex_IsExpCmpFilter_tendsto_norm", "Tendsto_norm_l_atTop", "Not an equality or iff proposition"),
    ("Complex_neg_pi_lt_arg", "minus_pi_lt_arg_x", "Not an equality or iff proposition"),
    ("Complex_neg_pi_lt_log_im", "minus_pi_lt_log_x_im", "Not an equality or iff proposition"),
    ("Complex_hasDerivAt_logTaylor", "HasDerivAt_logTaylor_n_plus_1_j_in_Finset_range_n_minus_1_pow_j_star_z_pow_j_z", "Not an equality or iff proposition"),
    ("Real_summable_exp_nat_mul_of_ge", "Summable_fun_i_colon_exp_c_star_f_i", "Not an equality or iff proposition"),
    ("Real_GammaIntegral_convergent", "IntegrableOn_fun_x_colon_eq_gt_exp_minus_x_star_x_pow_s_minus_1_Ioi_0", "Not an equality or iff proposition"),
    ("Complex_GammaIntegral_convergent", "IntegrableOn_fun_x_eq_gt_minus_x_exp_star_x_pow_s_minus_1_colon_to_Ioi_0", "Not an equality or iff proposition"),
    ("Complex_betaIntegral_convergent_left", "IntervalIntegrable_fun_x_eq_gt_x_colon_pow_u_minus_1_star_1_minus_x_colon_pow_v_minus_1_colon", "Not an equality or iff proposition"),
    ("Complex_betaIntegral_convergent", "IntervalIntegrable_fun_x_eq_gt_x_colon_pow_u_minus_1_star_1_minus_x_colon_pow_v_minus_1_colon", "Not an equality or iff proposition"),
    ("Real_Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma", "Gamma_a_star_s_plus_b_star_t_le_Gamma_s_pow_a_star_Gamma_t_pow_b", "Not an equality or iff proposition"),
    ("Real_le_exp_log", "x_le_exp_log_x", "Not an equality or iff proposition"),
    ("Real_two_mul_le_exp", "_2_star_x_le_exp_x", "Not an equality or iff proposition"),
    ("Real_log_le_log", "log_x_le_log_y", "Not an equality or iff proposition"),
    ("Real_log_lt_log", "log_x_lt_log_y", "Not an equality or iff proposition"),
    ("Real_log_le_self", "log_x_le_x", "Not an equality or iff proposition"),
    ("Real_abs_log_mul_self_lt", "pipe_log_x_star_xpipe_lt_1", "Not an equality or iff proposition"),
    ("Real_abs_log_sub_add_sum_range_le", "pipe_i_in_range_n_x_pow_i_plus_1_slash_i_plus_1_plus_log_1_minus_x_pipe_le_pipe_xpipe_pow_n_plus_1_slash_1_minus_pipe_x", "Not an equality or iff proposition"),
    ("Real_sum_range_sub_log_div_le", "pipe_1_slash_2_star_log_1_plus_x_slash_1_minus_x_minus_i_in_range_n_x_pow_2_star_i_plus_1_slash_2_star_i_plus_1_pipe", "Not an equality or iff proposition"),
    ("Real_sum_range_le_log_div", "i_in_range_n_x_pow_2_star_i_plus_1_slash_2_star_i_plus_1_le_1_slash_2_star_log_1_plus_x_slash_1_minus_x", "Not an equality or iff proposition"),
    ("Real_log_div_le_sum_range_add", "_1_slash_2_star_log_1_plus_x_slash_1_minus_x_le_i_in_range_n_x_pow_2_star_i_plus_1_slash_2_star_i", "Not an equality or iff proposition"),
    ("Real_posLog_le_posLog", "logpos_x_le_logpos_y", "Not an equality or iff proposition"),
    ("Complex_multipliable_of_summable_log", "Multipliable_f", "Not an equality or iff proposition"),
    ("Complex_multipliable_one_add_of_summable", "Multipliable_fun_i_1_plus_f_i", "Not an equality or iff proposition"),
    ("Real_multipliable_of_summable_log", "Multipliable_f", "Not an equality or iff proposition"),
    ("Real_multipliable_of_summable_log", "_unknown", "Empty proposition"),
    ("Real_multipliable_one_add_of_summable", "Multipliable_fun_i_1_plus_f_i", "Not an equality or iff proposition"),
    ("Real_abs_rpow_le_abs_rpow", "pipe_x_pow_ypipe_le_pipe_xpipe_pow_y", "Not an equality or iff proposition"),
    ("Real_abs_rpow_le_exp_log_mul", "pipe_x_pow_ypipe_le_exp_log_x_star_y", "Not an equality or iff proposition"),
    ("Real_le_rpow_add", "x_pow_y_star_x_pow_z_le_x_pow_y_plus_z", "Not an equality or iff proposition"),
    ("Real_rpow_lt_rpow", "x_pow_z_lt_y_pow_z", "Not an equality or iff proposition"),
    ("Real_rpow_le_rpow", "x_pow_z_le_y_pow_z", "Not an equality or iff proposition"),
    ("Real_rpow_le_rpow_of_nonpos", "y_pow_z_le_x_pow_z", "Not an equality or iff proposition"),
]
