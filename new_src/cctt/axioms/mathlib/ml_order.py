"""Mathlib: Order — auto-generated from Mathlib4.

Contains 400 rewrite rules derived from Mathlib theorems.
Plus 3733 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_order"
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

def _r0000_map_one_of_isLeftRegular(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AbsoluteValue.map_one_of_isLeftRegular
    # abv 1 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "abv", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: AbsoluteValue_map_one_of_isLeftRegular"))
        except Exception:
            pass
    return results


def _r0001_map_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: map_pow
    # abv (a ^ n) = abv a ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "abv", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("abv", (OVar("a"),)), OVar("n")))
            results.append((rhs, "Mathlib: map_pow"))
        except Exception:
            pass
    return results


def _r0002_add_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: add_top
    # a + ⊤ = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: add_top"))
        except Exception:
            pass
    return results


def _r0003_add_right_inj_of_ne_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: add_right_inj_of_ne_top
    # a + b = a + c ↔ b = c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("+", (args[0], OVar("c"))), args[1])), OVar("c")))
            results.append((rhs, "Mathlib: add_right_inj_of_ne_top"))
        except Exception:
            pass
    return results


def _r0004_neg_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: LinearOrderedAddCommGroupWithTop.neg_eq_top
    # -a = ⊤ ↔ a = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("top"), OVar("a"))), OVar("top")))
            results.append((rhs, "Mathlib: LinearOrderedAddCommGroupWithTop_neg_eq_top"))
    except Exception:
        pass
    return results


def _r0005_sub_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: LinearOrderedAddCommGroupWithTop.sub_top
    # a - ⊤ = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: LinearOrderedAddCommGroupWithTop_sub_top"))
        except Exception:
            pass
    return results


def _r0006_sub_right_inj_of_ne_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: LinearOrderedAddCommGroupWithTop.sub_right_inj_of_ne_top
    # a - b = a - c ↔ b = c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("-", (args[0], OVar("c"))), args[1])), OVar("c")))
            results.append((rhs, "Mathlib: LinearOrderedAddCommGroupWithTop_sub_right_inj_of_ne_top"))
        except Exception:
            pass
    return results


def _r0007_add_neg_cancel_iff_ne_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: LinearOrderedAddCommGroupWithTop.add_neg_cancel_iff_ne_top
    # a + -a = 0 ↔ a ≠ ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("iff", (OLit(0), args[0])), OVar("top")))
            results.append((rhs, "Mathlib: LinearOrderedAddCommGroupWithTop_add_neg_cancel_iff_ne_top"))
        except Exception:
            pass
    return results


def _r0008_coe_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithTop.LinearOrderedAddCommGroup.coe_sub
    # (↑(a - b) : WithTop G) = ↑a - ↑b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_minus_b", 3)
    if args is not None:
        try:
            rhs = OOp("-", (OVar("a"), OVar("b")))
            results.append((rhs, "Mathlib: WithTop_LinearOrderedAddCommGroup_coe_sub"))
        except Exception:
            pass
    return results


def _r0009_neg_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithTop.LinearOrderedAddCommGroup.neg_top
    # -(⊤ : WithTop G) = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_top_colon_WithTop_G")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: WithTop_LinearOrderedAddCommGroup_neg_top"))
    except Exception:
        pass
    return results


def _r0010_top_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithTop.LinearOrderedAddCommGroup.top_sub
    # ⊤ - x = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: WithTop_LinearOrderedAddCommGroup_top_sub"))
        except Exception:
            pass
    return results


def _r0011_sub_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithTop.LinearOrderedAddCommGroup.sub_top
    # x - ⊤ = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: WithTop_LinearOrderedAddCommGroup_sub_top"))
        except Exception:
            pass
    return results


def _r0012_sub_eq_top_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithTop.LinearOrderedAddCommGroup.sub_eq_top_iff
    # x - y = ⊤ ↔ x = ⊤ ∨ y = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("top"), args[0])), OOp("==", (OOp("or", (OVar("top"), args[1])), OVar("top")))))
            results.append((rhs, "Mathlib: WithTop_LinearOrderedAddCommGroup_sub_eq_top_iff"))
        except Exception:
            pass
    return results


def _r0013_add_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CauSeq.add_apply
    # (f + g) i = f i + g i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_plus_g", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("f", (args[0],)), OOp("g", (args[0],))))
            results.append((rhs, "Mathlib: CauSeq_add_apply"))
        except Exception:
            pass
    return results


def _r0014_const_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CauSeq.const_inj
    # (const x : CauSeq β abv) = const y ↔ x = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "const", 5)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("const", (OVar("y"),)), args[0])), OVar("y")))
            results.append((rhs, "Mathlib: CauSeq_const_inj"))
        except Exception:
            pass
    return results


def _r0015_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CauSeq.coe_one
    # ⇑(1 : CauSeq β abv) = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_CauSeq_b_abv")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: CauSeq_coe_one"))
    except Exception:
        pass
    return results


def _r0016_zero_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CauSeq.zero_apply
    # (0 : CauSeq β abv) i = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_CauSeq_b_abv", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CauSeq_zero_apply"))
        except Exception:
            pass
    return results


def _r0017_one_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CauSeq.one_apply
    # (1 : CauSeq β abv) i = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_CauSeq_b_abv", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: CauSeq_one_apply"))
        except Exception:
            pass
    return results


def _r0018_const_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CauSeq.const_zero
    # const 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "const", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CauSeq_const_zero"))
        except Exception:
            pass
    return results


def _r0019_const_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CauSeq.const_one
    # const 1 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "const", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: CauSeq_const_one"))
        except Exception:
            pass
    return results


def _r0020_const_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CauSeq.const_add
    # const (x + y) = const x + const y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "const", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("const", (OVar("x"),)), OOp("const", (OVar("y"),))))
            results.append((rhs, "Mathlib: CauSeq_const_add"))
        except Exception:
            pass
    return results


def _r0021_mul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CauSeq.mul_apply
    # (f * g) i = f i * g i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_star_g", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("f", (args[0],)), OOp("g", (args[0],))))
            results.append((rhs, "Mathlib: CauSeq_mul_apply"))
        except Exception:
            pass
    return results


def _r0022_const_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CauSeq.const_mul
    # const (x * y) = const x * const y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "const", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("const", (OVar("x"),)), OOp("const", (OVar("y"),))))
            results.append((rhs, "Mathlib: CauSeq_const_mul"))
        except Exception:
            pass
    return results


def _r0023_neg_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CauSeq.neg_apply
    # (-f) i = -f i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minus_f", 1)
    if args is not None:
        try:
            rhs = OOp("minus_f", (args[0],))
            results.append((rhs, "Mathlib: CauSeq_neg_apply"))
        except Exception:
            pass
    return results


def _r0024_const_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CauSeq.const_neg
    # const (-x) = -const x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "const", 1)
    if args is not None:
        try:
            rhs = OOp("minus_const", (OVar("x"),))
            results.append((rhs, "Mathlib: CauSeq_const_neg"))
        except Exception:
            pass
    return results


def _r0025_sub_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CauSeq.sub_apply
    # (f - g) i = f i - g i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_minus_g", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("f", (args[0],)), OOp("g", (args[0],))))
            results.append((rhs, "Mathlib: CauSeq_sub_apply"))
        except Exception:
            pass
    return results


def _r0026_const_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CauSeq.const_sub
    # const (x - y) = const x - const y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "const", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("const", (OVar("x"),)), OOp("const", (OVar("y"),))))
            results.append((rhs, "Mathlib: CauSeq_const_sub"))
        except Exception:
            pass
    return results


def _r0027_smul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CauSeq.smul_apply
    # (a • f) i = a • f i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_f", 1)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("f"), args[0],))
            results.append((rhs, "Mathlib: CauSeq_smul_apply"))
        except Exception:
            pass
    return results


def _r0028_const_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CauSeq.const_smul
    # const (a • x) = a • const x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "const", 1)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("const"), OVar("x"),))
            results.append((rhs, "Mathlib: CauSeq_const_smul"))
        except Exception:
            pass
    return results


def _r0029_pow_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_apply
    # (f ^ n) i = f i ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_pow_n", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("f", (args[0],)), OVar("n")))
            results.append((rhs, "Mathlib: pow_apply"))
        except Exception:
            pass
    return results


def _r0030_const_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: const_pow
    # const (x ^ n) = const x ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "const", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("const", (OVar("x"),)), OVar("n")))
            results.append((rhs, "Mathlib: const_pow"))
        except Exception:
            pass
    return results


def _r0031_inv_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inv_apply
    # inv f hf i = (f i)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inv", 3)
    if args is not None:
        try:
            rhs = OVar("f_i_inv")
            results.append((rhs, "Mathlib: inv_apply"))
        except Exception:
            pass
    return results


def _r0032_coe_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_inf
    # ⇑(f ⊓ g) = (f : ℕ → α) ⊓ g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_colon_to_a", (OVar("_unknown"), OVar("g"),))
            results.append((rhs, "Mathlib: coe_inf"))
    except Exception:
        pass
    return results


def _r0033_sup_limZero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: sup_limZero
    # LimZero (f ⊔ g)   | ε, ε0 =>     (exists_forall_ge_and (hf _ ε0) (hg _ ε0)).imp fun _ H j ij =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LimZero", 4)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("exists_forall_ge_and_hf_e0_hg_e0_imp"), OVar("fun"), OVar("_unknown"), OVar("H"), OVar("j"), OVar("ij"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: sup_limZero"))
        except Exception:
            pass
    return results


def _r0034_inf_idem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inf_idem
    # a ⊓ a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: inf_idem"))
        except Exception:
            pass
    return results


def _r0035_sup_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: sup_comm
    # a ⊔ b = b ⊔ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("b", (args[0], OVar("a"),))
            results.append((rhs, "Mathlib: sup_comm"))
        except Exception:
            pass
    return results


def _r0036_mk_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CauSeq.Completion.mk_eq
    # mk f = mk g ↔ LimZero (f - g)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OOp("pair", (OVar("g"),)), OOp("LimZero", (OOp("-", (args[0], OVar("g"))),))))
            results.append((rhs, "Mathlib: CauSeq_Completion_mk_eq"))
        except Exception:
            pass
    return results


def _r0037_ofRat_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CauSeq.Completion.ofRat_intCast
    # (ofRat z : Cauchy abv) = z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofRat", 4)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: CauSeq_Completion_ofRat_intCast"))
        except Exception:
            pass
    return results


def _r0038_ofRat_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CauSeq.Completion.ofRat_add
    # ofRat (x + y) = (ofRat x + ofRat y : Cauchy abv)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofRat", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("ofRat", (OVar("x"),)), OOp("ofRat", (OVar("y"), OVar("colon"), OVar("Cauchy"), OVar("abv"),))))
            results.append((rhs, "Mathlib: CauSeq_Completion_ofRat_add"))
        except Exception:
            pass
    return results


def _r0039_ofRat_ratCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofRat_ratCast
    # ofRat (q : β) = (q : Cauchy abv)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofRat", 1)
    if args is not None:
        try:
            rhs = OOp("q", (OVar("colon"), OVar("Cauchy"), OVar("abv"),))
            results.append((rhs, "Mathlib: ofRat_ratCast"))
        except Exception:
            pass
    return results


def _r0040_lim_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: lim_add
    # lim f + lim g = lim (f + g)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("lim", (OOp("+", (OVar("f"), OVar("g"))),))
            results.append((rhs, "Mathlib: lim_add"))
        except Exception:
            pass
    return results


def _r0041_inducedMap_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ConditionallyCompleteLinearOrderedField.inducedMap_one
    # inducedMap α β 1 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inducedMap", 3)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ConditionallyCompleteLinearOrderedField_inducedMap_one"))
        except Exception:
            pass
    return results


def _r0042_inducedOrderRingIso_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ConditionallyCompleteLinearOrderedField.inducedOrderRingIso_symm
    # (inducedOrderRingIso β γ).symm = inducedOrderRingIso γ β
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("inducedOrderRingIso_b_g_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("inducedOrderRingIso", (OVar("g"), OVar("b"),))
            results.append((rhs, "Mathlib: ConditionallyCompleteLinearOrderedField_inducedOrderRingIso_symm"))
    except Exception:
        pass
    return results


def _r0043_inducedOrderRingIso_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ConditionallyCompleteLinearOrderedField.inducedOrderRingIso_self
    # inducedOrderRingIso β β = OrderRingIso.refl β
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inducedOrderRingIso", 2)
    if args is not None:
        try:
            rhs = OOp("OrderRingIso_refl", (args[1],))
            results.append((rhs, "Mathlib: ConditionallyCompleteLinearOrderedField_inducedOrderRingIso_self"))
        except Exception:
            pass
    return results


def _r0044_abs_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: abs_div
    # |a / b| = |a| / |b|
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("pipe_apipe"), OVar("pipe_bpipe")))
            results.append((rhs, "Mathlib: abs_div"))
        except Exception:
            pass
    return results


def _r0045_abs_neg_one_zpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: abs_neg_one_zpow
    # |(-1 : α) ^ p| = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: abs_neg_one_zpow"))
        except Exception:
            pass
    return results


def _r0046_floorDiv_of_nonpos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: floorDiv_of_nonpos
    # b ⌊/⌋ a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "b", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: floorDiv_of_nonpos"))
        except Exception:
            pass
    return results


def _r0047_floorDiv_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: floorDiv_zero
    # b ⌊/⌋ (0 : α) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "b", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: floorDiv_zero"))
        except Exception:
            pass
    return results


def _r0048_zero_floorDiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: zero_floorDiv
    # (0 : β) ⌊/⌋ a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_b", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: zero_floorDiv"))
        except Exception:
            pass
    return results


def _r0049_ceilDiv_of_nonpos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ceilDiv_of_nonpos
    # b ⌈/⌉ a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "b", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ceilDiv_of_nonpos"))
        except Exception:
            pass
    return results


def _r0050_ceilDiv_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ceilDiv_zero
    # b ⌈/⌉ (0 : α) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "b", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ceilDiv_zero"))
        except Exception:
            pass
    return results


def _r0051_zero_ceilDiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: zero_ceilDiv
    # (0 : β) ⌈/⌉ a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_b", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: zero_ceilDiv"))
        except Exception:
            pass
    return results


def _r0052_smul_floorDiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: smul_floorDiv
    # a • b ⌊/⌋ a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 4)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: smul_floorDiv"))
        except Exception:
            pass
    return results


def _r0053_smul_ceilDiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: smul_ceilDiv
    # a • b ⌈/⌉ a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 4)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: smul_ceilDiv"))
        except Exception:
            pass
    return results


def _r0054_ceil_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.ceil_top
    # ⌈∞⌉ₑ = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("inf")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: ENat_ceil_top"))
    except Exception:
        pass
    return results


def _r0055_floor_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.floor_coe
    # ⌊r⌋ₑ = ⌊r⌋₊
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("r")
            results.append((rhs, "Mathlib: ENat_floor_coe"))
    except Exception:
        pass
    return results


def _r0056_ceil_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.ceil_coe
    # ⌈r⌉ₑ = ⌈r⌉₊
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("r")
            results.append((rhs, "Mathlib: ENat_ceil_coe"))
    except Exception:
        pass
    return results


def _r0057_floor_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.floor_eq_top
    # ⌊r⌋ₑ = ⊤ ↔ r = ∞
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("top"), OVar("r"))), OVar("inf")))
            results.append((rhs, "Mathlib: ENat_floor_eq_top"))
    except Exception:
        pass
    return results


def _r0058_ceil_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.ceil_eq_top
    # ⌈r⌉ₑ = ⊤ ↔ r = ∞
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("top"), OVar("r"))), OVar("inf")))
            results.append((rhs, "Mathlib: ENat_ceil_eq_top"))
    except Exception:
        pass
    return results


def _r0059_ceil_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.ceil_natCast
    # ⌈n⌉ₑ = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: ENat_ceil_natCast"))
    except Exception:
        pass
    return results


def _r0060_floor_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.floor_zero
    # ⌊0⌋ₑ = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ENat_floor_zero"))
    except Exception:
        pass
    return results


def _r0061_ceil_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.ceil_zero
    # ⌈0⌉ₑ = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ENat_ceil_zero"))
    except Exception:
        pass
    return results


def _r0062_floor_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.floor_one
    # ⌊1⌋ₑ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ENat_floor_one"))
    except Exception:
        pass
    return results


def _r0063_ceil_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.ceil_one
    # ⌈1⌉ₑ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ENat_ceil_one"))
    except Exception:
        pass
    return results


def _r0064_floor_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.floor_ofNat
    # ⌊ofNat(n)⌋ₑ = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofNat_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("ofNat_n")
            results.append((rhs, "Mathlib: ENat_floor_ofNat"))
    except Exception:
        pass
    return results


def _r0065_ceil_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.ceil_ofNat
    # ⌈ofNat(n)⌉ₑ = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofNat_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("ofNat_n")
            results.append((rhs, "Mathlib: ENat_ceil_ofNat"))
    except Exception:
        pass
    return results


def _r0066_ceil_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.ceil_eq_zero
    # ⌈r⌉ₑ = 0 ↔ r = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("r"))), OLit(0)))
            results.append((rhs, "Mathlib: ENat_ceil_eq_zero"))
    except Exception:
        pass
    return results


def _r0067_ceil_le_floor_add_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.ceil_le_floor_add_one
    # ∀ r : ℝ≥0∞, ⌈r⌉ₑ ≤ ⌊r⌋ₑ + 1   | ∞ => le_rfl   | (r : ℝ≥0) =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("le_rfl"), OVar("pipe"), OOp("r", (OVar("colon"), OVar("ge_0"),)), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: ENat_ceil_le_floor_add_one"))
        except Exception:
            pass
    return results


def _r0068_ceil_toENNReal_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.ceil_toENNReal_add
    # ⌈n + r⌉ₑ = n + ⌈r⌉ₑ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], args[1]))
            results.append((rhs, "Mathlib: ENat_ceil_toENNReal_add"))
        except Exception:
            pass
    return results


def _r0069_floor_add_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.floor_add_natCast
    # ⌊r + n⌋ₑ = ⌊r⌋ₑ + n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], args[1]))
            results.append((rhs, "Mathlib: ENat_floor_add_natCast"))
        except Exception:
            pass
    return results


def _r0070_ceil_add_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.ceil_add_natCast
    # ⌈r + n⌉ₑ = ⌈r⌉ₑ + n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], args[1]))
            results.append((rhs, "Mathlib: ENat_ceil_add_natCast"))
        except Exception:
            pass
    return results


def _r0071_floor_natCast_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.floor_natCast_add
    # ⌊n + r⌋ₑ = n + ⌊r⌋ₑ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], args[1]))
            results.append((rhs, "Mathlib: ENat_floor_natCast_add"))
        except Exception:
            pass
    return results


def _r0072_ceil_natCast_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.ceil_natCast_add
    # ⌈n + r⌉ₑ = n + ⌈r⌉ₑ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], args[1]))
            results.append((rhs, "Mathlib: ENat_ceil_natCast_add"))
        except Exception:
            pass
    return results


def _r0073_floor_add_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.floor_add_one
    # ⌊r + 1⌋ₑ = ⌊r⌋ₑ + 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], OLit(1)))
            results.append((rhs, "Mathlib: ENat_floor_add_one"))
        except Exception:
            pass
    return results


def _r0074_ceil_add_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.ceil_add_one
    # ⌈r + 1⌉ₑ = ⌈r⌉ₑ + 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], OLit(1)))
            results.append((rhs, "Mathlib: ENat_ceil_add_one"))
        except Exception:
            pass
    return results


def _r0075_floor_add_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.floor_add_ofNat
    # ⌊r + ofNat(n)⌋ₑ = ⌊r⌋ₑ + ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], args[1]))
            results.append((rhs, "Mathlib: ENat_floor_add_ofNat"))
        except Exception:
            pass
    return results


def _r0076_ceil_add_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.ceil_add_ofNat
    # ⌈r + ofNat(n)⌉ₑ = ⌈r⌉ₑ + ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], args[1]))
            results.append((rhs, "Mathlib: ENat_ceil_add_ofNat"))
        except Exception:
            pass
    return results


def _r0077_floor_sub_toENNReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.floor_sub_toENNReal
    # ∀ (r : ℝ≥0∞) (n : ℕ∞), ⌊r - n⌋ₑ = ⌊r⌋ₑ - n   | ∞, ⊤ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("-", (args[0], OOp("n", (OVar("pipe"), OVar("inf"), OVar("top"), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: ENat_floor_sub_toENNReal"))
        except Exception:
            pass
    return results


def _r0078_ceil_sub_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.ceil_sub_natCast
    # ⌈r - n⌉ₑ = ⌈r⌉ₑ - n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("-", (args[0], args[1]))
            results.append((rhs, "Mathlib: ENat_ceil_sub_natCast"))
        except Exception:
            pass
    return results


def _r0079_floor_sub_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.floor_sub_one
    # ⌊r - 1⌋ₑ = ⌊r⌋ₑ - 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("-", (args[0], OLit(1)))
            results.append((rhs, "Mathlib: ENat_floor_sub_one"))
        except Exception:
            pass
    return results


def _r0080_ceil_sub_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.ceil_sub_one
    # ⌈r - 1⌉ₑ = ⌈r⌉ₑ - 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("-", (args[0], OLit(1)))
            results.append((rhs, "Mathlib: ENat_ceil_sub_one"))
        except Exception:
            pass
    return results


def _r0081_floor_sub_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.floor_sub_ofNat
    # ⌊r - ofNat(n)⌋ₑ = ⌊r⌋ₑ - ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("-", (args[0], args[1]))
            results.append((rhs, "Mathlib: ENat_floor_sub_ofNat"))
        except Exception:
            pass
    return results


def _r0082_ceil_sub_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.ceil_sub_ofNat
    # ⌈r - ofNat(n)⌉ₑ = ⌈r⌉ₑ - ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("-", (args[0], args[1]))
            results.append((rhs, "Mathlib: ENat_ceil_sub_ofNat"))
        except Exception:
            pass
    return results


def _r0083_toENNReal_iInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.toENNReal_iInf
    # toENNReal (⨅ i, f i) = ⨅ i, toENNReal (f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toENNReal", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), OVar("toENNReal"), OOp("f", (OVar("i"),)),))
            results.append((rhs, "Mathlib: ENat_toENNReal_iInf"))
        except Exception:
            pass
    return results


def _r0084_floor_add_fract(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: floor_add_fract
    # (⌊a⌋ : R) + fract a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: floor_add_fract"))
        except Exception:
            pass
    return results


def _r0085_fract_add_floor(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fract_add_floor
    # fract a + ⌊a⌋ = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: fract_add_floor"))
        except Exception:
            pass
    return results


def _r0086_self_sub_fract(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: self_sub_fract
    # a - fract a = ⌊a⌋
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: self_sub_fract"))
        except Exception:
            pass
    return results


def _r0087_fract_sub_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fract_sub_self
    # fract a - a = -⌊a⌋
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OVar("minus_a")
            results.append((rhs, "Mathlib: fract_sub_self"))
        except Exception:
            pass
    return results


def _r0088_fract_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fract_add
    # ∃ z : ℤ, fract (a + b) - fract a - fract b = z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OVar("z")
            results.append((rhs, "Mathlib: fract_add"))
        except Exception:
            pass
    return results


def _r0089_fract_add_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fract_add_natCast
    # fract (a + m) = fract a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fract", 1)
    if args is not None:
        try:
            rhs = OOp("fract", (OVar("a"),))
            results.append((rhs, "Mathlib: fract_add_natCast"))
        except Exception:
            pass
    return results


def _r0090_fract_add_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fract_add_one
    # fract (a + 1) = fract a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fract", 1)
    if args is not None:
        try:
            rhs = OOp("fract", (OVar("a"),))
            results.append((rhs, "Mathlib: fract_add_one"))
        except Exception:
            pass
    return results


def _r0091_fract_add_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fract_add_ofNat
    # fract (a + ofNat(n)) = fract a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fract", 1)
    if args is not None:
        try:
            rhs = OOp("fract", (OVar("a"),))
            results.append((rhs, "Mathlib: fract_add_ofNat"))
        except Exception:
            pass
    return results


def _r0092_fract_natCast_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fract_natCast_add
    # fract (↑n + a) = fract a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fract", 1)
    if args is not None:
        try:
            rhs = OOp("fract", (OVar("a"),))
            results.append((rhs, "Mathlib: fract_natCast_add"))
        except Exception:
            pass
    return results


def _r0093_fract_one_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fract_one_add
    # fract (1 + a) = fract a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fract", 1)
    if args is not None:
        try:
            rhs = OOp("fract", (OVar("a"),))
            results.append((rhs, "Mathlib: fract_one_add"))
        except Exception:
            pass
    return results


def _r0094_fract_ofNat_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fract_ofNat_add
    # fract (ofNat(n) + a) = fract a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fract", 1)
    if args is not None:
        try:
            rhs = OOp("fract", (OVar("a"),))
            results.append((rhs, "Mathlib: fract_ofNat_add"))
        except Exception:
            pass
    return results


def _r0095_fract_sub_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fract_sub_natCast
    # fract (a - n) = fract a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fract", 1)
    if args is not None:
        try:
            rhs = OOp("fract", (OVar("a"),))
            results.append((rhs, "Mathlib: fract_sub_natCast"))
        except Exception:
            pass
    return results


def _r0096_fract_sub_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fract_sub_one
    # fract (a - 1) = fract a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fract", 1)
    if args is not None:
        try:
            rhs = OOp("fract", (OVar("a"),))
            results.append((rhs, "Mathlib: fract_sub_one"))
        except Exception:
            pass
    return results


def _r0097_fract_sub_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fract_sub_ofNat
    # fract (a - ofNat(n)) = fract a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fract", 1)
    if args is not None:
        try:
            rhs = OOp("fract", (OVar("a"),))
            results.append((rhs, "Mathlib: fract_sub_ofNat"))
        except Exception:
            pass
    return results


def _r0098_fract_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fract_one
    # fract (1 : R) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fract", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: fract_one"))
        except Exception:
            pass
    return results


def _r0099_abs_fract(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: abs_fract
    # |fract a| = fract a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pipe_fract", 1)
    if args is not None:
        try:
            rhs = OOp("fract", (OVar("a"),))
            results.append((rhs, "Mathlib: abs_fract"))
        except Exception:
            pass
    return results


def _r0100_fract_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fract_intCast
    # fract (z : R) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fract", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: fract_intCast"))
        except Exception:
            pass
    return results


def _r0101_fract_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fract_ofNat
    # fract (ofNat(n) : R) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fract", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: fract_ofNat"))
        except Exception:
            pass
    return results


def _r0102_fract_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fract_eq_iff
    # fract a = b ↔ 0 ≤ b ∧ b < 1 ∧ ∃ z : ℤ, a - b = z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fract", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("<=", (OOp("iff", (OVar("b"), OLit(0))), OOp("<", (OOp("and", (OVar("b"), OVar("b"))), OOp("and", (OLit(1), OOp("-", (OOp("exists", (OVar("z"), OVar("colon"), OVar("_unknown"), args[0],)), OVar("b"))))))))), OVar("z")))
            results.append((rhs, "Mathlib: fract_eq_iff"))
        except Exception:
            pass
    return results


def _r0103_fract_fract(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fract_fract
    # fract (fract a) = fract a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fract", 1)
    if args is not None:
        try:
            rhs = OOp("fract", (OVar("a"),))
            results.append((rhs, "Mathlib: fract_fract"))
        except Exception:
            pass
    return results


def _r0104_fract_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fract_eq_zero_iff
    # fract a = 0 ↔ a ∈ range Int.cast
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fract", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OLit(0), OOp("in", (args[0], OOp("range", (OVar("Int_cast"),))))))
            results.append((rhs, "Mathlib: fract_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0105_ceil_eq_on_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ceil_eq_on_Ioc
    # ∀ a ∈ Set.Ioc (z - 1 : R) z, ⌈a⌉ = z
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("z")
            results.append((rhs, "Mathlib: ceil_eq_on_Ioc"))
    except Exception:
        pass
    return results


def _r0106_ceil_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ceil_natCast
    # ⌈(n : R)⌉ = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_colon_R")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: ceil_natCast"))
    except Exception:
        pass
    return results


def _r0107_ceil_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ceil_ofNat
    # ⌈(ofNat(n) : R)⌉ = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofNat_n_colon_R")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("ofNat_n")
            results.append((rhs, "Mathlib: ceil_ofNat"))
    except Exception:
        pass
    return results


def _r0108_ceil_add_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ceil_add_intCast
    # ⌈a + z⌉ = ⌈a⌉ + z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], args[1]))
            results.append((rhs, "Mathlib: ceil_add_intCast"))
        except Exception:
            pass
    return results


def _r0109_ceil_intCast_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ceil_intCast_add
    # ⌈z + a⌉ = z + ⌈a⌉
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], args[1]))
            results.append((rhs, "Mathlib: ceil_intCast_add"))
        except Exception:
            pass
    return results


def _r0110_ceil_add_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ceil_add_natCast
    # ⌈a + n⌉ = ⌈a⌉ + n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], args[1]))
            results.append((rhs, "Mathlib: ceil_add_natCast"))
        except Exception:
            pass
    return results


def _r0111_ceil_natCast_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ceil_natCast_add
    # ⌈n + a⌉ = n + ⌈a⌉
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], args[1]))
            results.append((rhs, "Mathlib: ceil_natCast_add"))
        except Exception:
            pass
    return results


def _r0112_ceil_add_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ceil_add_one
    # ⌈a + 1⌉ = ⌈a⌉ + 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], OLit(1)))
            results.append((rhs, "Mathlib: ceil_add_one"))
        except Exception:
            pass
    return results


def _r0113_ceil_one_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ceil_one_add
    # ⌈1 + a⌉ = 1 + ⌈a⌉
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OLit(1), args[1]))
            results.append((rhs, "Mathlib: ceil_one_add"))
        except Exception:
            pass
    return results


def _r0114_ceil_add_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ceil_add_ofNat
    # ⌈a + ofNat(n)⌉ = ⌈a⌉ + ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], args[1]))
            results.append((rhs, "Mathlib: ceil_add_ofNat"))
        except Exception:
            pass
    return results


def _r0115_ceil_sub_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ceil_sub_natCast
    # ⌈a - n⌉ = ⌈a⌉ - n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("-", (args[0], args[1]))
            results.append((rhs, "Mathlib: ceil_sub_natCast"))
        except Exception:
            pass
    return results


def _r0116_ceil_sub_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ceil_sub_ofNat
    # ⌈a - ofNat(n)⌉ = ⌈a⌉ - ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("-", (args[0], args[1]))
            results.append((rhs, "Mathlib: ceil_sub_ofNat"))
        except Exception:
            pass
    return results


def _r0117_ceil_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ceil_one
    # ⌈(1 : R)⌉ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_R")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ceil_one"))
    except Exception:
        pass
    return results


def _r0118_ceil_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ceil_eq_iff
    # ⌈a⌉₊ = n ↔ ↑(n - 1) < a ∧ a ≤ n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("<=", (OOp("<", (OOp("iff", (OVar("n"), OVar("n_minus_1"))), OOp("and", (OVar("a"), OVar("a"))))), OVar("n")))
            results.append((rhs, "Mathlib: ceil_eq_iff"))
    except Exception:
        pass
    return results


def _r0119_ceil_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ceil_zero
    # ⌈(0 : R)⌉₊ = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_R")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ceil_zero"))
    except Exception:
        pass
    return results


def _r0120_ceil_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ceil_one
    # ⌈(1 : R)⌉₊ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_R")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ceil_one"))
    except Exception:
        pass
    return results


def _r0121_ceil_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ceil_ofNat
    # ⌈(ofNat(n) : R)⌉₊ = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofNat_n_colon_R")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("ofNat_n")
            results.append((rhs, "Mathlib: ceil_ofNat"))
    except Exception:
        pass
    return results


def _r0122_floor_sub_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: floor_sub_ofNat
    # ⌊a - ofNat(n)⌋₊ = ⌊a⌋₊ - ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("-", (args[0], args[1]))
            results.append((rhs, "Mathlib: floor_sub_ofNat"))
        except Exception:
            pass
    return results


def _r0123_ceil_sub_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ceil_sub_ofNat
    # ⌈a - ofNat(n)⌉₊ = ⌈a⌉₊ - ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("-", (args[0], args[1]))
            results.append((rhs, "Mathlib: ceil_sub_ofNat"))
        except Exception:
            pass
    return results


def _r0124_mabs_eq_inv_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mabs_eq_inv_self
    # |a|ₘ = a⁻¹ ↔ a ≤ 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pipe_apipe")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("<=", (OOp("iff", (OVar("ainv"), OVar("a"))), OLit(1)))
            results.append((rhs, "Mathlib: mabs_eq_inv_self"))
    except Exception:
        pass
    return results


def _r0125_genLTOne_unique(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: LinearOrderedCommGroup.genLTOne_unique
    # g = genLTOne G
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("g")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("genLTOne", (OVar("G"),))
            results.append((rhs, "Mathlib: LinearOrderedCommGroup_genLTOne_unique"))
    except Exception:
        pass
    return results


def _r0126_coe_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RelHom.coe_mul
    # ⇑(f * g) = f ∘ g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_star_g")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comp", (OVar("f"), OVar("g")))
            results.append((rhs, "Mathlib: RelHom_coe_mul"))
    except Exception:
        pass
    return results


def _r0127_mul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RelHom.mul_apply
    # (e₁ * e₂) x = e₁ (e₂ x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_1_star_e_2", 1)
    if args is not None:
        try:
            rhs = OOp("e_1", (OOp("e_2", (args[0],)),))
            results.append((rhs, "Mathlib: RelHom_mul_apply"))
        except Exception:
            pass
    return results


def _r0128_coe_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RelEmbedding.coe_mul
    # ⇑(f * g) = f ∘ g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_star_g")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comp", (OVar("f"), OVar("g")))
            results.append((rhs, "Mathlib: RelEmbedding_coe_mul"))
    except Exception:
        pass
    return results


def _r0129_one_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RelEmbedding.one_apply
    # (1 : r ↪r r) a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_r_r_r", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: RelEmbedding_one_apply"))
        except Exception:
            pass
    return results


def _r0130_mul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RelEmbedding.mul_apply
    # (e₁ * e₂) x = e₁ (e₂ x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_1_star_e_2", 1)
    if args is not None:
        try:
            rhs = OOp("e_1", (OOp("e_2", (args[0],)),))
            results.append((rhs, "Mathlib: RelEmbedding_mul_apply"))
        except Exception:
            pass
    return results


def _r0131_one_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RelIso.one_apply
    # (1 : r ≃r r) x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_r_r_r", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: RelIso_one_apply"))
        except Exception:
            pass
    return results


def _r0132_mul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RelIso.mul_apply
    # (e₁ * e₂) x = e₁ (e₂ x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_1_star_e_2", 1)
    if args is not None:
        try:
            rhs = OOp("e_1", (OOp("e_2", (args[0],)),))
            results.append((rhs, "Mathlib: RelIso_mul_apply"))
        except Exception:
            pass
    return results


def _r0133_apply_inv_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RelIso.apply_inv_self
    # e (e⁻¹ x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: RelIso_apply_inv_self"))
        except Exception:
            pass
    return results


def _r0134_coe_ofLexMulEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_ofLexMulEquiv
    # ⇑(ofLexMulEquiv α) = ofLex
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofLexMulEquiv_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("ofLex")
            results.append((rhs, "Mathlib: coe_ofLexMulEquiv"))
    except Exception:
        pass
    return results


def _r0135_symm_toLexMulEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: symm_toLexMulEquiv
    # (toLexMulEquiv α).symm = ofLexMulEquiv α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("toLexMulEquiv_a_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("ofLexMulEquiv", (OVar("a"),))
            results.append((rhs, "Mathlib: symm_toLexMulEquiv"))
    except Exception:
        pass
    return results


def _r0136_symm_ofLexMulEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: symm_ofLexMulEquiv
    # (ofLexMulEquiv α).symm = toLexMulEquiv α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofLexMulEquiv_a_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("toLexMulEquiv", (OVar("a"),))
            results.append((rhs, "Mathlib: symm_ofLexMulEquiv"))
    except Exception:
        pass
    return results


def _r0137_toEquiv_toLexMulEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toEquiv_toLexMulEquiv
    # (toLexMulEquiv α : α ≃ Lex α) = toLex
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toLexMulEquiv", 6)
    if args is not None:
        try:
            rhs = OVar("toLex")
            results.append((rhs, "Mathlib: toEquiv_toLexMulEquiv"))
        except Exception:
            pass
    return results


def _r0138_toEquiv_ofLexMulEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toEquiv_ofLexMulEquiv
    # (ofLexMulEquiv α : Lex α ≃ α) = ofLex
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofLexMulEquiv", 6)
    if args is not None:
        try:
            rhs = OVar("ofLex")
            results.append((rhs, "Mathlib: toEquiv_ofLexMulEquiv"))
        except Exception:
            pass
    return results


def _r0139_dedup_nsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: dedup_nsmul
    # (n • s).dedup = s.dedup
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_s_dedup")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_dedup")
            results.append((rhs, "Mathlib: dedup_nsmul"))
    except Exception:
        pass
    return results


def _r0140_count_nsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: count_nsmul
    # count a (n • s) = n * count a s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "count", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("n"), OOp("count", (args[0], OVar("s"),))))
            results.append((rhs, "Mathlib: count_nsmul"))
        except Exception:
            pass
    return results


def _r0141_csInf_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: csInf_one
    # sInf (1 : Set M) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sInf", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: csInf_one"))
        except Exception:
            pass
    return results


def _r0142_inv_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inv_Iic
    # (Iic a)⁻¹ = Ici a⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Iic_a_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Ici", (OVar("ainv"),))
            results.append((rhs, "Mathlib: inv_Iic"))
    except Exception:
        pass
    return results


def _r0143_inv_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inv_Ioi
    # (Ioi a)⁻¹ = Iio a⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Ioi_a_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Iio", (OVar("ainv"),))
            results.append((rhs, "Mathlib: inv_Ioi"))
    except Exception:
        pass
    return results


def _r0144_inv_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inv_Iio
    # (Iio a)⁻¹ = Ioi a⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Iio_a_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Ioi", (OVar("ainv"),))
            results.append((rhs, "Mathlib: inv_Iio"))
    except Exception:
        pass
    return results


def _r0145_inv_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inv_Icc
    # (Icc a b)⁻¹ = Icc b⁻¹ a⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Icc_a_b_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Icc", (OVar("binv"), OVar("ainv"),))
            results.append((rhs, "Mathlib: inv_Icc"))
    except Exception:
        pass
    return results


def _r0146_inv_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inv_Ico
    # (Ico a b)⁻¹ = Ioc b⁻¹ a⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Ico_a_b_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Ioc", (OVar("binv"), OVar("ainv"),))
            results.append((rhs, "Mathlib: inv_Ico"))
    except Exception:
        pass
    return results


def _r0147_inv_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inv_Ioc
    # (Ioc a b)⁻¹ = Ico b⁻¹ a⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Ioc_a_b_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Ico", (OVar("binv"), OVar("ainv"),))
            results.append((rhs, "Mathlib: inv_Ioc"))
    except Exception:
        pass
    return results


def _r0148_inv_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inv_Ioo
    # (Ioo a b)⁻¹ = Ioo b⁻¹ a⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Ioo_a_b_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Ioo", (OVar("binv"), OVar("ainv"),))
            results.append((rhs, "Mathlib: inv_Ioo"))
    except Exception:
        pass
    return results


def _r0149_preimage_const_mul_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_mul_Ioi
    # (fun x => a * x) ⁻¹' Ioi b = Ioi (b / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_a_star_x", 3)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OOp("//", (args[2], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_const_mul_Ioi"))
        except Exception:
            pass
    return results


def _r0150_preimage_const_mul_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_mul_Iic
    # (fun x => a * x) ⁻¹' Iic b = Iic (b / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_a_star_x", 3)
    if args is not None:
        try:
            rhs = OOp("Iic", (OOp("//", (args[2], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_const_mul_Iic"))
        except Exception:
            pass
    return results


def _r0151_preimage_const_mul_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_mul_Iio
    # (fun x => a * x) ⁻¹' Iio b = Iio (b / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_a_star_x", 3)
    if args is not None:
        try:
            rhs = OOp("Iio", (OOp("//", (args[2], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_const_mul_Iio"))
        except Exception:
            pass
    return results


def _r0152_preimage_const_mul_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_mul_Icc
    # (fun x => a * x) ⁻¹' Icc b c = Icc (b / a) (c / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_a_star_x", 4)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("//", (args[2], OVar("a"))), OOp("//", (args[3], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_const_mul_Icc"))
        except Exception:
            pass
    return results


def _r0153_preimage_const_mul_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_mul_Ico
    # (fun x => a * x) ⁻¹' Ico b c = Ico (b / a) (c / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_a_star_x", 4)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("//", (args[2], OVar("a"))), OOp("//", (args[3], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_const_mul_Ico"))
        except Exception:
            pass
    return results


def _r0154_preimage_const_mul_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_mul_Ioc
    # (fun x => a * x) ⁻¹' Ioc b c = Ioc (b / a) (c / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_a_star_x", 4)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("//", (args[2], OVar("a"))), OOp("//", (args[3], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_const_mul_Ioc"))
        except Exception:
            pass
    return results


def _r0155_preimage_const_mul_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_mul_Ioo
    # (fun x => a * x) ⁻¹' Ioo b c = Ioo (b / a) (c / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_a_star_x", 4)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OOp("//", (args[2], OVar("a"))), OOp("//", (args[3], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_const_mul_Ioo"))
        except Exception:
            pass
    return results


def _r0156_preimage_mul_const_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_mul_const_Ioi
    # (fun x => x * a) ⁻¹' Ioi b = Ioi (b / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_star_a", 3)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OOp("//", (args[2], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_mul_const_Ioi"))
        except Exception:
            pass
    return results


def _r0157_preimage_mul_const_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_mul_const_Iic
    # (fun x => x * a) ⁻¹' Iic b = Iic (b / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_star_a", 3)
    if args is not None:
        try:
            rhs = OOp("Iic", (OOp("//", (args[2], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_mul_const_Iic"))
        except Exception:
            pass
    return results


def _r0158_preimage_mul_const_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_mul_const_Iio
    # (fun x => x * a) ⁻¹' Iio b = Iio (b / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_star_a", 3)
    if args is not None:
        try:
            rhs = OOp("Iio", (OOp("//", (args[2], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_mul_const_Iio"))
        except Exception:
            pass
    return results


def _r0159_preimage_mul_const_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_mul_const_Icc
    # (fun x => x * a) ⁻¹' Icc b c = Icc (b / a) (c / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_star_a", 4)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("//", (args[2], OVar("a"))), OOp("//", (args[3], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_mul_const_Icc"))
        except Exception:
            pass
    return results


def _r0160_preimage_mul_const_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_mul_const_Ico
    # (fun x => x * a) ⁻¹' Ico b c = Ico (b / a) (c / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_star_a", 4)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("//", (args[2], OVar("a"))), OOp("//", (args[3], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_mul_const_Ico"))
        except Exception:
            pass
    return results


def _r0161_preimage_mul_const_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_mul_const_Ioc
    # (fun x => x * a) ⁻¹' Ioc b c = Ioc (b / a) (c / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_star_a", 4)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("//", (args[2], OVar("a"))), OOp("//", (args[3], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_mul_const_Ioc"))
        except Exception:
            pass
    return results


def _r0162_preimage_mul_const_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_mul_const_Ioo
    # (fun x => x * a) ⁻¹' Ioo b c = Ioo (b / a) (c / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_star_a", 4)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OOp("//", (args[2], OVar("a"))), OOp("//", (args[3], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_mul_const_Ioo"))
        except Exception:
            pass
    return results


def _r0163_preimage_div_const_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_div_const_Ioi
    # (fun x => x / a) ⁻¹' Ioi b = Ioi (b * a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_slash_a", 3)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OOp("*", (args[2], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_div_const_Ioi"))
        except Exception:
            pass
    return results


def _r0164_preimage_div_const_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_div_const_Iic
    # (fun x => x / a) ⁻¹' Iic b = Iic (b * a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_slash_a", 3)
    if args is not None:
        try:
            rhs = OOp("Iic", (OOp("*", (args[2], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_div_const_Iic"))
        except Exception:
            pass
    return results


def _r0165_preimage_div_const_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_div_const_Iio
    # (fun x => x / a) ⁻¹' Iio b = Iio (b * a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_slash_a", 3)
    if args is not None:
        try:
            rhs = OOp("Iio", (OOp("*", (args[2], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_div_const_Iio"))
        except Exception:
            pass
    return results


def _r0166_preimage_div_const_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_div_const_Icc
    # (fun x => x / a) ⁻¹' Icc b c = Icc (b * a) (c * a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_slash_a", 4)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("*", (args[2], OVar("a"))), OOp("*", (args[3], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_div_const_Icc"))
        except Exception:
            pass
    return results


def _r0167_preimage_div_const_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_div_const_Ico
    # (fun x => x / a) ⁻¹' Ico b c = Ico (b * a) (c * a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_slash_a", 4)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("*", (args[2], OVar("a"))), OOp("*", (args[3], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_div_const_Ico"))
        except Exception:
            pass
    return results


def _r0168_preimage_div_const_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_div_const_Ioc
    # (fun x => x / a) ⁻¹' Ioc b c = Ioc (b * a) (c * a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_slash_a", 4)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("*", (args[2], OVar("a"))), OOp("*", (args[3], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_div_const_Ioc"))
        except Exception:
            pass
    return results


def _r0169_preimage_div_const_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_div_const_Ioo
    # (fun x => x / a) ⁻¹' Ioo b c = Ioo (b * a) (c * a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_slash_a", 4)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OOp("*", (args[2], OVar("a"))), OOp("*", (args[3], OVar("a"))),))
            results.append((rhs, "Mathlib: preimage_div_const_Ioo"))
        except Exception:
            pass
    return results


def _r0170_preimage_const_div_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_div_Iic
    # (fun x => a / x) ⁻¹' Iic b = Ici (a / b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_a_slash_x", 3)
    if args is not None:
        try:
            rhs = OOp("Ici", (OOp("//", (OVar("a"), args[2])),))
            results.append((rhs, "Mathlib: preimage_const_div_Iic"))
        except Exception:
            pass
    return results


def _r0171_preimage_const_div_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_div_Ioi
    # (fun x => a / x) ⁻¹' Ioi b = Iio (a / b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_a_slash_x", 3)
    if args is not None:
        try:
            rhs = OOp("Iio", (OOp("//", (OVar("a"), args[2])),))
            results.append((rhs, "Mathlib: preimage_const_div_Ioi"))
        except Exception:
            pass
    return results


def _r0172_preimage_const_div_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_div_Iio
    # (fun x => a / x) ⁻¹' Iio b = Ioi (a / b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_a_slash_x", 3)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OOp("//", (OVar("a"), args[2])),))
            results.append((rhs, "Mathlib: preimage_const_div_Iio"))
        except Exception:
            pass
    return results


def _r0173_preimage_const_div_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_div_Icc
    # (fun x => a / x) ⁻¹' Icc b c = Icc (a / c) (a / b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_a_slash_x", 4)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("//", (OVar("a"), args[3])), OOp("//", (OVar("a"), args[2])),))
            results.append((rhs, "Mathlib: preimage_const_div_Icc"))
        except Exception:
            pass
    return results


def _r0174_preimage_const_div_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_div_Ico
    # (fun x => a / x) ⁻¹' Ico b c = Ioc (a / c) (a / b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_a_slash_x", 4)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("//", (OVar("a"), args[3])), OOp("//", (OVar("a"), args[2])),))
            results.append((rhs, "Mathlib: preimage_const_div_Ico"))
        except Exception:
            pass
    return results


def _r0175_preimage_const_div_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_div_Ioc
    # (fun x => a / x) ⁻¹' Ioc b c = Ico (a / c) (a / b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_a_slash_x", 4)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("//", (OVar("a"), args[3])), OOp("//", (OVar("a"), args[2])),))
            results.append((rhs, "Mathlib: preimage_const_div_Ioc"))
        except Exception:
            pass
    return results


def _r0176_preimage_const_div_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_div_Ioo
    # (fun x => a / x) ⁻¹' Ioo b c = Ioo (a / c) (a / b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_a_slash_x", 4)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OOp("//", (OVar("a"), args[3])), OOp("//", (OVar("a"), args[2])),))
            results.append((rhs, "Mathlib: preimage_const_div_Ioo"))
        except Exception:
            pass
    return results


def _r0177_image_div_const_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: image_div_const_Iic
    # (fun x => x / a) '' Iic b = Iic (b / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_slash_a", 3)
    if args is not None:
        try:
            rhs = OOp("Iic", (OOp("//", (args[2], OVar("a"))),))
            results.append((rhs, "Mathlib: image_div_const_Iic"))
        except Exception:
            pass
    return results


def _r0178_image_div_const_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: image_div_const_Ioi
    # (fun x => x / a) '' Ioi b = Ioi (b / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_slash_a", 3)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OOp("//", (args[2], OVar("a"))),))
            results.append((rhs, "Mathlib: image_div_const_Ioi"))
        except Exception:
            pass
    return results


def _r0179_image_div_const_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: image_div_const_Iio
    # (fun x => x / a) '' Iio b = Iio (b / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_slash_a", 3)
    if args is not None:
        try:
            rhs = OOp("Iio", (OOp("//", (args[2], OVar("a"))),))
            results.append((rhs, "Mathlib: image_div_const_Iio"))
        except Exception:
            pass
    return results


def _r0180_image_div_const_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: image_div_const_Icc
    # (fun x => x / a) '' Icc b c = Icc (b / a) (c / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_slash_a", 4)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("//", (args[2], OVar("a"))), OOp("//", (args[3], OVar("a"))),))
            results.append((rhs, "Mathlib: image_div_const_Icc"))
        except Exception:
            pass
    return results


def _r0181_image_div_const_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: image_div_const_Ico
    # (fun x => x / a) '' Ico b c = Ico (b / a) (c / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_slash_a", 4)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("//", (args[2], OVar("a"))), OOp("//", (args[3], OVar("a"))),))
            results.append((rhs, "Mathlib: image_div_const_Ico"))
        except Exception:
            pass
    return results


def _r0182_image_div_const_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: image_div_const_Ioc
    # (fun x => x / a) '' Ioc b c = Ioc (b / a) (c / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_slash_a", 4)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("//", (args[2], OVar("a"))), OOp("//", (args[3], OVar("a"))),))
            results.append((rhs, "Mathlib: image_div_const_Ioc"))
        except Exception:
            pass
    return results


def _r0183_image_div_const_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: image_div_const_Ioo
    # (fun x => x / a) '' Ioo b c = Ioo (b / a) (c / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_slash_a", 4)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OOp("//", (args[2], OVar("a"))), OOp("//", (args[3], OVar("a"))),))
            results.append((rhs, "Mathlib: image_div_const_Ioo"))
        except Exception:
            pass
    return results


def _r0184_preimage_add_const_uIcc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_add_const_uIcc
    # (fun x => x + a) ⁻¹' [[b, c]] = [[b - a, c - a]]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_plus_a", 2)
    if args is not None:
        try:
            rhs = OVar("b_minus_a_c_minus_a")
            results.append((rhs, "Mathlib: preimage_add_const_uIcc"))
        except Exception:
            pass
    return results


def _r0185_preimage_sub_const_uIcc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_sub_const_uIcc
    # (fun x => x - a) ⁻¹' [[b, c]] = [[b + a, c + a]]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_minus_a", 2)
    if args is not None:
        try:
            rhs = OVar("b_plus_a_c_plus_a")
            results.append((rhs, "Mathlib: preimage_sub_const_uIcc"))
        except Exception:
            pass
    return results


def _r0186_preimage_const_sub_uIcc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_sub_uIcc
    # (fun x => a - x) ⁻¹' [[b, c]] = [[a - b, a - c]]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_a_minus_x", 2)
    if args is not None:
        try:
            rhs = OVar("a_minus_b_a_minus_c")
            results.append((rhs, "Mathlib: preimage_const_sub_uIcc"))
        except Exception:
            pass
    return results


def _r0187_image_neg_uIcc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: image_neg_uIcc
    # Neg.neg '' [[a, b]] = [[-a, -b]]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "neg", 2)
    if args is not None:
        try:
            rhs = OVar("minus_a_minus_b")
            results.append((rhs, "Mathlib: image_neg_uIcc"))
        except Exception:
            pass
    return results


def _r0188_preimage_mul_const_Ici_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_mul_const_Ici₀
    # (· * c) ⁻¹' Ici a = Ici (a / c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "star_c", 3)
    if args is not None:
        try:
            rhs = OOp("Ici", (OOp("//", (args[2], OVar("c"))),))
            results.append((rhs, "Mathlib: preimage_mul_const_Ici_0"))
        except Exception:
            pass
    return results


def _r0189_preimage_mul_const_Ioi_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_mul_const_Ioi₀
    # (· * c) ⁻¹' Ioi a = Ioi (a / c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "star_c", 3)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OOp("//", (args[2], OVar("c"))),))
            results.append((rhs, "Mathlib: preimage_mul_const_Ioi_0"))
        except Exception:
            pass
    return results


def _r0190_preimage_mul_const_Iio_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_mul_const_Iio₀
    # (· * c) ⁻¹' Iio a = Iio (a / c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "star_c", 3)
    if args is not None:
        try:
            rhs = OOp("Iio", (OOp("//", (args[2], OVar("c"))),))
            results.append((rhs, "Mathlib: preimage_mul_const_Iio_0"))
        except Exception:
            pass
    return results


def _r0191_preimage_mul_const_Icc_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_mul_const_Icc₀
    # (· * c) ⁻¹' Icc a b = Icc (a / c) (b / c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "star_c", 4)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("//", (args[2], OVar("c"))), OOp("//", (args[3], OVar("c"))),))
            results.append((rhs, "Mathlib: preimage_mul_const_Icc_0"))
        except Exception:
            pass
    return results


def _r0192_preimage_mul_const_Ioo_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_mul_const_Ioo₀
    # (fun x => x * c) ⁻¹' Ioo a b = Ioo (a / c) (b / c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_star_c", 4)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OOp("//", (args[2], OVar("c"))), OOp("//", (args[3], OVar("c"))),))
            results.append((rhs, "Mathlib: preimage_mul_const_Ioo_0"))
        except Exception:
            pass
    return results


def _r0193_preimage_mul_const_Ioc_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_mul_const_Ioc₀
    # (fun x => x * c) ⁻¹' Ioc a b = Ioc (a / c) (b / c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_star_c", 4)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("//", (args[2], OVar("c"))), OOp("//", (args[3], OVar("c"))),))
            results.append((rhs, "Mathlib: preimage_mul_const_Ioc_0"))
        except Exception:
            pass
    return results


def _r0194_preimage_mul_const_Ico_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_mul_const_Ico₀
    # (fun x => x * c) ⁻¹' Ico a b = Ico (a / c) (b / c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_star_c", 4)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("//", (args[2], OVar("c"))), OOp("//", (args[3], OVar("c"))),))
            results.append((rhs, "Mathlib: preimage_mul_const_Ico_0"))
        except Exception:
            pass
    return results


def _r0195_preimage_const_mul_Ici_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_mul_Ici₀
    # (c * ·) ⁻¹' Ici a = Ici (a / c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_star", 3)
    if args is not None:
        try:
            rhs = OOp("Ici", (OOp("//", (args[2], OVar("c"))),))
            results.append((rhs, "Mathlib: preimage_const_mul_Ici_0"))
        except Exception:
            pass
    return results


def _r0196_preimage_const_mul_Icc_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_mul_Icc₀
    # (c * ·) ⁻¹' Icc a b = Icc (a / c) (b / c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_star", 4)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("//", (args[2], OVar("c"))), OOp("//", (args[3], OVar("c"))),))
            results.append((rhs, "Mathlib: preimage_const_mul_Icc_0"))
        except Exception:
            pass
    return results


def _r0197_preimage_const_mul_Iio_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_mul_Iio₀
    # (c * ·) ⁻¹' Iio a = Iio (a / c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_star", 3)
    if args is not None:
        try:
            rhs = OOp("Iio", (OOp("//", (args[2], OVar("c"))),))
            results.append((rhs, "Mathlib: preimage_const_mul_Iio_0"))
        except Exception:
            pass
    return results


def _r0198_preimage_const_mul_Ioi_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_mul_Ioi₀
    # (c * ·) ⁻¹' Ioi a = Ioi (a / c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_star", 3)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OOp("//", (args[2], OVar("c"))),))
            results.append((rhs, "Mathlib: preimage_const_mul_Ioi_0"))
        except Exception:
            pass
    return results


def _r0199_preimage_const_mul_Ioo_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_mul_Ioo₀
    # (c * ·) ⁻¹' Ioo a b = Ioo (a / c) (b / c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_star", 4)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OOp("//", (args[2], OVar("c"))), OOp("//", (args[3], OVar("c"))),))
            results.append((rhs, "Mathlib: preimage_const_mul_Ioo_0"))
        except Exception:
            pass
    return results


def _r0200_preimage_const_mul_Ioc_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_mul_Ioc₀
    # (c * ·) ⁻¹' Ioc a b = Ioc (a / c) (b / c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_star", 4)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("//", (args[2], OVar("c"))), OOp("//", (args[3], OVar("c"))),))
            results.append((rhs, "Mathlib: preimage_const_mul_Ioc_0"))
        except Exception:
            pass
    return results


def _r0201_preimage_const_mul_Ico_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_mul_Ico₀
    # (c * ·) ⁻¹' Ico a b = Ico (a / c) (b / c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_star", 4)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("//", (args[2], OVar("c"))), OOp("//", (args[3], OVar("c"))),))
            results.append((rhs, "Mathlib: preimage_const_mul_Ico_0"))
        except Exception:
            pass
    return results


def _r0202_preimage_mul_const_Ioc_of_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_mul_const_Ioc_of_neg
    # (fun x => x * c) ⁻¹' Ioc a b = Ico (b / c) (a / c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_star_c", 4)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("//", (args[3], OVar("c"))), OOp("//", (args[2], OVar("c"))),))
            results.append((rhs, "Mathlib: preimage_mul_const_Ioc_of_neg"))
        except Exception:
            pass
    return results


def _r0203_preimage_const_mul_Iio_of_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_const_mul_Iio_of_neg
    # (c * ·) ⁻¹' Iio a = Ioi (a / c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_star", 3)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OOp("//", (args[2], OVar("c"))),))
            results.append((rhs, "Mathlib: preimage_const_mul_Iio_of_neg"))
        except Exception:
            pass
    return results


def _r0204_image_div_const_uIcc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: image_div_const_uIcc
    # (fun x => x / a) '' [[b, c]] = [[b / a, c / a]]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_slash_a", 2)
    if args is not None:
        try:
            rhs = OVar("b_slash_a_c_slash_a")
            results.append((rhs, "Mathlib: image_div_const_uIcc"))
        except Exception:
            pass
    return results


def _r0205_leOnePart_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: leOnePart_one
    # (1 : α)⁻ᵐ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_a_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: leOnePart_one"))
    except Exception:
        pass
    return results


def _r0206_oneLePart_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: oneLePart_eq_one
    # a⁺ᵐ = 1 ↔ a ≤ 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("apos")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("<=", (OOp("iff", (OLit(1), OVar("a"))), OLit(1)))
            results.append((rhs, "Mathlib: oneLePart_eq_one"))
    except Exception:
        pass
    return results


def _r0207_oneLePart_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: oneLePart_inv
    # a⁻¹⁺ᵐ = a⁻ᵐ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ainv_pos")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("ainv")
            results.append((rhs, "Mathlib: oneLePart_inv"))
    except Exception:
        pass
    return results


def _r0208_leOnePart_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: leOnePart_inv
    # a⁻¹⁻ᵐ = a⁺ᵐ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ainv_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("apos")
            results.append((rhs, "Mathlib: leOnePart_inv"))
    except Exception:
        pass
    return results


def _r0209_oneLePart_max(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: oneLePart_max
    # (max a b)⁺ᵐ = max a⁺ᵐ b⁺ᵐ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("max_a_b_pos")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("max", (OVar("apos"), OVar("bpos"),))
            results.append((rhs, "Mathlib: oneLePart_max"))
    except Exception:
        pass
    return results


def _r0210_leOnePart_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: leOnePart_eq_one
    # a⁻ᵐ = 1 ↔ 1 ≤ a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ainv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("<=", (OOp("iff", (OLit(1), OLit(1))), OVar("a")))
            results.append((rhs, "Mathlib: leOnePart_eq_one"))
    except Exception:
        pass
    return results


def _r0211_oneLePart_of_one_lt_oneLePart(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: oneLePart_of_one_lt_oneLePart
    # a⁺ᵐ = a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("apos")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a")
            results.append((rhs, "Mathlib: oneLePart_of_one_lt_oneLePart"))
    except Exception:
        pass
    return results


def _r0212_leOnePart_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Pi.leOnePart_apply
    # f⁻ᵐ i = (f i)⁻ᵐ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "finv", 1)
    if args is not None:
        try:
            rhs = OVar("f_i_inv")
            results.append((rhs, "Mathlib: Pi_leOnePart_apply"))
        except Exception:
            pass
    return results


def _r0213_oneLePart_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Pi.oneLePart_def
    # f⁺ᵐ = fun i ↦ (f i)⁺ᵐ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("fpos")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("fun", (OVar("i"), OVar("_unknown"), OVar("f_i_pos"),))
            results.append((rhs, "Mathlib: Pi_oneLePart_def"))
    except Exception:
        pass
    return results


def _r0214_leOnePart_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Pi.leOnePart_def
    # f⁻ᵐ = fun i ↦ (f i)⁻ᵐ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("finv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("fun", (OVar("i"), OVar("_unknown"), OVar("f_i_inv"),))
            results.append((rhs, "Mathlib: Pi_leOnePart_def"))
    except Exception:
        pass
    return results


def _r0215_ofDual_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofDual_one
    # (ofDual 1 : α) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofDual", 3)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ofDual_one"))
        except Exception:
            pass
    return results


def _r0216_toDual_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toDual_eq_one
    # toDual a = 1 ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toDual", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[0])), OLit(1)))
            results.append((rhs, "Mathlib: toDual_eq_one"))
        except Exception:
            pass
    return results


def _r0217_ofDual_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofDual_eq_one
    # ofDual a = 1 ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofDual", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[0])), OLit(1)))
            results.append((rhs, "Mathlib: ofDual_eq_one"))
        except Exception:
            pass
    return results


def _r0218_toDual_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toDual_mul
    # toDual (a * b) = toDual a * toDual b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toDual", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("toDual", (OVar("a"),)), OOp("toDual", (OVar("b"),))))
            results.append((rhs, "Mathlib: toDual_mul"))
        except Exception:
            pass
    return results


def _r0219_ofDual_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofDual_mul
    # ofDual (a * b) = ofDual a * ofDual b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofDual", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("ofDual", (OVar("a"),)), OOp("ofDual", (OVar("b"),))))
            results.append((rhs, "Mathlib: ofDual_mul"))
        except Exception:
            pass
    return results


def _r0220_toDual_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toDual_inv
    # toDual a⁻¹ = (toDual a)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toDual", 1)
    if args is not None:
        try:
            rhs = OVar("toDual_a_inv")
            results.append((rhs, "Mathlib: toDual_inv"))
        except Exception:
            pass
    return results


def _r0221_ofDual_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofDual_inv
    # ofDual a⁻¹ = (ofDual a)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofDual", 1)
    if args is not None:
        try:
            rhs = OVar("ofDual_a_inv")
            results.append((rhs, "Mathlib: ofDual_inv"))
        except Exception:
            pass
    return results


def _r0222_toDual_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toDual_div
    # toDual (a / b) = toDual a / toDual b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toDual", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("toDual", (OVar("a"),)), OOp("toDual", (OVar("b"),))))
            results.append((rhs, "Mathlib: toDual_div"))
        except Exception:
            pass
    return results


def _r0223_ofDual_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofDual_div
    # ofDual (a / b) = ofDual a / ofDual b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofDual", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("ofDual", (OVar("a"),)), OOp("ofDual", (OVar("b"),))))
            results.append((rhs, "Mathlib: ofDual_div"))
        except Exception:
            pass
    return results


def _r0224_toDual_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toDual_pow
    # toDual (a ^ b) = toDual a ^ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toDual", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("toDual", (OVar("a"),)), OVar("b")))
            results.append((rhs, "Mathlib: toDual_pow"))
        except Exception:
            pass
    return results


def _r0225_ofDual_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofDual_pow
    # ofDual (a ^ b) = ofDual a ^ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofDual", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("ofDual", (OVar("a"),)), OVar("b")))
            results.append((rhs, "Mathlib: ofDual_pow"))
        except Exception:
            pass
    return results


def _r0226_pow_toDual(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_toDual
    # a ^ toDual b = a ^ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], OVar("b")))
            results.append((rhs, "Mathlib: pow_toDual"))
        except Exception:
            pass
    return results


def _r0227_pow_ofDual(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_ofDual
    # a ^ ofDual b = a ^ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], OVar("b")))
            results.append((rhs, "Mathlib: pow_ofDual"))
        except Exception:
            pass
    return results


def _r0228_toLex_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toLex_eq_one
    # toLex a = 1 ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toLex", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[0])), OLit(1)))
            results.append((rhs, "Mathlib: toLex_eq_one"))
        except Exception:
            pass
    return results


def _r0229_ofLex_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofLex_one
    # (ofLex 1 : α) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofLex", 3)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ofLex_one"))
        except Exception:
            pass
    return results


def _r0230_ofLex_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofLex_eq_one
    # ofLex a = 1 ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofLex", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[0])), OLit(1)))
            results.append((rhs, "Mathlib: ofLex_eq_one"))
        except Exception:
            pass
    return results


def _r0231_toLex_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toLex_mul
    # toLex (a * b) = toLex a * toLex b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toLex", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("toLex", (OVar("a"),)), OOp("toLex", (OVar("b"),))))
            results.append((rhs, "Mathlib: toLex_mul"))
        except Exception:
            pass
    return results


def _r0232_ofLex_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofLex_mul
    # ofLex (a * b) = ofLex a * ofLex b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofLex", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("ofLex", (OVar("a"),)), OOp("ofLex", (OVar("b"),))))
            results.append((rhs, "Mathlib: ofLex_mul"))
        except Exception:
            pass
    return results


def _r0233_toLex_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toLex_inv
    # toLex a⁻¹ = (toLex a)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toLex", 1)
    if args is not None:
        try:
            rhs = OVar("toLex_a_inv")
            results.append((rhs, "Mathlib: toLex_inv"))
        except Exception:
            pass
    return results


def _r0234_ofLex_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofLex_inv
    # ofLex a⁻¹ = (ofLex a)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofLex", 1)
    if args is not None:
        try:
            rhs = OVar("ofLex_a_inv")
            results.append((rhs, "Mathlib: ofLex_inv"))
        except Exception:
            pass
    return results


def _r0235_toLex_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toLex_div
    # toLex (a / b) = toLex a / toLex b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toLex", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("toLex", (OVar("a"),)), OOp("toLex", (OVar("b"),))))
            results.append((rhs, "Mathlib: toLex_div"))
        except Exception:
            pass
    return results


def _r0236_ofLex_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofLex_div
    # ofLex (a / b) = ofLex a / ofLex b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofLex", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("ofLex", (OVar("a"),)), OOp("ofLex", (OVar("b"),))))
            results.append((rhs, "Mathlib: ofLex_div"))
        except Exception:
            pass
    return results


def _r0237_toLex_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toLex_pow
    # toLex (a ^ b) = toLex a ^ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toLex", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("toLex", (OVar("a"),)), OVar("b")))
            results.append((rhs, "Mathlib: toLex_pow"))
        except Exception:
            pass
    return results


def _r0238_ofLex_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofLex_pow
    # ofLex (a ^ b) = ofLex a ^ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofLex", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("ofLex", (OVar("a"),)), OVar("b")))
            results.append((rhs, "Mathlib: ofLex_pow"))
        except Exception:
            pass
    return results


def _r0239_pow_toLex(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_toLex
    # a ^ toLex b = a ^ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], OVar("b")))
            results.append((rhs, "Mathlib: pow_toLex"))
        except Exception:
            pass
    return results


def _r0240_pow_ofLex(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_ofLex
    # a ^ ofLex b = a ^ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], OVar("b")))
            results.append((rhs, "Mathlib: pow_ofLex"))
        except Exception:
            pass
    return results


def _r0241_toColex_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toColex_eq_one
    # toColex a = 1 ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toColex", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[0])), OLit(1)))
            results.append((rhs, "Mathlib: toColex_eq_one"))
        except Exception:
            pass
    return results


def _r0242_ofColex_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofColex_one
    # (ofColex 1 : α) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofColex", 3)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ofColex_one"))
        except Exception:
            pass
    return results


def _r0243_ofColex_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofColex_eq_one
    # ofColex a = 1 ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofColex", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[0])), OLit(1)))
            results.append((rhs, "Mathlib: ofColex_eq_one"))
        except Exception:
            pass
    return results


def _r0244_toColex_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toColex_mul
    # toColex (a * b) = toColex a * toColex b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toColex", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("toColex", (OVar("a"),)), OOp("toColex", (OVar("b"),))))
            results.append((rhs, "Mathlib: toColex_mul"))
        except Exception:
            pass
    return results


def _r0245_ofColex_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofColex_mul
    # ofColex (a * b) = ofColex a * ofColex b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofColex", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("ofColex", (OVar("a"),)), OOp("ofColex", (OVar("b"),))))
            results.append((rhs, "Mathlib: ofColex_mul"))
        except Exception:
            pass
    return results


def _r0246_toColex_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toColex_inv
    # toColex a⁻¹ = (toColex a)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toColex", 1)
    if args is not None:
        try:
            rhs = OVar("toColex_a_inv")
            results.append((rhs, "Mathlib: toColex_inv"))
        except Exception:
            pass
    return results


def _r0247_ofColex_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofColex_inv
    # ofColex a⁻¹ = (ofColex a)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofColex", 1)
    if args is not None:
        try:
            rhs = OVar("ofColex_a_inv")
            results.append((rhs, "Mathlib: ofColex_inv"))
        except Exception:
            pass
    return results


def _r0248_toColex_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toColex_div
    # toColex (a / b) = toColex a / toColex b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toColex", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("toColex", (OVar("a"),)), OOp("toColex", (OVar("b"),))))
            results.append((rhs, "Mathlib: toColex_div"))
        except Exception:
            pass
    return results


def _r0249_ofColex_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofColex_div
    # ofColex (a / b) = ofColex a / ofColex b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofColex", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("ofColex", (OVar("a"),)), OOp("ofColex", (OVar("b"),))))
            results.append((rhs, "Mathlib: ofColex_div"))
        except Exception:
            pass
    return results


def _r0250_toColex_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toColex_pow
    # toColex (a ^ b) = toColex a ^ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toColex", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("toColex", (OVar("a"),)), OVar("b")))
            results.append((rhs, "Mathlib: toColex_pow"))
        except Exception:
            pass
    return results


def _r0251_ofColex_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofColex_pow
    # ofColex (a ^ b) = ofColex a ^ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofColex", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("ofColex", (OVar("a"),)), OVar("b")))
            results.append((rhs, "Mathlib: ofColex_pow"))
        except Exception:
            pass
    return results


def _r0252_pow_toColex(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_toColex
    # a ^ toColex b = a ^ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], OVar("b")))
            results.append((rhs, "Mathlib: pow_toColex"))
        except Exception:
            pass
    return results


def _r0253_pow_ofColex(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_ofColex
    # a ^ ofColex b = a ^ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], OVar("b")))
            results.append((rhs, "Mathlib: pow_ofColex"))
        except Exception:
            pass
    return results


def _r0254_mabs_div_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mabs_div_comm
    # |a / b|ₘ = |b / a|ₘ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("pipe_b"), OVar("apipe")))
            results.append((rhs, "Mathlib: mabs_div_comm"))
        except Exception:
            pass
    return results


def _r0255_mabs_ite(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mabs_ite
    # |if p then a else b|ₘ = if p then |a|ₘ else |b|ₘ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pipe_if", 5)
    if args is not None:
        try:
            rhs = OOp("if", (args[0], args[1], OVar("pipe_apipe"), args[3], OVar("pipe_bpipe"),))
            results.append((rhs, "Mathlib: mabs_ite"))
        except Exception:
            pass
    return results


def _r0256_mabs_le_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mabs_le_one
    # |a|ₘ ≤ 1 ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: mabs_le_one"))
        except Exception:
            pass
    return results


def _r0257_abs_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Pi.abs_def
    # |f| = fun i ↦ |f i|
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pipe_fpipe")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("fun", (OVar("i"), OVar("_unknown"), OVar("pipe_f"), OVar("ipipe"),))
            results.append((rhs, "Mathlib: Pi_abs_def"))
    except Exception:
        pass
    return results


def _r0258_le_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: le_zero_iff
    # a ≤ 0 ↔ a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: le_zero_iff"))
        except Exception:
            pass
    return results


def _r0259_ofDual_toAdd_eq_top_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofDual_toAdd_eq_top_iff
    # OrderDual.ofDual x.toAdd = ⊤ ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "OrderDual_ofDual", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("top"), OVar("x"))), OLit(0)))
            results.append((rhs, "Mathlib: ofDual_toAdd_eq_top_iff"))
        except Exception:
            pass
    return results


def _r0260_ofAdd_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofAdd_bot
    # Multiplicative.ofAdd ⊥ = (0 : Multiplicative αᵒᵈ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Multiplicative_ofAdd", 1)
    if args is not None:
        try:
            rhs = OOp("_0", (OVar("colon"), OVar("Multiplicative"), OVar("a"),))
            results.append((rhs, "Mathlib: ofAdd_bot"))
        except Exception:
            pass
    return results


def _r0261_nonpos_iff_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: nonpos_iff_eq_zero
    # x ≤ 0 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: nonpos_iff_eq_zero"))
        except Exception:
            pass
    return results


def _r0262_coe_le_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_le_iff
    # a ≤ x ↔ ∃ b : α, x = b ∧ a ≤ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("and", (OVar("b"), args[0])), OVar("b")))
            results.append((rhs, "Mathlib: coe_le_iff"))
        except Exception:
            pass
    return results


def _r0263_le_coe_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: le_coe_iff
    # x ≤ b ↔ ∀ a : α, x = ↑a → a ≤ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("implies", (OVar("a"), OVar("a"))), OVar("b")))
            results.append((rhs, "Mathlib: le_coe_iff"))
        except Exception:
            pass
    return results


def _r0264_lt_iff_exists_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: lt_iff_exists_coe
    # x < y ↔ ∃ b : α, y = b ∧ x < b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("and", (OVar("b"), args[0])), OVar("b")))
            results.append((rhs, "Mathlib: lt_iff_exists_coe"))
        except Exception:
            pass
    return results


def _r0265_lt_coe_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: lt_coe_iff
    # x < b ↔ ∀ a : α, x = a → a < b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("implies", (OVar("a"), OVar("a"))), OVar("b")))
            results.append((rhs, "Mathlib: lt_coe_iff"))
        except Exception:
            pass
    return results


def _r0266_pow_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_nonneg
    # ∀ n, 0 ≤ a ^ n   | 0 => pow_zero a ▸ zero_le_one   | n + 1 => pow_succ a n ▸ mul_nonneg (pow_nonneg ha _) ha  lemma zero
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("+", (OOp("subst", (OOp("gt", (OVar("pow_zero"), OVar("a"),)), OOp("zero_le_one", (OVar("pipe"), OVar("n"),)))), OOp("subst", (OOp("_1", (OVar("eq_gt"), OVar("pow_succ"), OVar("a"), OVar("n"),)), OOp("**", (OOp("mul_nonneg", (OOp("pow_nonneg", (OVar("ha"), OVar("_unknown"),)), OVar("ha_lemma"), OVar("zero_pow_le_one"), OSeq((OOp("ZeroLEOneClass", (OVar("M_0"),)),)), OVar("colon"), OVar("forall"), OVar("n"), OVar("colon"), OVar("_unknown"), OOp("_0", (OVar("colon"), OVar("M_0"),)),)), OVar("n"))))))), OOp("+", (OOp("_1", (OVar("pipe"), OLit(0), OVar("eq_gt"), OVar("pow_zero_le"), OVar("pipe"), OVar("n"),)), OOp("_1", (OVar("eq_gt"),))))))
            results.append((rhs, "Mathlib: pow_nonneg"))
        except Exception:
            pass
    return results


def _r0267_zero_pow_le_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: zero_pow_le_one
    # ∀ n : ℕ, (0 : M₀) ^ n ≤ 1   | 0 => (pow_zero _).le   | n + 1 =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("gt", (OVar("pow_zero_le"), OVar("pipe"), OVar("n"),)), OOp("_1", (OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: zero_pow_le_one"))
        except Exception:
            pass
    return results


def _r0268_pow_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_pos
    # ∀ n, 0 < a ^ n   | 0 =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: pow_pos"))
        except Exception:
            pass
    return results


def _r0269_pow_lt_pow_left_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_lt_pow_left₀
    # ∀ {n : ℕ}, n ≠ 0 → a ^ n < b ^ n   | 1, _ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: pow_lt_pow_left_0"))
        except Exception:
            pass
    return results


def _r0270_zpow_eq_one_iff_right_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: zpow_eq_one_iff_right₀
    # a ^ n = 1 ↔ n = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[1])), OLit(0)))
            results.append((rhs, "Mathlib: zpow_eq_one_iff_right_0"))
        except Exception:
            pass
    return results


def _r0271_mul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_apply
    # (f * g) a = f a * g a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_star_g", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("f", (args[0],)), OOp("g", (args[0],))))
            results.append((rhs, "Mathlib: mul_apply"))
        except Exception:
            pass
    return results


def _r0272_mul_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_comp
    # (g₁ * g₂).comp f = g₁.comp f * g₂.comp f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_1_star_g_2_comp", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("g_1_comp", (args[0],)), OOp("g_2_comp", (args[0],))))
            results.append((rhs, "Mathlib: mul_comp"))
        except Exception:
            pass
    return results


def _r0273_toOrderHom_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toOrderHom_eq_coe
    # f.toOrderHom = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toOrderHom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: toOrderHom_eq_coe"))
    except Exception:
        pass
    return results


def _r0274_mul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_apply
    # (f * g) a = f a * g a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_star_g", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("f", (args[0],)), OOp("g", (args[0],))))
            results.append((rhs, "Mathlib: mul_apply"))
        except Exception:
            pass
    return results


def _r0275_mul_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_comp
    # (g₁ * g₂).comp f = g₁.comp f * g₂.comp f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_1_star_g_2_comp", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("g_1_comp", (args[0],)), OOp("g_2_comp", (args[0],))))
            results.append((rhs, "Mathlib: mul_comp"))
        except Exception:
            pass
    return results


def _r0276_fst_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonemptyInterval.fst_one
    # (1 : NonemptyInterval α).fst = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_NonemptyInterval_a_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: NonemptyInterval_fst_one"))
    except Exception:
        pass
    return results


def _r0277_pure_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonemptyInterval.pure_one
    # pure (1 : α) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pure", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: NonemptyInterval_pure_one"))
        except Exception:
            pass
    return results


def _r0278_fst_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonemptyInterval.fst_mul
    # (s * t).fst = s.fst * t.fst
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_star_t_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("s_fst"), OVar("t_fst")))
            results.append((rhs, "Mathlib: NonemptyInterval_fst_mul"))
    except Exception:
        pass
    return results


def _r0279_pure_mul_pure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonemptyInterval.pure_mul_pure
    # pure a * pure b = pure (a * b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("pure", (OOp("*", (OVar("a"), OVar("b"))),))
            results.append((rhs, "Mathlib: NonemptyInterval_pure_mul_pure"))
        except Exception:
            pass
    return results


def _r0280_fst_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonemptyInterval.fst_pow
    # (s ^ n).fst = s.fst ^ n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_pow_n_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OVar("s_fst"), OVar("n")))
            results.append((rhs, "Mathlib: NonemptyInterval_fst_pow"))
    except Exception:
        pass
    return results


def _r0281_snd_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonemptyInterval.snd_sub
    # (s - t).snd = s.snd - t.fst
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_minus_t_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("s_snd"), OVar("t_fst")))
            results.append((rhs, "Mathlib: NonemptyInterval_snd_sub"))
    except Exception:
        pass
    return results


def _r0282_coe_sub_interval(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonemptyInterval.coe_sub_interval
    # (↑(s - t) : Interval α) = s - t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_minus_t", 3)
    if args is not None:
        try:
            rhs = OOp("-", (OVar("s"), OVar("t")))
            results.append((rhs, "Mathlib: NonemptyInterval_coe_sub_interval"))
        except Exception:
            pass
    return results


def _r0283_snd_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonemptyInterval.snd_div
    # (s / t).snd = s.snd / t.fst
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_slash_t_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("//", (OVar("s_snd"), OVar("t_fst")))
            results.append((rhs, "Mathlib: NonemptyInterval_snd_div"))
    except Exception:
        pass
    return results


def _r0284_coe_div_interval(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonemptyInterval.coe_div_interval
    # (↑(s / t) : Interval α) = s / t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_slash_t", 3)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("s"), OVar("t")))
            results.append((rhs, "Mathlib: NonemptyInterval_coe_div_interval"))
        except Exception:
            pass
    return results


def _r0285_snd_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonemptyInterval.snd_inv
    # s⁻¹.snd = s.fst⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sinv_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_fstinv")
            results.append((rhs, "Mathlib: NonemptyInterval_snd_inv"))
    except Exception:
        pass
    return results


def _r0286_coe_inv_interval(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonemptyInterval.coe_inv_interval
    # (↑(s⁻¹) : Interval α) = (↑s)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sinv", 3)
    if args is not None:
        try:
            rhs = OVar("s_inv")
            results.append((rhs, "Mathlib: NonemptyInterval_coe_inv_interval"))
        except Exception:
            pass
    return results


def _r0287_length_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonemptyInterval.length_neg
    # (-s).length = s.length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_s_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_length")
            results.append((rhs, "Mathlib: NonemptyInterval_length_neg"))
    except Exception:
        pass
    return results


def _r0288_length_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonemptyInterval.length_add
    # (s + t).length = s.length + t.length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_plus_t_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("s_length"), OVar("t_length")))
            results.append((rhs, "Mathlib: NonemptyInterval_length_add"))
    except Exception:
        pass
    return results


def _r0289_length_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonemptyInterval.length_sub
    # (s - t).length = s.length + t.length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_minus_t_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("s_length"), OVar("t_length")))
            results.append((rhs, "Mathlib: NonemptyInterval_length_sub"))
    except Exception:
        pass
    return results


def _r0290_length_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonemptyInterval.length_sum
    # (∑ i ∈ s, f i).length = ∑ i ∈ s, (f i).length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("i_in_s_f_i_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("f_i_length"),))))
            results.append((rhs, "Mathlib: NonemptyInterval_length_sum"))
    except Exception:
        pass
    return results


def _r0291_kstar_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: kstar_one
    # (1 : α)∗ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: kstar_one"))
    except Exception:
        pass
    return results


def _r0292_kstar_mul_kstar(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: kstar_mul_kstar
    # a∗ * a∗ = a∗
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: kstar_mul_kstar"))
        except Exception:
            pass
    return results


def _r0293_kstar_eq_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: kstar_eq_self
    # a∗ = a ↔ a * a = a ∧ 1 ≤ a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("a"), OOp("*", (OVar("a"), OVar("a"))))), OOp("<=", (OOp("and", (OVar("a"), OLit(1))), OVar("a")))))
            results.append((rhs, "Mathlib: kstar_eq_self"))
    except Exception:
        pass
    return results


def _r0294_pow_le_kstar(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_le_kstar
    # ∀ {n : ℕ}, a ^ n ≤ a∗   | 0 => (pow_zero _).trans_le one_le_kstar   | n + 1 =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("gt", (OVar("pow_zero_trans_le"), OVar("one_le_kstar"), OVar("pipe"), OVar("n"),)), OOp("_1", (OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: pow_le_kstar"))
        except Exception:
            pass
    return results


def _r0295_toAddSubgroup_closedBall(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.toAddSubgroup_closedBall
    # (closedBall K c).toAddSubgroup = closedBallAddSubgroup c
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("closedBall_K_c_toAddSubgroup")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("closedBallAddSubgroup", (OVar("c"),))
            results.append((rhs, "Mathlib: ArchimedeanClass_toAddSubgroup_closedBall"))
    except Exception:
        pass
    return results


def _r0296_coe_ofLexLinearEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_ofLexLinearEquiv
    # ⇑(ofLexLinearEquiv α β) = ofLex
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofLexLinearEquiv_a_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("ofLex")
            results.append((rhs, "Mathlib: coe_ofLexLinearEquiv"))
    except Exception:
        pass
    return results


def _r0297_symm_toLexLinearEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: symm_toLexLinearEquiv
    # (toLexLinearEquiv α β).symm = ofLexLinearEquiv α β
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("toLexLinearEquiv_a_b_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("ofLexLinearEquiv", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: symm_toLexLinearEquiv"))
    except Exception:
        pass
    return results


def _r0298_symm_ofLexLinearEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: symm_ofLexLinearEquiv
    # (ofLexLinearEquiv α β).symm = toLexLinearEquiv α β
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofLexLinearEquiv_a_b_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("toLexLinearEquiv", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: symm_ofLexLinearEquiv"))
    except Exception:
        pass
    return results


def _r0299_upperBounds_smul_of_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: upperBounds_smul_of_pos
    # upperBounds (a • s) = a • upperBounds s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "upperBounds", 1)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("upperBounds"), OVar("s"),))
            results.append((rhs, "Mathlib: upperBounds_smul_of_pos"))
        except Exception:
            pass
    return results


def _r0300_upperBounds_smul_of_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: upperBounds_smul_of_neg
    # upperBounds (a • s) = a • lowerBounds s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "upperBounds", 1)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("lowerBounds"), OVar("s"),))
            results.append((rhs, "Mathlib: upperBounds_smul_of_neg"))
        except Exception:
            pass
    return results


def _r0301_le_iff_exists_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: le_iff_exists_mul
    # a ≤ b ↔ ∃ c, b = a * c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("*", (args[0], OVar("c")))
            results.append((rhs, "Mathlib: le_iff_exists_mul"))
        except Exception:
            pass
    return results


def _r0302_orderAddMonoidHom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: LocallyFiniteOrder.orderAddMonoidHom_apply
    # orderAddMonoidHom G x = addMonoidHom G x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "orderAddMonoidHom", 2)
    if args is not None:
        try:
            rhs = OOp("addMonoidHom", (args[0], args[1],))
            results.append((rhs, "Mathlib: LocallyFiniteOrder_orderAddMonoidHom_apply"))
        except Exception:
            pass
    return results


def _r0303_toMulBot_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithZero.toMulBot_coe
    # toMulBot ↑x = Multiplicative.ofAdd (↑x.toAdd : WithBot α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toMulBot", 1)
    if args is not None:
        try:
            rhs = OOp("Multiplicative_ofAdd", (OOp("x_toAdd", (OVar("colon"), OVar("WithBot"), OVar("a"),)),))
            results.append((rhs, "Mathlib: WithZero_toMulBot_coe"))
        except Exception:
            pass
    return results


def _r0304_toMulBot_coe_ofAdd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithZero.toMulBot_coe_ofAdd
    # toMulBot.symm (Multiplicative.ofAdd (x : WithBot α)) = Multiplicative.ofAdd x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toMulBot_symm", 1)
    if args is not None:
        try:
            rhs = OOp("Multiplicative_ofAdd", (OVar("x"),))
            results.append((rhs, "Mathlib: WithZero_toMulBot_coe_ofAdd"))
        except Exception:
            pass
    return results


def _r0305_max_mul_min(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: max_mul_min
    # max a b * min a b = a * b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("a"), OVar("b")))
            results.append((rhs, "Mathlib: max_mul_min"))
        except Exception:
            pass
    return results


def _r0306_toMul_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toMul_top
    # toMul ⊤ = (⊤ : α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toMul", 1)
    if args is not None:
        try:
            rhs = OOp("top", (OVar("colon"), OVar("a"),))
            results.append((rhs, "Mathlib: toMul_top"))
        except Exception:
            pass
    return results


def _r0307_ofMul_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofMul_eq_top
    # ofMul a = ⊤ ↔ a = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofMul", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("top"), args[0])), OVar("top")))
            results.append((rhs, "Mathlib: ofMul_eq_top"))
        except Exception:
            pass
    return results


def _r0308_toMul_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toMul_eq_top
    # toMul a = ⊤ ↔ a = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toMul", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("top"), args[0])), OVar("top")))
            results.append((rhs, "Mathlib: toMul_eq_top"))
        except Exception:
            pass
    return results


def _r0309_toMul_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toMul_bot
    # toMul ⊥ = (⊥ : α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toMul", 1)
    if args is not None:
        try:
            rhs = OOp("bot", (OVar("colon"), OVar("a"),))
            results.append((rhs, "Mathlib: toMul_bot"))
        except Exception:
            pass
    return results


def _r0310_ofMul_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofMul_eq_bot
    # ofMul a = ⊥ ↔ a = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofMul", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("bot"), args[0])), OVar("bot")))
            results.append((rhs, "Mathlib: ofMul_eq_bot"))
        except Exception:
            pass
    return results


def _r0311_toMul_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toMul_eq_bot
    # toMul a = ⊥ ↔ a = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toMul", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("bot"), args[0])), OVar("bot")))
            results.append((rhs, "Mathlib: toMul_eq_bot"))
        except Exception:
            pass
    return results


def _r0312_toAdd_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toAdd_top
    # toAdd ⊤ = (⊤ : α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toAdd", 1)
    if args is not None:
        try:
            rhs = OOp("top", (OVar("colon"), OVar("a"),))
            results.append((rhs, "Mathlib: toAdd_top"))
        except Exception:
            pass
    return results


def _r0313_ofAdd_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofAdd_eq_top
    # ofAdd a = ⊤ ↔ a = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofAdd", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("top"), args[0])), OVar("top")))
            results.append((rhs, "Mathlib: ofAdd_eq_top"))
        except Exception:
            pass
    return results


def _r0314_toAdd_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toAdd_eq_top
    # toAdd a = ⊤ ↔ a = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toAdd", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("top"), args[0])), OVar("top")))
            results.append((rhs, "Mathlib: toAdd_eq_top"))
        except Exception:
            pass
    return results


def _r0315_toAdd_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toAdd_bot
    # toAdd ⊥ = (⊥ : α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toAdd", 1)
    if args is not None:
        try:
            rhs = OOp("bot", (OVar("colon"), OVar("a"),))
            results.append((rhs, "Mathlib: toAdd_bot"))
        except Exception:
            pass
    return results


def _r0316_ofAdd_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofAdd_eq_bot
    # ofAdd a = ⊥ ↔ a = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofAdd", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("bot"), args[0])), OVar("bot")))
            results.append((rhs, "Mathlib: ofAdd_eq_bot"))
        except Exception:
            pass
    return results


def _r0317_toAdd_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toAdd_eq_bot
    # toAdd a = ⊥ ↔ a = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toAdd", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("bot"), args[0])), OVar("bot")))
            results.append((rhs, "Mathlib: toAdd_eq_bot"))
        except Exception:
            pass
    return results


def _r0318_coe_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithTop.coe_eq_one
    # (a : WithTop α) = 1 ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[2])), OLit(1)))
            results.append((rhs, "Mathlib: WithTop_coe_eq_one"))
        except Exception:
            pass
    return results


def _r0319_untop_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithTop.untop_one
    # (1 : WithTop α).untop coe_ne_top = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_WithTop_a_untop", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: WithTop_untop_one"))
        except Exception:
            pass
    return results


def _r0320_untopD_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithTop.untopD_one
    # (1 : WithTop α).untopD d = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_WithTop_a_untopD", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: WithTop_untopD_one"))
        except Exception:
            pass
    return results


def _r0321_map_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithTop.map_one
    # (1 : WithTop α).map f = (f 1 : WithTop β)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_WithTop_a_map", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OLit(1), OVar("colon"), OVar("WithTop"), OVar("b"),))
            results.append((rhs, "Mathlib: WithTop_map_one"))
        except Exception:
            pass
    return results


def _r0322_map_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithTop.map_eq_one_iff
    # WithTop.map f v = 1 ↔ ∃ x, v = .some x ∧ f x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "WithTop_map", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), OOp("exists", (OVar("x"), args[1],)))), OOp("==", (OOp("and", (OOp("some", (OVar("x"),)), OOp("f", (OVar("x"),)))), OLit(1)))))
            results.append((rhs, "Mathlib: WithTop_map_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0323_top_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: top_add
    # ⊤ + x = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: top_add"))
        except Exception:
            pass
    return results


def _r0324_add_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: add_top
    # x + ⊤ = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: add_top"))
        except Exception:
            pass
    return results


def _r0325_add_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: add_eq_top
    # x + y = ⊤ ↔ x = ⊤ ∨ y = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("top"), args[0])), OOp("==", (OOp("or", (OVar("top"), args[1])), OVar("top")))))
            results.append((rhs, "Mathlib: add_eq_top"))
        except Exception:
            pass
    return results


def _r0326_add_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: add_eq_coe
    # ∀ {a b : WithTop α} {c : α}, a + b = c ↔ ∃ a' b' : α, ↑a' = a ∧ ↑b' = b ∧ a' + b' = c   | ⊤, b, c =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("c"), OOp("exists", (OVar("a_prime"), OVar("b_prime"), OVar("colon"), args[0], OVar("a_prime"),)))), OOp("==", (OOp("and", (args[0], OVar("b_prime"))), OOp("==", (OOp("and", (args[1], OOp("+", (OVar("a_prime"), OVar("b_prime"))))), OOp("c", (OVar("pipe"), OVar("top"), args[1], OVar("c"), OVar("eq_gt"),))))))))
            results.append((rhs, "Mathlib: add_eq_coe"))
        except Exception:
            pass
    return results


def _r0327_coe_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_ofNat
    # ((ofNat(n) : α) : WithTop α) = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofNat_n_colon_a", 3)
    if args is not None:
        try:
            rhs = OVar("ofNat_n")
            results.append((rhs, "Mathlib: coe_ofNat"))
        except Exception:
            pass
    return results


def _r0328_coe_eq_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_eq_ofNat
    # (m : WithTop α) = ofNat(n) ↔ m = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("ofNat_n"), OVar("m"))), OVar("ofNat_n")))
            results.append((rhs, "Mathlib: coe_eq_ofNat"))
        except Exception:
            pass
    return results


def _r0329_ofNat_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofNat_eq_coe
    # ofNat(n) = (m : WithTop α) ↔ ofNat(n) = m
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofNat_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("m", (OVar("colon"), OVar("WithTop"), OVar("a"),)), OVar("ofNat_n"))), OVar("m")))
            results.append((rhs, "Mathlib: ofNat_eq_coe"))
    except Exception:
        pass
    return results


def _r0330_map_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: map_ofNat
    # WithTop.map f (ofNat(n) : WithTop α) = f (ofNat(n))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "WithTop_map", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("ofNat_n"),))
            results.append((rhs, "Mathlib: map_ofNat"))
        except Exception:
            pass
    return results


def _r0331_map_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: map_natCast
    # WithTop.map f (n : WithTop α) = f n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "WithTop_map", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("n"),))
            results.append((rhs, "Mathlib: map_natCast"))
        except Exception:
            pass
    return results


def _r0332_map_eq_ofNat_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: map_eq_ofNat_iff
    # a.map f = ofNat(n) ↔ ∃ x, a = .some x ∧ f x = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_map", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("ofNat_n"), OOp("exists", (OVar("x"), OVar("a"),)))), OOp("==", (OOp("and", (OOp("some", (OVar("x"),)), OOp("f", (OVar("x"),)))), OVar("n")))))
            results.append((rhs, "Mathlib: map_eq_ofNat_iff"))
        except Exception:
            pass
    return results


def _r0333_coe_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithBot.coe_eq_one
    # (a : WithBot α) = 1 ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[2])), OLit(1)))
            results.append((rhs, "Mathlib: WithBot_coe_eq_one"))
        except Exception:
            pass
    return results


def _r0334_one_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithBot.one_eq_coe
    # 1 = (a : WithBot α) ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    if _is_lit(term, 1):
        try:
            rhs = OOp("==", (OOp("iff", (OOp("a", (OVar("colon"), OVar("WithBot"), OVar("a"),)), OVar("a"))), OLit(1)))
            results.append((rhs, "Mathlib: WithBot_one_eq_coe"))
        except Exception:
            pass
    return results


def _r0335_unbot_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithBot.unbot_one
    # (1 : WithBot α).unbot coe_ne_bot = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_WithBot_a_unbot", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: WithBot_unbot_one"))
        except Exception:
            pass
    return results


def _r0336_unbotD_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithBot.unbotD_one
    # (1 : WithBot α).unbotD d = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_WithBot_a_unbotD", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: WithBot_unbotD_one"))
        except Exception:
            pass
    return results


def _r0337_map_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithBot.map_one
    # (1 : WithBot α).map f = (f 1 : WithBot β)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_WithBot_a_map", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OLit(1), OVar("colon"), OVar("WithBot"), OVar("b"),))
            results.append((rhs, "Mathlib: WithBot_map_one"))
        except Exception:
            pass
    return results


def _r0338_map_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithBot.map_eq_one_iff
    # WithBot.map f v = 1 ↔ ∃ x, v = .some x ∧ f x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "WithBot_map", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), OOp("exists", (OVar("x"), args[1],)))), OOp("==", (OOp("and", (OOp("some", (OVar("x"),)), OOp("f", (OVar("x"),)))), OLit(1)))))
            results.append((rhs, "Mathlib: WithBot_map_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0339_bot_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: bot_add
    # ⊥ + x = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: bot_add"))
        except Exception:
            pass
    return results


def _r0340_add_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: add_bot
    # x + ⊥ = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: add_bot"))
        except Exception:
            pass
    return results


def _r0341_add_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: add_eq_bot
    # x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("bot"), args[0])), OOp("==", (OOp("or", (OVar("bot"), args[1])), OVar("bot")))))
            results.append((rhs, "Mathlib: add_eq_bot"))
        except Exception:
            pass
    return results


def _r0342_add_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: add_eq_coe
    # ∀ {a b : WithBot α} {c : α}, a + b = c ↔ ∃ a' b' : α, ↑a' = a ∧ ↑b' = b ∧ a' + b' = c   | ⊥, b, c =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("c"), OOp("exists", (OVar("a_prime"), OVar("b_prime"), OVar("colon"), args[0], OVar("a_prime"),)))), OOp("==", (OOp("and", (args[0], OVar("b_prime"))), OOp("==", (OOp("and", (args[1], OOp("+", (OVar("a_prime"), OVar("b_prime"))))), OOp("c", (OVar("pipe"), OVar("bot"), args[1], OVar("c"), OVar("eq_gt"),))))))))
            results.append((rhs, "Mathlib: add_eq_coe"))
        except Exception:
            pass
    return results


def _r0343_coe_nsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_nsmul
    # ↑(n • a) = n • (a : WithBot α)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("n", (OVar("_unknown"), OOp("a", (OVar("colon"), OVar("WithBot"), OVar("a"),)),))
            results.append((rhs, "Mathlib: coe_nsmul"))
    except Exception:
        pass
    return results


def _r0344_coe_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_ofNat
    # ((ofNat(n) : α) : WithBot α) = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofNat_n_colon_a", 3)
    if args is not None:
        try:
            rhs = OVar("ofNat_n")
            results.append((rhs, "Mathlib: coe_ofNat"))
        except Exception:
            pass
    return results


def _r0345_coe_eq_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_eq_ofNat
    # (m : WithBot α) = ofNat(n) ↔ m = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("ofNat_n"), OVar("m"))), OVar("ofNat_n")))
            results.append((rhs, "Mathlib: coe_eq_ofNat"))
        except Exception:
            pass
    return results


def _r0346_ofNat_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofNat_eq_coe
    # ofNat(n) = (m : WithBot α) ↔ ofNat(n) = m
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofNat_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("m", (OVar("colon"), OVar("WithBot"), OVar("a"),)), OVar("ofNat_n"))), OVar("m")))
            results.append((rhs, "Mathlib: ofNat_eq_coe"))
    except Exception:
        pass
    return results


def _r0347_map_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: map_ofNat
    # WithBot.map f (ofNat(n) : WithBot α) = f ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "WithBot_map", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("ofNat_n"),))
            results.append((rhs, "Mathlib: map_ofNat"))
        except Exception:
            pass
    return results


def _r0348_map_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: map_natCast
    # WithBot.map f (n : WithBot α) = f n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "WithBot_map", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("n"),))
            results.append((rhs, "Mathlib: map_natCast"))
        except Exception:
            pass
    return results


def _r0349_map_eq_ofNat_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: map_eq_ofNat_iff
    # a.map f = ofNat(n) ↔ ∃ x, a = .some x ∧ f x = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_map", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("ofNat_n"), OOp("exists", (OVar("x"), OVar("a"),)))), OOp("==", (OOp("and", (OOp("some", (OVar("x"),)), OOp("f", (OVar("x"),)))), OVar("n")))))
            results.append((rhs, "Mathlib: map_eq_ofNat_iff"))
        except Exception:
            pass
    return results


def _r0350_mk_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nonneg.mk_eq_zero
    # (⟨x, hx⟩ : { x : α // 0 ≤ x }) = 0 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_hx", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("x"))), OLit(0)))
            results.append((rhs, "Mathlib: Nonneg_mk_eq_zero"))
        except Exception:
            pass
    return results


def _r0351_mk_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nonneg.mk_eq_one
    # (⟨x, hx⟩ : { x : α // 0 ≤ x }) = 1 ↔ x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_hx", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), OVar("x"))), OLit(1)))
            results.append((rhs, "Mathlib: Nonneg_mk_eq_one"))
        except Exception:
            pass
    return results


def _r0352_mk_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mk_natCast
    # (⟨n, n.cast_nonneg'⟩ : { x : α // 0 ≤ x }) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n_n_cast_nonneg_prime", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: mk_natCast"))
        except Exception:
            pass
    return results


def _r0353_toNonneg_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toNonneg_of_nonneg
    # toNonneg a = ⟨a, h⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toNonneg", 1)
    if args is not None:
        try:
            rhs = OVar("a_h")
            results.append((rhs, "Mathlib: toNonneg_of_nonneg"))
        except Exception:
            pass
    return results


def _r0354_toNonneg_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toNonneg_coe
    # toNonneg (a : α) = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toNonneg", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: toNonneg_coe"))
        except Exception:
            pass
    return results


def _r0355_inv_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nonneg.inv_mk
    # (⟨x, hx⟩ : { x : α // 0 ≤ x })⁻¹ = ⟨x⁻¹, inv_nonneg.2 hx⟩
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_hx_colon_x_colon_a_slash_slash_0_le_x_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("xinv_inv_nonneg_2_hx")
            results.append((rhs, "Mathlib: Nonneg_inv_mk"))
    except Exception:
        pass
    return results


def _r0356_mk_div_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nonneg.mk_div_mk
    # (⟨x, hx⟩ : { x : α // 0 ≤ x }) / ⟨y, hy⟩ = ⟨x / y, div_nonneg hx hy⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OVar("x_slash_y_div_nonneg_hx_hy")
            results.append((rhs, "Mathlib: Nonneg_mk_div_mk"))
        except Exception:
            pass
    return results


def _r0357_mk_nnratCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nonneg.mk_nnratCast
    # (⟨q, q.cast_nonneg⟩ : {x : α // 0 ≤ x}) = q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "q_q_cast_nonneg", 2)
    if args is not None:
        try:
            rhs = OVar("q")
            results.append((rhs, "Mathlib: Nonneg_mk_nnratCast"))
        except Exception:
            pass
    return results


def _r0358_coe_nnqsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nonneg.coe_nnqsmul
    # ↑(q • a) = (q • a : α)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("q_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("q", (OVar("_unknown"), OVar("a"), OVar("colon"), OVar("a"),))
            results.append((rhs, "Mathlib: Nonneg_coe_nnqsmul"))
    except Exception:
        pass
    return results


def _r0359_mk_nnqsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nonneg.mk_nnqsmul
    # (⟨q • a, by rw [NNRat.smul_def]; exact mul_nonneg q.cast_nonneg ha⟩ : {x : α // 0 ≤ x}) =       q • a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "q_a_by_rw_NNRat_smul_def_exact_mul_nonneg_q_cast_nonneg_ha", 2)
    if args is not None:
        try:
            rhs = OOp("q", (OVar("_unknown"), OVar("a"),))
            results.append((rhs, "Mathlib: Nonneg_mk_nnqsmul"))
        except Exception:
            pass
    return results


def _r0360_mk_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nonneg.mk_smul
    # (⟨a, ha⟩ : R≥0) • x = a • x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_ha_colon_Rge_0", 2)
    if args is not None:
        try:
            rhs = OOp("a", (args[0], args[1],))
            results.append((rhs, "Mathlib: Nonneg_mk_smul"))
        except Exception:
            pass
    return results


def _r0361_abs_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: abs_two
    # |(2 : α)| = 2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pipe_2_colon_a_pipe")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(2)
            results.append((rhs, "Mathlib: abs_two"))
    except Exception:
        pass
    return results


def _r0362_abs_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: abs_mul
    # |a * b| = |a| * |b|
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("pipe_apipe"), OVar("pipe_bpipe")))
            results.append((rhs, "Mathlib: abs_mul"))
        except Exception:
            pass
    return results


def _r0363_pow_abs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_abs
    # |a| ^ n = |a ^ n|
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("pipe_a"), OVar("npipe")))
            results.append((rhs, "Mathlib: pow_abs"))
        except Exception:
            pass
    return results


def _r0364_abs_mul_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: abs_mul_self
    # |a * a| = a * a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("a"), OVar("a")))
            results.append((rhs, "Mathlib: abs_mul_self"))
        except Exception:
            pass
    return results


def _r0365_abs_sq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: abs_sq
    # |x ^ 2| = x ^ 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("x"), OLit(2)))
            results.append((rhs, "Mathlib: abs_sq"))
        except Exception:
            pass
    return results


def _r0366_orderHom_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.orderHom_zero
    # orderHom f 0 = mk (f 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "orderHom", 2)
    if args is not None:
        try:
            rhs = OOp("pair", (OOp("f", (OLit(1),)),))
            results.append((rhs, "Mathlib: ArchimedeanClass_orderHom_zero"))
        except Exception:
            pass
    return results


def _r0367_mk_eq_zero_of_archimedean(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.mk_eq_zero_of_archimedean
    # mk x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ArchimedeanClass_mk_eq_zero_of_archimedean"))
        except Exception:
            pass
    return results


def _r0368_eq_zero_or_top_of_archimedean(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.eq_zero_or_top_of_archimedean
    # x = 0 ∨ x = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("or", (OLit(0), OVar("x"))), OVar("top")))
            results.append((rhs, "Mathlib: ArchimedeanClass_eq_zero_or_top_of_archimedean"))
    except Exception:
        pass
    return results


def _r0369_mk_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.mk_ofNat
    # mk (ofNat(n) : S) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ArchimedeanClass_mk_ofNat"))
        except Exception:
            pass
    return results


def _r0370_mk_ratCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mk_ratCast
    # mk (q : R) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: mk_ratCast"))
        except Exception:
            pass
    return results


def _r0371_cast_max(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: cast_max
    # (↑(max a b) : R) = max (a : R) (b : R)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "max_a_b", 2)
    if args is not None:
        try:
            rhs = OOp("max", (OOp("a", (args[0], args[1],)), OOp("b", (args[0], args[1],)),))
            results.append((rhs, "Mathlib: cast_max"))
        except Exception:
            pass
    return results


def _r0372_cast_abs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: cast_abs
    # (↑|a| : R) = |(a : R)|
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pipe_apipe", 2)
    if args is not None:
        try:
            rhs = OVar("pipe_a_colon_R_pipe")
            results.append((rhs, "Mathlib: cast_abs"))
        except Exception:
            pass
    return results


def _r0373_ofLex_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofLex_intCast
    # (ofLex n : R) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofLex", 3)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ofLex_intCast"))
        except Exception:
            pass
    return results


def _r0374_stdPart_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.stdPart_one
    # stdPart (1 : K) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "stdPart", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ArchimedeanClass_stdPart_one"))
        except Exception:
            pass
    return results


def _r0375_stdPart_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.stdPart_neg
    # stdPart (-x) = -stdPart x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "stdPart", 1)
    if args is not None:
        try:
            rhs = OOp("minus_stdPart", (OVar("x"),))
            results.append((rhs, "Mathlib: ArchimedeanClass_stdPart_neg"))
        except Exception:
            pass
    return results


def _r0376_stdPart_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.stdPart_natCast
    # stdPart (n : K) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "stdPart", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: ArchimedeanClass_stdPart_natCast"))
        except Exception:
            pass
    return results


def _r0377_stdPart_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.stdPart_ofNat
    # stdPart (ofNat(n) : K) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "stdPart", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: ArchimedeanClass_stdPart_ofNat"))
        except Exception:
            pass
    return results


def _r0378_stdPart_map_real(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.stdPart_map_real
    # stdPart (f r) = r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "stdPart", 1)
    if args is not None:
        try:
            rhs = OVar("r")
            results.append((rhs, "Mathlib: ArchimedeanClass_stdPart_map_real"))
        except Exception:
            pass
    return results


def _r0379_ofArchimedean_stdPart(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.ofArchimedean_stdPart
    # FiniteResidueField.ofArchimedean f (stdPart x) = .mk (.mk x hx)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "FiniteResidueField_ofArchimedean", 2)
    if args is not None:
        try:
            rhs = OOp("mk", (OOp("mk", (OVar("x"), OVar("hx"),)),))
            results.append((rhs, "Mathlib: ArchimedeanClass_ofArchimedean_stdPart"))
        except Exception:
            pass
    return results


def _r0380_toDual_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toDual_ofNat
    # (toDual (ofNat(n) : R)) = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toDual", 1)
    if args is not None:
        try:
            rhs = OVar("ofNat_n")
            results.append((rhs, "Mathlib: toDual_ofNat"))
        except Exception:
            pass
    return results


def _r0381_ofDual_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofDual_ofNat
    # (ofDual (ofNat(n) : Rᵒᵈ)) = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofDual", 1)
    if args is not None:
        try:
            rhs = OVar("ofNat_n")
            results.append((rhs, "Mathlib: ofDual_ofNat"))
        except Exception:
            pass
    return results


def _r0382_ofDual_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofDual_intCast
    # (ofDual n : R) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofDual", 3)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ofDual_intCast"))
        except Exception:
            pass
    return results


def _r0383_top_mul_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithTop.top_mul_top
    # (⊤ * ⊤ : WithTop α) = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: WithTop_top_mul_top"))
        except Exception:
            pass
    return results


def _r0384_mul_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithTop.mul_def
    # a * b = if a = 0 ∨ b = 0 then 0 else WithTop.map₂ (· * ·) a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (args[0],)), OOp("==", (OOp("or", (OLit(0), args[1])), OOp("_0", (OVar("then"), OLit(0), OVar("else"), OVar("WithTop_map_2"), OOp("*", (OVar("_unknown"), OVar("_unknown"))), args[0], args[1],))))))
            results.append((rhs, "Mathlib: WithTop_mul_def"))
        except Exception:
            pass
    return results


def _r0385_top_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: top_pow
    # ∀ {n : ℕ}, n ≠ 0 → (⊤ : WithTop α) ^ n = ⊤ | _ + 1, _ => rfl  @[simp] lemma pow_eq_top_iff : x ^ n = ⊤ ↔ x = ⊤ ∧ n ≠ 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("+", (OOp("top", (OVar("pipe"), OVar("_unknown"),)), OOp("**", (OOp("_1", (OVar("_unknown"), OVar("eq_gt"), OVar("rfl_at_simp"), OVar("lemma"), OVar("pow_eq_top_iff"), OVar("colon"), OVar("x"),)), args[1])))), OOp("==", (OOp("iff", (OVar("top"), OVar("x"))), OOp("!=", (OOp("and", (OVar("top"), args[1])), OLit(0)))))))
            results.append((rhs, "Mathlib: top_pow"))
        except Exception:
            pass
    return results


def _r0386_pow_eq_top_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_eq_top_iff
    # x ^ n = ⊤ ↔ x = ⊤ ∧ n ≠ 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("top"), args[0])), OOp("!=", (OOp("and", (OVar("top"), args[1])), OLit(0)))))
            results.append((rhs, "Mathlib: pow_eq_top_iff"))
        except Exception:
            pass
    return results


def _r0387_pow_ne_top_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_ne_top_iff
    # x ^ n ≠ ⊤ ↔ x ≠ ⊤ ∨ n = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: pow_ne_top_iff"))
        except Exception:
            pass
    return results


def _r0388_eq_top_of_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: eq_top_of_pow
    # x = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: eq_top_of_pow"))
    except Exception:
        pass
    return results


def _r0389_bot_mul_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithBot.bot_mul_bot
    # (⊥ * ⊥ : WithBot α) = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: WithBot_bot_mul_bot"))
        except Exception:
            pass
    return results


def _r0390_mul_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithBot.mul_def
    # a * b = if a = 0 ∨ b = 0 then 0 else WithBot.map₂ (· * ·) a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (args[0],)), OOp("==", (OOp("or", (OLit(0), args[1])), OOp("_0", (OVar("then"), OLit(0), OVar("else"), OVar("WithBot_map_2"), OOp("*", (OVar("_unknown"), OVar("_unknown"))), args[0], args[1],))))))
            results.append((rhs, "Mathlib: WithBot_mul_def"))
        except Exception:
            pass
    return results


def _r0391_round_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: round_one
    # round (1 : α) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "round", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: round_one"))
        except Exception:
            pass
    return results


def _r0392_round_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: round_natCast
    # round (n : α) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "round", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: round_natCast"))
        except Exception:
            pass
    return results


def _r0393_round_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: round_ofNat
    # round (ofNat(n) : α) = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "round", 1)
    if args is not None:
        try:
            rhs = OVar("ofNat_n")
            results.append((rhs, "Mathlib: round_ofNat"))
        except Exception:
            pass
    return results


def _r0394_round_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: round_intCast
    # round (n : α) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "round", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: round_intCast"))
        except Exception:
            pass
    return results


def _r0395_round_eq_half_ceil_two_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: round_eq_half_ceil_two_mul
    # round x = ⌈2 * x⌉ / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "round", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("_2"), OOp("//", (args[0], OLit(2)))))
            results.append((rhs, "Mathlib: round_eq_half_ceil_two_mul"))
        except Exception:
            pass
    return results


def _r0396_round_sub_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: round_sub_intCast
    # round (x - y) = round x - y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "round", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("round", (OVar("x"),)), OVar("y")))
            results.append((rhs, "Mathlib: round_sub_intCast"))
        except Exception:
            pass
    return results


def _r0397_round_add_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: round_add_natCast
    # round (x + y) = round x + y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "round", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("round", (OVar("x"),)), OVar("y")))
            results.append((rhs, "Mathlib: round_add_natCast"))
        except Exception:
            pass
    return results


def _r0398_round_add_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: round_add_ofNat
    # round (x + ofNat(n)) = round x + ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "round", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("round", (OVar("x"),)), OVar("ofNat_n")))
            results.append((rhs, "Mathlib: round_add_ofNat"))
        except Exception:
            pass
    return results


def _r0399_round_sub_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: round_sub_ofNat
    # round (x - ofNat(n)) = round x - ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "round", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("round", (OVar("x"),)), OVar("ofNat_n")))
            results.append((rhs, "Mathlib: round_sub_ofNat"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_order rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("!=", "*", "**", "+", "-", "//", "<", "<=", "FiniteResidueField_ofArchimedean", "LimZero", "Multiplicative_ofAdd", "OrderDual_ofDual", "WithBot_map", "WithTop_map", "_0", "_0_colon_CauSeq_b_abv", "_0_colon_b", "_1", "_1_colon_CauSeq_b_abv", "_1_colon_WithBot_a_map", "_1_colon_WithBot_a_unbot", "_1_colon_WithBot_a_unbotD", "_1_colon_WithTop_a_map", "_1_colon_WithTop_a_untop", "_1_colon_WithTop_a_untopD", "_1_colon_r_r_r", "_unknown", "a", "a_f", "a_ha_colon_Rge_0", "a_map", "a_minus_b", "abv", "b", "bot", "c_star", "const", "count", "e", "e_1_star_e_2", "einv", "exists", "f", "f_minus_g", "f_plus_g", "f_pow_n", "f_star_g", "finv", "forall", "fract",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_order axioms."""
    if recognizes(term):
        return 0.7
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_order rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_map_one_of_isLeftRegular(term, ctx))
    results.extend(_r0001_map_pow(term, ctx))
    results.extend(_r0002_add_top(term, ctx))
    results.extend(_r0003_add_right_inj_of_ne_top(term, ctx))
    results.extend(_r0004_neg_eq_top(term, ctx))
    results.extend(_r0005_sub_top(term, ctx))
    results.extend(_r0006_sub_right_inj_of_ne_top(term, ctx))
    results.extend(_r0007_add_neg_cancel_iff_ne_top(term, ctx))
    results.extend(_r0008_coe_sub(term, ctx))
    results.extend(_r0009_neg_top(term, ctx))
    results.extend(_r0010_top_sub(term, ctx))
    results.extend(_r0011_sub_top(term, ctx))
    results.extend(_r0012_sub_eq_top_iff(term, ctx))
    results.extend(_r0013_add_apply(term, ctx))
    results.extend(_r0014_const_inj(term, ctx))
    results.extend(_r0015_coe_one(term, ctx))
    results.extend(_r0016_zero_apply(term, ctx))
    results.extend(_r0017_one_apply(term, ctx))
    results.extend(_r0018_const_zero(term, ctx))
    results.extend(_r0019_const_one(term, ctx))
    results.extend(_r0020_const_add(term, ctx))
    results.extend(_r0021_mul_apply(term, ctx))
    results.extend(_r0022_const_mul(term, ctx))
    results.extend(_r0023_neg_apply(term, ctx))
    results.extend(_r0024_const_neg(term, ctx))
    results.extend(_r0025_sub_apply(term, ctx))
    results.extend(_r0026_const_sub(term, ctx))
    results.extend(_r0027_smul_apply(term, ctx))
    results.extend(_r0028_const_smul(term, ctx))
    results.extend(_r0029_pow_apply(term, ctx))
    results.extend(_r0030_const_pow(term, ctx))
    results.extend(_r0031_inv_apply(term, ctx))
    results.extend(_r0032_coe_inf(term, ctx))
    results.extend(_r0033_sup_limZero(term, ctx))
    results.extend(_r0034_inf_idem(term, ctx))
    results.extend(_r0035_sup_comm(term, ctx))
    results.extend(_r0036_mk_eq(term, ctx))
    results.extend(_r0037_ofRat_intCast(term, ctx))
    results.extend(_r0038_ofRat_add(term, ctx))
    results.extend(_r0039_ofRat_ratCast(term, ctx))
    results.extend(_r0040_lim_add(term, ctx))
    results.extend(_r0041_inducedMap_one(term, ctx))
    results.extend(_r0042_inducedOrderRingIso_symm(term, ctx))
    results.extend(_r0043_inducedOrderRingIso_self(term, ctx))
    results.extend(_r0044_abs_div(term, ctx))
    results.extend(_r0045_abs_neg_one_zpow(term, ctx))
    results.extend(_r0046_floorDiv_of_nonpos(term, ctx))
    results.extend(_r0047_floorDiv_zero(term, ctx))
    results.extend(_r0048_zero_floorDiv(term, ctx))
    results.extend(_r0049_ceilDiv_of_nonpos(term, ctx))
    results.extend(_r0050_ceilDiv_zero(term, ctx))
    results.extend(_r0051_zero_ceilDiv(term, ctx))
    results.extend(_r0052_smul_floorDiv(term, ctx))
    results.extend(_r0053_smul_ceilDiv(term, ctx))
    results.extend(_r0054_ceil_top(term, ctx))
    results.extend(_r0055_floor_coe(term, ctx))
    results.extend(_r0056_ceil_coe(term, ctx))
    results.extend(_r0057_floor_eq_top(term, ctx))
    results.extend(_r0058_ceil_eq_top(term, ctx))
    results.extend(_r0059_ceil_natCast(term, ctx))
    results.extend(_r0060_floor_zero(term, ctx))
    results.extend(_r0061_ceil_zero(term, ctx))
    results.extend(_r0062_floor_one(term, ctx))
    results.extend(_r0063_ceil_one(term, ctx))
    results.extend(_r0064_floor_ofNat(term, ctx))
    results.extend(_r0065_ceil_ofNat(term, ctx))
    results.extend(_r0066_ceil_eq_zero(term, ctx))
    results.extend(_r0067_ceil_le_floor_add_one(term, ctx))
    results.extend(_r0068_ceil_toENNReal_add(term, ctx))
    results.extend(_r0069_floor_add_natCast(term, ctx))
    results.extend(_r0070_ceil_add_natCast(term, ctx))
    results.extend(_r0071_floor_natCast_add(term, ctx))
    results.extend(_r0072_ceil_natCast_add(term, ctx))
    results.extend(_r0073_floor_add_one(term, ctx))
    results.extend(_r0074_ceil_add_one(term, ctx))
    results.extend(_r0075_floor_add_ofNat(term, ctx))
    results.extend(_r0076_ceil_add_ofNat(term, ctx))
    results.extend(_r0077_floor_sub_toENNReal(term, ctx))
    results.extend(_r0078_ceil_sub_natCast(term, ctx))
    results.extend(_r0079_floor_sub_one(term, ctx))
    results.extend(_r0080_ceil_sub_one(term, ctx))
    results.extend(_r0081_floor_sub_ofNat(term, ctx))
    results.extend(_r0082_ceil_sub_ofNat(term, ctx))
    results.extend(_r0083_toENNReal_iInf(term, ctx))
    results.extend(_r0084_floor_add_fract(term, ctx))
    results.extend(_r0085_fract_add_floor(term, ctx))
    results.extend(_r0086_self_sub_fract(term, ctx))
    results.extend(_r0087_fract_sub_self(term, ctx))
    results.extend(_r0088_fract_add(term, ctx))
    results.extend(_r0089_fract_add_natCast(term, ctx))
    results.extend(_r0090_fract_add_one(term, ctx))
    results.extend(_r0091_fract_add_ofNat(term, ctx))
    results.extend(_r0092_fract_natCast_add(term, ctx))
    results.extend(_r0093_fract_one_add(term, ctx))
    results.extend(_r0094_fract_ofNat_add(term, ctx))
    results.extend(_r0095_fract_sub_natCast(term, ctx))
    results.extend(_r0096_fract_sub_one(term, ctx))
    results.extend(_r0097_fract_sub_ofNat(term, ctx))
    results.extend(_r0098_fract_one(term, ctx))
    results.extend(_r0099_abs_fract(term, ctx))
    results.extend(_r0100_fract_intCast(term, ctx))
    results.extend(_r0101_fract_ofNat(term, ctx))
    results.extend(_r0102_fract_eq_iff(term, ctx))
    results.extend(_r0103_fract_fract(term, ctx))
    results.extend(_r0104_fract_eq_zero_iff(term, ctx))
    results.extend(_r0105_ceil_eq_on_Ioc(term, ctx))
    results.extend(_r0106_ceil_natCast(term, ctx))
    results.extend(_r0107_ceil_ofNat(term, ctx))
    results.extend(_r0108_ceil_add_intCast(term, ctx))
    results.extend(_r0109_ceil_intCast_add(term, ctx))
    results.extend(_r0110_ceil_add_natCast(term, ctx))
    results.extend(_r0111_ceil_natCast_add(term, ctx))
    results.extend(_r0112_ceil_add_one(term, ctx))
    results.extend(_r0113_ceil_one_add(term, ctx))
    results.extend(_r0114_ceil_add_ofNat(term, ctx))
    results.extend(_r0115_ceil_sub_natCast(term, ctx))
    results.extend(_r0116_ceil_sub_ofNat(term, ctx))
    results.extend(_r0117_ceil_one(term, ctx))
    results.extend(_r0118_ceil_eq_iff(term, ctx))
    results.extend(_r0119_ceil_zero(term, ctx))
    results.extend(_r0120_ceil_one(term, ctx))
    results.extend(_r0121_ceil_ofNat(term, ctx))
    results.extend(_r0122_floor_sub_ofNat(term, ctx))
    results.extend(_r0123_ceil_sub_ofNat(term, ctx))
    results.extend(_r0124_mabs_eq_inv_self(term, ctx))
    results.extend(_r0125_genLTOne_unique(term, ctx))
    results.extend(_r0126_coe_mul(term, ctx))
    results.extend(_r0127_mul_apply(term, ctx))
    results.extend(_r0128_coe_mul(term, ctx))
    results.extend(_r0129_one_apply(term, ctx))
    results.extend(_r0130_mul_apply(term, ctx))
    results.extend(_r0131_one_apply(term, ctx))
    results.extend(_r0132_mul_apply(term, ctx))
    results.extend(_r0133_apply_inv_self(term, ctx))
    results.extend(_r0134_coe_ofLexMulEquiv(term, ctx))
    results.extend(_r0135_symm_toLexMulEquiv(term, ctx))
    results.extend(_r0136_symm_ofLexMulEquiv(term, ctx))
    results.extend(_r0137_toEquiv_toLexMulEquiv(term, ctx))
    results.extend(_r0138_toEquiv_ofLexMulEquiv(term, ctx))
    results.extend(_r0139_dedup_nsmul(term, ctx))
    results.extend(_r0140_count_nsmul(term, ctx))
    results.extend(_r0141_csInf_one(term, ctx))
    results.extend(_r0142_inv_Iic(term, ctx))
    results.extend(_r0143_inv_Ioi(term, ctx))
    results.extend(_r0144_inv_Iio(term, ctx))
    results.extend(_r0145_inv_Icc(term, ctx))
    results.extend(_r0146_inv_Ico(term, ctx))
    results.extend(_r0147_inv_Ioc(term, ctx))
    results.extend(_r0148_inv_Ioo(term, ctx))
    results.extend(_r0149_preimage_const_mul_Ioi(term, ctx))
    results.extend(_r0150_preimage_const_mul_Iic(term, ctx))
    results.extend(_r0151_preimage_const_mul_Iio(term, ctx))
    results.extend(_r0152_preimage_const_mul_Icc(term, ctx))
    results.extend(_r0153_preimage_const_mul_Ico(term, ctx))
    results.extend(_r0154_preimage_const_mul_Ioc(term, ctx))
    results.extend(_r0155_preimage_const_mul_Ioo(term, ctx))
    results.extend(_r0156_preimage_mul_const_Ioi(term, ctx))
    results.extend(_r0157_preimage_mul_const_Iic(term, ctx))
    results.extend(_r0158_preimage_mul_const_Iio(term, ctx))
    results.extend(_r0159_preimage_mul_const_Icc(term, ctx))
    results.extend(_r0160_preimage_mul_const_Ico(term, ctx))
    results.extend(_r0161_preimage_mul_const_Ioc(term, ctx))
    results.extend(_r0162_preimage_mul_const_Ioo(term, ctx))
    results.extend(_r0163_preimage_div_const_Ioi(term, ctx))
    results.extend(_r0164_preimage_div_const_Iic(term, ctx))
    results.extend(_r0165_preimage_div_const_Iio(term, ctx))
    results.extend(_r0166_preimage_div_const_Icc(term, ctx))
    results.extend(_r0167_preimage_div_const_Ico(term, ctx))
    results.extend(_r0168_preimage_div_const_Ioc(term, ctx))
    results.extend(_r0169_preimage_div_const_Ioo(term, ctx))
    results.extend(_r0170_preimage_const_div_Iic(term, ctx))
    results.extend(_r0171_preimage_const_div_Ioi(term, ctx))
    results.extend(_r0172_preimage_const_div_Iio(term, ctx))
    results.extend(_r0173_preimage_const_div_Icc(term, ctx))
    results.extend(_r0174_preimage_const_div_Ico(term, ctx))
    results.extend(_r0175_preimage_const_div_Ioc(term, ctx))
    results.extend(_r0176_preimage_const_div_Ioo(term, ctx))
    results.extend(_r0177_image_div_const_Iic(term, ctx))
    results.extend(_r0178_image_div_const_Ioi(term, ctx))
    results.extend(_r0179_image_div_const_Iio(term, ctx))
    results.extend(_r0180_image_div_const_Icc(term, ctx))
    results.extend(_r0181_image_div_const_Ico(term, ctx))
    results.extend(_r0182_image_div_const_Ioc(term, ctx))
    results.extend(_r0183_image_div_const_Ioo(term, ctx))
    results.extend(_r0184_preimage_add_const_uIcc(term, ctx))
    results.extend(_r0185_preimage_sub_const_uIcc(term, ctx))
    results.extend(_r0186_preimage_const_sub_uIcc(term, ctx))
    results.extend(_r0187_image_neg_uIcc(term, ctx))
    results.extend(_r0188_preimage_mul_const_Ici_0(term, ctx))
    results.extend(_r0189_preimage_mul_const_Ioi_0(term, ctx))
    results.extend(_r0190_preimage_mul_const_Iio_0(term, ctx))
    results.extend(_r0191_preimage_mul_const_Icc_0(term, ctx))
    results.extend(_r0192_preimage_mul_const_Ioo_0(term, ctx))
    results.extend(_r0193_preimage_mul_const_Ioc_0(term, ctx))
    results.extend(_r0194_preimage_mul_const_Ico_0(term, ctx))
    results.extend(_r0195_preimage_const_mul_Ici_0(term, ctx))
    results.extend(_r0196_preimage_const_mul_Icc_0(term, ctx))
    results.extend(_r0197_preimage_const_mul_Iio_0(term, ctx))
    results.extend(_r0198_preimage_const_mul_Ioi_0(term, ctx))
    results.extend(_r0199_preimage_const_mul_Ioo_0(term, ctx))
    results.extend(_r0200_preimage_const_mul_Ioc_0(term, ctx))
    results.extend(_r0201_preimage_const_mul_Ico_0(term, ctx))
    results.extend(_r0202_preimage_mul_const_Ioc_of_neg(term, ctx))
    results.extend(_r0203_preimage_const_mul_Iio_of_neg(term, ctx))
    results.extend(_r0204_image_div_const_uIcc(term, ctx))
    results.extend(_r0205_leOnePart_one(term, ctx))
    results.extend(_r0206_oneLePart_eq_one(term, ctx))
    results.extend(_r0207_oneLePart_inv(term, ctx))
    results.extend(_r0208_leOnePart_inv(term, ctx))
    results.extend(_r0209_oneLePart_max(term, ctx))
    results.extend(_r0210_leOnePart_eq_one(term, ctx))
    results.extend(_r0211_oneLePart_of_one_lt_oneLePart(term, ctx))
    results.extend(_r0212_leOnePart_apply(term, ctx))
    results.extend(_r0213_oneLePart_def(term, ctx))
    results.extend(_r0214_leOnePart_def(term, ctx))
    results.extend(_r0215_ofDual_one(term, ctx))
    results.extend(_r0216_toDual_eq_one(term, ctx))
    results.extend(_r0217_ofDual_eq_one(term, ctx))
    results.extend(_r0218_toDual_mul(term, ctx))
    results.extend(_r0219_ofDual_mul(term, ctx))
    results.extend(_r0220_toDual_inv(term, ctx))
    results.extend(_r0221_ofDual_inv(term, ctx))
    results.extend(_r0222_toDual_div(term, ctx))
    results.extend(_r0223_ofDual_div(term, ctx))
    results.extend(_r0224_toDual_pow(term, ctx))
    results.extend(_r0225_ofDual_pow(term, ctx))
    results.extend(_r0226_pow_toDual(term, ctx))
    results.extend(_r0227_pow_ofDual(term, ctx))
    results.extend(_r0228_toLex_eq_one(term, ctx))
    results.extend(_r0229_ofLex_one(term, ctx))
    results.extend(_r0230_ofLex_eq_one(term, ctx))
    results.extend(_r0231_toLex_mul(term, ctx))
    results.extend(_r0232_ofLex_mul(term, ctx))
    results.extend(_r0233_toLex_inv(term, ctx))
    results.extend(_r0234_ofLex_inv(term, ctx))
    results.extend(_r0235_toLex_div(term, ctx))
    results.extend(_r0236_ofLex_div(term, ctx))
    results.extend(_r0237_toLex_pow(term, ctx))
    results.extend(_r0238_ofLex_pow(term, ctx))
    results.extend(_r0239_pow_toLex(term, ctx))
    results.extend(_r0240_pow_ofLex(term, ctx))
    results.extend(_r0241_toColex_eq_one(term, ctx))
    results.extend(_r0242_ofColex_one(term, ctx))
    results.extend(_r0243_ofColex_eq_one(term, ctx))
    results.extend(_r0244_toColex_mul(term, ctx))
    results.extend(_r0245_ofColex_mul(term, ctx))
    results.extend(_r0246_toColex_inv(term, ctx))
    results.extend(_r0247_ofColex_inv(term, ctx))
    results.extend(_r0248_toColex_div(term, ctx))
    results.extend(_r0249_ofColex_div(term, ctx))
    results.extend(_r0250_toColex_pow(term, ctx))
    results.extend(_r0251_ofColex_pow(term, ctx))
    results.extend(_r0252_pow_toColex(term, ctx))
    results.extend(_r0253_pow_ofColex(term, ctx))
    results.extend(_r0254_mabs_div_comm(term, ctx))
    results.extend(_r0255_mabs_ite(term, ctx))
    results.extend(_r0256_mabs_le_one(term, ctx))
    results.extend(_r0257_abs_def(term, ctx))
    results.extend(_r0258_le_zero_iff(term, ctx))
    results.extend(_r0259_ofDual_toAdd_eq_top_iff(term, ctx))
    results.extend(_r0260_ofAdd_bot(term, ctx))
    results.extend(_r0261_nonpos_iff_eq_zero(term, ctx))
    results.extend(_r0262_coe_le_iff(term, ctx))
    results.extend(_r0263_le_coe_iff(term, ctx))
    results.extend(_r0264_lt_iff_exists_coe(term, ctx))
    results.extend(_r0265_lt_coe_iff(term, ctx))
    results.extend(_r0266_pow_nonneg(term, ctx))
    results.extend(_r0267_zero_pow_le_one(term, ctx))
    results.extend(_r0268_pow_pos(term, ctx))
    results.extend(_r0269_pow_lt_pow_left_0(term, ctx))
    results.extend(_r0270_zpow_eq_one_iff_right_0(term, ctx))
    results.extend(_r0271_mul_apply(term, ctx))
    results.extend(_r0272_mul_comp(term, ctx))
    results.extend(_r0273_toOrderHom_eq_coe(term, ctx))
    results.extend(_r0274_mul_apply(term, ctx))
    results.extend(_r0275_mul_comp(term, ctx))
    results.extend(_r0276_fst_one(term, ctx))
    results.extend(_r0277_pure_one(term, ctx))
    results.extend(_r0278_fst_mul(term, ctx))
    results.extend(_r0279_pure_mul_pure(term, ctx))
    results.extend(_r0280_fst_pow(term, ctx))
    results.extend(_r0281_snd_sub(term, ctx))
    results.extend(_r0282_coe_sub_interval(term, ctx))
    results.extend(_r0283_snd_div(term, ctx))
    results.extend(_r0284_coe_div_interval(term, ctx))
    results.extend(_r0285_snd_inv(term, ctx))
    results.extend(_r0286_coe_inv_interval(term, ctx))
    results.extend(_r0287_length_neg(term, ctx))
    results.extend(_r0288_length_add(term, ctx))
    results.extend(_r0289_length_sub(term, ctx))
    results.extend(_r0290_length_sum(term, ctx))
    results.extend(_r0291_kstar_one(term, ctx))
    results.extend(_r0292_kstar_mul_kstar(term, ctx))
    results.extend(_r0293_kstar_eq_self(term, ctx))
    results.extend(_r0294_pow_le_kstar(term, ctx))
    results.extend(_r0295_toAddSubgroup_closedBall(term, ctx))
    results.extend(_r0296_coe_ofLexLinearEquiv(term, ctx))
    results.extend(_r0297_symm_toLexLinearEquiv(term, ctx))
    results.extend(_r0298_symm_ofLexLinearEquiv(term, ctx))
    results.extend(_r0299_upperBounds_smul_of_pos(term, ctx))
    results.extend(_r0300_upperBounds_smul_of_neg(term, ctx))
    results.extend(_r0301_le_iff_exists_mul(term, ctx))
    results.extend(_r0302_orderAddMonoidHom_apply(term, ctx))
    results.extend(_r0303_toMulBot_coe(term, ctx))
    results.extend(_r0304_toMulBot_coe_ofAdd(term, ctx))
    results.extend(_r0305_max_mul_min(term, ctx))
    results.extend(_r0306_toMul_top(term, ctx))
    results.extend(_r0307_ofMul_eq_top(term, ctx))
    results.extend(_r0308_toMul_eq_top(term, ctx))
    results.extend(_r0309_toMul_bot(term, ctx))
    results.extend(_r0310_ofMul_eq_bot(term, ctx))
    results.extend(_r0311_toMul_eq_bot(term, ctx))
    results.extend(_r0312_toAdd_top(term, ctx))
    results.extend(_r0313_ofAdd_eq_top(term, ctx))
    results.extend(_r0314_toAdd_eq_top(term, ctx))
    results.extend(_r0315_toAdd_bot(term, ctx))
    results.extend(_r0316_ofAdd_eq_bot(term, ctx))
    results.extend(_r0317_toAdd_eq_bot(term, ctx))
    results.extend(_r0318_coe_eq_one(term, ctx))
    results.extend(_r0319_untop_one(term, ctx))
    results.extend(_r0320_untopD_one(term, ctx))
    results.extend(_r0321_map_one(term, ctx))
    results.extend(_r0322_map_eq_one_iff(term, ctx))
    results.extend(_r0323_top_add(term, ctx))
    results.extend(_r0324_add_top(term, ctx))
    results.extend(_r0325_add_eq_top(term, ctx))
    results.extend(_r0326_add_eq_coe(term, ctx))
    results.extend(_r0327_coe_ofNat(term, ctx))
    results.extend(_r0328_coe_eq_ofNat(term, ctx))
    results.extend(_r0329_ofNat_eq_coe(term, ctx))
    results.extend(_r0330_map_ofNat(term, ctx))
    results.extend(_r0331_map_natCast(term, ctx))
    results.extend(_r0332_map_eq_ofNat_iff(term, ctx))
    results.extend(_r0333_coe_eq_one(term, ctx))
    results.extend(_r0334_one_eq_coe(term, ctx))
    results.extend(_r0335_unbot_one(term, ctx))
    results.extend(_r0336_unbotD_one(term, ctx))
    results.extend(_r0337_map_one(term, ctx))
    results.extend(_r0338_map_eq_one_iff(term, ctx))
    results.extend(_r0339_bot_add(term, ctx))
    results.extend(_r0340_add_bot(term, ctx))
    results.extend(_r0341_add_eq_bot(term, ctx))
    results.extend(_r0342_add_eq_coe(term, ctx))
    results.extend(_r0343_coe_nsmul(term, ctx))
    results.extend(_r0344_coe_ofNat(term, ctx))
    results.extend(_r0345_coe_eq_ofNat(term, ctx))
    results.extend(_r0346_ofNat_eq_coe(term, ctx))
    results.extend(_r0347_map_ofNat(term, ctx))
    results.extend(_r0348_map_natCast(term, ctx))
    results.extend(_r0349_map_eq_ofNat_iff(term, ctx))
    results.extend(_r0350_mk_eq_zero(term, ctx))
    results.extend(_r0351_mk_eq_one(term, ctx))
    results.extend(_r0352_mk_natCast(term, ctx))
    results.extend(_r0353_toNonneg_of_nonneg(term, ctx))
    results.extend(_r0354_toNonneg_coe(term, ctx))
    results.extend(_r0355_inv_mk(term, ctx))
    results.extend(_r0356_mk_div_mk(term, ctx))
    results.extend(_r0357_mk_nnratCast(term, ctx))
    results.extend(_r0358_coe_nnqsmul(term, ctx))
    results.extend(_r0359_mk_nnqsmul(term, ctx))
    results.extend(_r0360_mk_smul(term, ctx))
    results.extend(_r0361_abs_two(term, ctx))
    results.extend(_r0362_abs_mul(term, ctx))
    results.extend(_r0363_pow_abs(term, ctx))
    results.extend(_r0364_abs_mul_self(term, ctx))
    results.extend(_r0365_abs_sq(term, ctx))
    results.extend(_r0366_orderHom_zero(term, ctx))
    results.extend(_r0367_mk_eq_zero_of_archimedean(term, ctx))
    results.extend(_r0368_eq_zero_or_top_of_archimedean(term, ctx))
    results.extend(_r0369_mk_ofNat(term, ctx))
    results.extend(_r0370_mk_ratCast(term, ctx))
    results.extend(_r0371_cast_max(term, ctx))
    results.extend(_r0372_cast_abs(term, ctx))
    results.extend(_r0373_ofLex_intCast(term, ctx))
    results.extend(_r0374_stdPart_one(term, ctx))
    results.extend(_r0375_stdPart_neg(term, ctx))
    results.extend(_r0376_stdPart_natCast(term, ctx))
    results.extend(_r0377_stdPart_ofNat(term, ctx))
    results.extend(_r0378_stdPart_map_real(term, ctx))
    results.extend(_r0379_ofArchimedean_stdPart(term, ctx))
    results.extend(_r0380_toDual_ofNat(term, ctx))
    results.extend(_r0381_ofDual_ofNat(term, ctx))
    results.extend(_r0382_ofDual_intCast(term, ctx))
    results.extend(_r0383_top_mul_top(term, ctx))
    results.extend(_r0384_mul_def(term, ctx))
    results.extend(_r0385_top_pow(term, ctx))
    results.extend(_r0386_pow_eq_top_iff(term, ctx))
    results.extend(_r0387_pow_ne_top_iff(term, ctx))
    results.extend(_r0388_eq_top_of_pow(term, ctx))
    results.extend(_r0389_bot_mul_bot(term, ctx))
    results.extend(_r0390_mul_def(term, ctx))
    results.extend(_r0391_round_one(term, ctx))
    results.extend(_r0392_round_natCast(term, ctx))
    results.extend(_r0393_round_ofNat(term, ctx))
    results.extend(_r0394_round_intCast(term, ctx))
    results.extend(_r0395_round_eq_half_ceil_two_mul(term, ctx))
    results.extend(_r0396_round_sub_intCast(term, ctx))
    results.extend(_r0397_round_add_natCast(term, ctx))
    results.extend(_r0398_round_add_ofNat(term, ctx))
    results.extend(_r0399_round_sub_ofNat(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_order rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("GrpCat_FilteredColimits_colimit_mul_mk_eq", "_unknown", "Empty proposition"),
    ("MonCat_FilteredColimits_colimit_mul_mk_eq", "_unknown", "Empty proposition"),
    ("Infinite_of_smul_set", "a_s_Infinite_to_s_Infinite", "Not an equality or iff proposition"),
    ("AbsoluteValue_coe_mk", "AbsoluteValue_mk_f_h_1_h_2_h_3_colon_R_to_S_eq_f", "Not an equality or iff proposition"),
    ("AbsoluteValue_ext", "_unknown", "Empty proposition"),
    ("AbsoluteValue_nonneg", "_0_le_abv_x", "Not an equality or iff proposition"),
    ("AbsoluteValue_add_le", "abv_x_plus_y_le_abv_x_plus_abv_y", "Not an equality or iff proposition"),
    ("AbsoluteValue_listSum_le", "abv_l_sum_le_l_map_abv_sum", "Not an equality or iff proposition"),
    ("sub_le", "abv_a_minus_c_le_abv_a_minus_b_plus_abv_b_minus_c", "Not an equality or iff proposition"),
    ("apply_nat_le_self", "abv_n_le_n", "Not an equality or iff proposition"),
    ("le_sub", "abv_a_minus_abv_b_le_abv_a_minus_b", "Not an equality or iff proposition"),
    ("le_add", "abv_a_minus_abv_b_le_abv_a_plus_b", "Not an equality or iff proposition"),
    ("sub_le_add", "abv_a_minus_b_le_abv_a_plus_abv_b", "Not an equality or iff proposition"),
    ("abs_abv_sub_le_abv_sub", "abs_abv_a_minus_abv_b_le_abv_a_minus_b", "Not an equality or iff proposition"),
    ("IsNontrivial_exists_abv_gt_one", "exists_x_1_lt_v_x", "Not an equality or iff proposition"),
    ("IsNontrivial_exists_abv_lt_one", "exists_x_ne_0_v_x_lt_1", "Not an equality or iff proposition"),
    ("IsAbsoluteValue_abv_nonneg", "_0_le_abv_x", "Not an equality or iff proposition"),
    ("IsAbsoluteValue_abv_add", "abv_x_plus_y_le_abv_x_plus_abv_y", "Not an equality or iff proposition"),
    ("abv_sub_le", "abv_a_minus_c_le_abv_a_minus_b_plus_abv_b_minus_c", "Not an equality or iff proposition"),
    ("sub_abv_le_abv_sub", "abv_a_minus_abv_b_le_abv_a_minus_b", "Not an equality or iff proposition"),
    ("abs_abv_sub_le_abv_sub", "abs_abv_a_minus_abv_b_le_abv_a_minus_b", "Not an equality or iff proposition"),
    ("abv_one", "_unknown", "Empty proposition"),
    ("AbsoluteValue_IsEuclidean_sub_mod_lt", "abv_a_b_lt_abv_b", "Not an equality or iff proposition"),
    ("abs_isEuclidean", "IsEuclidean_AbsoluteValue_abs_colon_AbsoluteValue", "Not an equality or iff proposition"),
    ("IsAddRegular_of_ne_top", "IsAddRegular_a", "Not an equality or iff proposition"),
    ("add_left_injective_of_ne_top", "Function_Injective_fun_x_x_plus_b", "Not an equality or iff proposition"),
    ("add_right_injective_of_ne_top", "Function_Injective_fun_x_b_plus_x", "Not an equality or iff proposition"),
    ("add_left_strictMono_of_ne_top", "StrictMono_fun_x_x_plus_b", "Not an equality or iff proposition"),
    ("add_right_strictMono_of_ne_top", "StrictMono_fun_x_b_plus_x", "Not an equality or iff proposition"),
    ("LinearOrderedAddCommGroupWithTop_top_ne_zero", "top_colon_a_ne_0", "Not an equality or iff proposition"),
    ("LinearOrderedAddCommGroupWithTop_zero_ne_top", "_0_ne_top_colon_a", "Not an equality or iff proposition"),
    ("LinearOrderedAddCommGroupWithTop_top_pos", "_0_colon_a_lt_top", "Not an equality or iff proposition"),
    ("LinearOrderedAddCommGroupWithTop_sub_left_injective_of_ne_top", "Function_Injective_fun_x_x_minus_b", "Not an equality or iff proposition"),
    ("LinearOrderedAddCommGroupWithTop_sub_right_injective_of_ne_top", "Function_Injective_fun_x_b_minus_x", "Not an equality or iff proposition"),
    ("LinearOrderedAddCommGroupWithTop_sub_left_strictMono_of_ne_top", "StrictMono_fun_x_x_minus_b", "Not an equality or iff proposition"),
    ("LinearOrderedAddCommGroupWithTop_sub_self_nonneg", "_0_le_a_minus_a", "Not an equality or iff proposition"),
    ("IsOrderedSMul_smul_le_smul", "a_c_le_b_d", "Not an equality or iff proposition"),
    ("SMul_smul_lt_smul_of_le_of_lt", "a_c_lt_b_d", "Not an equality or iff proposition"),
    ("SMul_smul_lt_smul_of_lt_of_le", "a_c_lt_b_d", "Not an equality or iff proposition"),
    ("IsOrderedModule_of_algebraMap_mono", "IsOrderedModule_a_b", "Not an equality or iff proposition"),
    ("algebraMap_mono", "Monotone_algebraMap_a_b", "Not an equality or iff proposition"),
    ("algebraMap_nonneg", "_0_le_algebraMap_a_b_a", "Not an equality or iff proposition"),
    ("algebraMap_strictMono", "StrictMono_algebraMap_a_b", "Not an equality or iff proposition"),
    ("algebraMap_pos", "_0_lt_algebraMap_a_b_a", "Not an equality or iff proposition"),
    ("pairwiseDisjoint_piAntidiag_map_addRightEmbedding", "antidiagonal_n_colon_Set_mu_times_mu_PairwiseDisjoint_fun_p_map_addRightEmbed", "Not an equality or iff proposition"),
    ("antidiagonal_congr", "_unknown", "Empty proposition"),
    ("antidiagonal_fst_le", "kl_1_le_n", "Not an equality or iff proposition"),
    ("antidiagonal_snd_le", "kl_2_le_n", "Not an equality or iff proposition"),
    ("existsUnique_zpow_near_of_one_lt", "exists_bang_k_colon_a_pow_k_le_g_and_g_lt_a_pow_k_plus_1", "Not an equality or iff proposition"),
    ("existsUnique_zpow_near_of_one_lt", "_unknown", "Empty proposition"),
    ("existsUnique_div_zpow_mem_Ico", "exists_bang_m_colon_b_slash_a_pow_m_in_Set_Ico_c_c_star_a", "Not an equality or iff proposition"),
    ("existsUnique_mul_zpow_mem_Ico", "exists_bang_m_colon_b_star_a_pow_m_in_Set_Ico_c_c_star_a", "Not an equality or iff proposition"),
    ("existsUnique_add_zpow_mem_Ioc", "exists_bang_m_colon_b_star_a_pow_m_in_Set_Ioc_c_c_star_a", "Not an equality or iff proposition"),
    ("existsUnique_sub_zpow_mem_Ioc", "exists_bang_m_colon_b_slash_a_pow_m_in_Set_Ioc_c_c_star_a", "Not an equality or iff proposition"),
    ("add_one_pow_unbounded_of_pos", "exists_n_colon_x_lt_y_plus_1_pow_n", "Not an equality or iff proposition"),
    ("pow_unbounded_of_one_lt", "exists_n_colon_x_lt_y_pow_n", "Not an equality or iff proposition"),
    ("exists_nat_pow_near", "exists_n_colon_y_pow_n_le_x_and_x_lt_y_pow_n_plus_1", "Not an equality or iff proposition"),
    ("exists_nat_one_div_lt", "exists_n_colon_1_slash_n_plus_1_colon_K_lt_e", "Not an equality or iff proposition"),
    ("exists_mem_Ico_zpow", "exists_n_colon_x_in_Ico_y_pow_n_y_pow_n_plus_1", "Not an equality or iff proposition"),
    ("exists_mem_Ioc_zpow", "exists_n_colon_x_in_Ioc_y_pow_n_y_pow_n_plus_1", "Not an equality or iff proposition"),
    ("exists_pow_lt_of_lt_one", "exists_n_colon_y_pow_n_lt_x", "Not an equality or iff proposition"),
    ("exists_nat_pow_near_of_lt_one", "exists_n_colon_y_pow_n_plus_1_lt_x_and_x_le_y_pow_n", "Not an equality or iff proposition"),
    ("exists_pow_btwn_of_lt_mul", "exists_n_colon_a_lt_c_pow_n_and_c_pow_n_lt_b", "Not an equality or iff proposition"),
    ("exists_zpow_btwn_of_lt_mul", "exists_n_colon_a_lt_c_pow_n_and_c_pow_n_lt_b", "Not an equality or iff proposition"),
    ("exists_rat_gt", "exists_q_colon_x_lt_q", "Not an equality or iff proposition"),
    ("exists_rat_lt", "exists_q_colon_q_colon_K_lt_x", "Not an equality or iff proposition"),
    ("exists_div_btwn", "exists_z_colon_x_lt_z_colon_K_slash_n_and_z_colon_K_slash_n_lt_y", "Not an equality or iff proposition"),
    ("exists_rat_btwn", "exists_q_colon_x_lt_q_and_q_lt_y", "Not an equality or iff proposition"),
    ("exists_rat_mem_uIoo", "exists_q_colon_q_in_Set_uIoo_x_y", "Not an equality or iff proposition"),
    ("exists_pow_btwn", "exists_q_colon_K_0_lt_q_and_x_lt_q_pow_n_and_q_pow_n_lt_y", "Not an equality or iff proposition"),
    ("exists_rat_pow_btwn", "exists_q_colon_0_lt_q_and_x_lt_q_colon_K_pow_n_and_q_colon_K_pow_n_lt_y", "Not an equality or iff proposition"),
    ("le_of_forall_rat_lt_imp_le", "x_le_y", "Not an equality or iff proposition"),
    ("le_of_forall_lt_rat_imp_le", "x_le_y", "Not an equality or iff proposition"),
    ("exists_pos_rat_lt", "exists_q_colon_0_lt_q_and_q_colon_K_lt_x", "Not an equality or iff proposition"),
    ("exists_rat_near", "exists_q_colon_pipe_x_minus_qpipe_lt_e", "Not an equality or iff proposition"),
    ("subsemigroup_strictAnti", "StrictAnti_subsemigroup_M_colon_eq_M", "Not an equality or iff proposition"),
    ("subgroup_strictAntiOn", "StrictAntiOn_subgroup_M_colon_eq_M_Set_Iio_top", "Not an equality or iff proposition"),
    ("subgroup_antitone", "Antitone_subgroup_M_colon_eq_M", "Not an equality or iff proposition"),
    ("ballSubgroup_antitone", "Antitone_ballSubgroup_M_colon_eq_M", "Not an equality or iff proposition"),
    ("exists_lt_pow", "exists_n_colon_b_lt_a_pow_n", "Not an equality or iff proposition"),
    ("exists_pow_lt", "exists_n_colon_a_pow_n_lt_b", "Not an equality or iff proposition"),
    ("exists_nat_ge", "exists_n_colon_x_le_n", "Not an equality or iff proposition"),
    ("exists_nat_gt", "exists_n_colon_x_lt_n", "Not an equality or iff proposition"),
    ("exists_int_ge", "exists_n_colon_x_le_n", "Not an equality or iff proposition"),
    ("exists_int_le", "exists_n_colon_n_le_x", "Not an equality or iff proposition"),
    ("exists_int_gt", "exists_n_colon_x_lt_n", "Not an equality or iff proposition"),
    ("exists_int_lt", "exists_n_colon_n_colon_R_lt_x", "Not an equality or iff proposition"),
    ("le_expect_nonempty_of_subadditive_on_pred", "m_i_in_s_f_i_le_i_in_s_m_f_i", "Not an equality or iff proposition"),
    ("le_expect_nonempty_of_subadditive", "m_i_in_s_f_i_le_i_in_s_m_f_i", "Not an equality or iff proposition"),
    ("le_expect_of_subadditive_on_pred", "m_i_in_s_f_i_le_i_in_s_m_f_i", "Not an equality or iff proposition"),
    ("le_expect_of_subadditive", "m_i_in_s_f_i_le_i_in_s_m_f_i", "Not an equality or iff proposition"),
    ("expect_pos", "_0_lt_i_in_s_f_i", "Not an equality or iff proposition"),
    ("exists_lt_of_lt_expect", "exists_x_in_s_a_lt_f_x", "Not an equality or iff proposition"),
    ("exists_lt_of_expect_lt", "exists_x_in_s_f_x_lt_a", "Not an equality or iff proposition"),
    ("abs_expect_le", "pipe_i_in_s_f_ipipe_le_i_in_s_pipe_f_ipipe", "Not an equality or iff proposition"),
    ("expect_mul_sq_le_sq_mul_sq", "i_in_s_f_i_star_g_i_pow_2_le_i_in_s_f_i_pow_2_star_i_in_s_g_i_pow_2", "Not an equality or iff proposition"),
    ("apply_prod_le_sum_apply", "g_x_in_s_f_x_le_x_in_s_g_f_x", "Not an equality or iff proposition"),
    ("sum_apply_le_apply_prod", "x_in_s_g_f_x_le_g_x_in_s_f_x", "Not an equality or iff proposition"),
    ("max_prod_le", "max_s_prod_f_s_prod_g_le_s_prod_fun_i_max_f_i_g_i", "Not an equality or iff proposition"),
    ("prod_min_le", "s_prod_fun_i_min_f_i_g_i_le_min_s_prod_f_s_prod_g", "Not an equality or iff proposition"),
    ("abs_sum_le_sum_abs", "pipe_i_in_s_f_ipipe_le_i_in_s_pipe_f_ipipe", "Not an equality or iff proposition"),
    ("abs_sum_of_nonneg", "_unknown", "Empty proposition"),
    ("card_le_mul_card_image_of_maps_to", "hash_s_le_n_star_hash_t", "Not an equality or iff proposition"),
    ("card_le_mul_card_image", "hash_s_le_n_star_hash_s_image_f", "Not an equality or iff proposition"),
    ("mul_card_image_le_card_of_maps_to", "n_star_hash_t_le_hash_s", "Not an equality or iff proposition"),
    ("mul_card_image_le_card", "n_star_hash_s_image_f_le_hash_s", "Not an equality or iff proposition"),
    ("sum_card_inter_le", "t_in_B_hash_s_inter_t_le_hash_s_star_n", "Not an equality or iff proposition"),
    ("sum_card_le", "s_in_B_hash_s_le_Fintype_card_a_star_n", "Not an equality or iff proposition"),
    ("le_sum_card_inter", "hash_s_star_n_le_t_in_B_hash_s_inter_t", "Not an equality or iff proposition"),
    ("le_sum_card", "Fintype_card_a_star_n_le_s_in_B_hash_s", "Not an equality or iff proposition"),
    ("card_le_card_biUnion", "hash_s_le_hash_s_biUnion_f", "Not an equality or iff proposition"),
    ("card_le_card_biUnion_add_card_fiber", "hash_s_le_hash_s_biUnion_f_plus_hash_i_in_s_pipe_f_i_eq_empty", "Not an equality or iff proposition"),
    ("card_le_card_biUnion_add_one", "hash_s_le_hash_s_biUnion_f_plus_1", "Not an equality or iff proposition"),
    ("single_le_prod_of_canonicallyOrdered", "f_i_le_j_in_s_f_j", "Not an equality or iff proposition"),
    ("prod_le_prod_of_subset", "_unknown", "Empty proposition"),
    ("prod_mono_set", "_unknown", "Empty proposition"),
    ("prod_le_prod_of_ne_one", "_unknown", "Empty proposition"),
    ("prod_lt_prod", "_unknown", "Empty proposition"),
    ("prod_lt_prod_of_nonempty", "_unknown", "Empty proposition"),
    ("prod_lt_prod_of_subset", "_unknown", "Empty proposition"),
    ("single_lt_prod", "_unknown", "Empty proposition"),
    ("one_lt_prod", "_1_lt_i_in_s_f_i", "Not an equality or iff proposition"),
    ("prod_lt_one", "i_in_s_f_i_lt_1", "Not an equality or iff proposition"),
    ("one_lt_prod", "_unknown", "Empty proposition"),
    ("prod_lt_one", "_unknown", "Empty proposition"),
    ("exists_lt_of_prod_lt", "_unknown", "Empty proposition"),
    ("exists_le_of_prod_le", "_unknown", "Empty proposition"),
    ("exists_one_lt_of_prod_one_of_exists_ne_one", "_unknown", "Empty proposition"),
    ("apply_sup_le_sum", "f_t_sup_s_le_i_in_t_f_s_i", "Not an equality or iff proposition"),
    ("apply_union_le_sum", "f_i_in_t_s_i_le_i_in_t_f_s_i", "Not an equality or iff proposition"),
    ("prod_strictMono", "_unknown", "Empty proposition"),
    ("one_lt_prod", "_1_lt_i_f_i", "Not an equality or iff proposition"),
    ("prod_lt_one", "i_f_i_lt_1", "Not an equality or iff proposition"),
    ("le_prod_of_submultiplicative_on_pred", "f_l_prod_le_l_map_f_prod", "Not an equality or iff proposition"),
    ("le_prod_of_submultiplicative", "f_l_prod_le_l_map_f_prod", "Not an equality or iff proposition"),
    ("le_prod_nonempty_of_submultiplicative_on_pred", "f_l_prod_le_l_map_f_prod", "Not an equality or iff proposition"),
    ("le_prod_nonempty_of_submultiplicative", "f_l_prod_le_l_map_f_prod", "Not an equality or iff proposition"),
    ("sum_le_foldr_max", "f_l_sum_le_l_map_f_foldr_max_0", "Not an equality or iff proposition"),
    ("single_le_prod", "forall_x_in_l_x_le_l_prod", "Not an equality or iff proposition"),
    ("apply_prod_le_sum_map", "f_l_prod_le_l_map_f_sum", "Not an equality or iff proposition"),
    ("sum_map_le_apply_prod", "l_map_f_sum_le_f_l_prod", "Not an equality or iff proposition"),
    ("le_prod_of_submultiplicative_on_pred", "f_s_prod_le_s_map_f_prod", "Not an equality or iff proposition"),
    ("le_prod_of_submultiplicative", "f_s_prod_le_s_map_f_prod", "Not an equality or iff proposition"),
    ("le_prod_nonempty_of_submultiplicative_on_pred", "f_s_prod_le_s_map_f_prod", "Not an equality or iff proposition"),
    ("le_prod_nonempty_of_submultiplicative", "f_s_prod_le_s_map_f_prod", "Not an equality or iff proposition"),
    ("prod_lt_prod", "_unknown", "Empty proposition"),
    ("prod_lt_prod_of_nonempty", "_unknown", "Empty proposition"),
    ("le_prod_of_mem", "a_le_m_prod", "Not an equality or iff proposition"),
    ("max_le_of_forall_le", "l_fold_max_bot_le_n", "Not an equality or iff proposition"),
    ("max_prod_le", "max_s_map_f_prod_s_map_g_prod_le_s_map_fun_i_max_f_i_g_i_prod", "Not an equality or iff proposition"),
    ("prod_min_le", "s_map_fun_i_min_f_i_g_i_prod_le_min_s_map_f_prod_s_map_g_prod", "Not an equality or iff proposition"),
    ("abs_sum_le_sum_abs", "pipe_s_sumpipe_le_s_map_abs_sum", "Not an equality or iff proposition"),
    ("apply_prod_le_sum_map", "f_m_prod_le_m_map_f_sum", "Not an equality or iff proposition"),
    ("sum_map_le_apply_prod", "m_map_f_sum_le_f_m_prod", "Not an equality or iff proposition"),
    ("prod_pos", "_0_lt_i_in_s_f_i", "Not an equality or iff proposition"),
    ("prod_lt_prod", "i_in_s_f_i_lt_i_in_s_g_i", "Not an equality or iff proposition"),
    ("prod_lt_prod_of_nonempty", "i_in_s_f_i_lt_i_in_s_g_i", "Not an equality or iff proposition"),
    ("prod_add_prod_le", "i_in_s_g_i_plus_i_in_s_h_i_le_i_in_s_f_i", "Not an equality or iff proposition"),
    ("le_prod_of_submultiplicative_on_pred_of_nonneg", "f_i_in_s_g_i_le_i_in_s_f_g_i", "Not an equality or iff proposition"),
    ("le_prod_of_submultiplicative_of_nonneg", "f_i_in_s_g_i_le_i_in_s_f_g_i", "Not an equality or iff proposition"),
    ("prod_add_prod_le", "_unknown", "Empty proposition"),
    ("sum_sq_le_sum_mul_sum_of_sq_eq_mul", "i_in_s_r_i_pow_2_le_i_in_s_f_i_star_i_in_s_g_i", "Not an equality or iff proposition"),
    ("sum_mul_sq_le_sq_mul_sq", "i_in_s_f_i_star_g_i_pow_2_le_i_in_s_f_i_pow_2_star_i_in_s_g_i_pow_2", "Not an equality or iff proposition"),
    ("sq_sum_div_le_sum_sq_div", "i_in_s_f_i_pow_2_slash_i_in_s_g_i_le_i_in_s_f_i_pow_2_slash_g_i", "Not an equality or iff proposition"),
    ("AbsoluteValue_sum_le", "abv_i_in_s_f_i_le_i_in_s_abv_f_i", "Not an equality or iff proposition"),
    ("IsAbsoluteValue_abv_sum", "abv_i_in_s_f_i_le_i_in_s_abv_f_i", "Not an equality or iff proposition"),
    ("rat_add_continuous_lemma", "exists_d_gt_0_forall_a_1_a_2_b_1_b_2_colon_b_abv_a_1_minus_b_1_lt_d_to_abv_a_2_minus_b_2_lt_d_to_abv", "Not an equality or iff proposition"),
    ("rat_mul_continuous_lemma", "exists_d_gt_0_forall_a_1_a_2_b_1_b_2_colon_b_abv_a_1_lt_K_1_to_abv_b_2_lt_K_2_to_abv_a_1_minus_b_1_lt_d_to", "Not an equality or iff proposition"),
    ("rat_inv_continuous_lemma", "exists_d_gt_0_forall_a_b_colon_b_K_le_abv_a_to_K_le_abv_b_to_abv_a_minus_b_lt_d_to_abv_ainv_minus_binv", "Not an equality or iff proposition"),
    ("IsCauSeq_cauchy_2", "exists_i_forall_j_ge_i_forall_k_ge_i_abv_f_j_minus_f_k_lt_e", "Not an equality or iff proposition"),
    ("IsCauSeq_cauchy_3", "exists_i_forall_j_ge_i_forall_k_ge_j_abv_f_k_minus_f_j_lt_e", "Not an equality or iff proposition"),
    ("IsCauSeq_bounded", "exists_r_forall_i_abv_f_i_lt_r", "Not an equality or iff proposition"),
    ("IsCauSeq_bounded", "_unknown", "Empty proposition"),
    ("IsCauSeq_const", "IsCauSeq_abv_fun_x", "Not an equality or iff proposition"),
    ("IsCauSeq_add", "IsCauSeq_abv_f_plus_g", "Not an equality or iff proposition"),
    ("IsCauSeq_mul", "IsCauSeq_abv_f_star_g", "Not an equality or iff proposition"),
    ("CauSeq_isCauSeq", "IsCauSeq_abv_f", "Not an equality or iff proposition"),
    ("CauSeq_cauchy", "forall_e_0_lt_e_to_exists_i_forall_j_ge_i_abv_f_j_minus_f_i_lt_e", "Not an equality or iff proposition"),
    ("CauSeq_cauchy_2", "_0_lt_e_to_exists_i_forall_j_ge_i_forall_k_ge_i_abv_f_j_minus_f_k_lt_e", "Not an equality or iff proposition"),
    ("CauSeq_cauchy_3", "_0_lt_e_to_exists_i_forall_j_ge_i_forall_k_ge_j_abv_f_k_minus_f_j_lt_e", "Not an equality or iff proposition"),
    ("CauSeq_bounded", "exists_r_forall_i_abv_f_i_lt_r", "Not an equality or iff proposition"),
    ("CauSeq_bounded", "_unknown", "Empty proposition"),
    ("CauSeq_coe_const", "const_x_colon_to_b_eq_Function_const_x", "Not an equality or iff proposition"),
    ("CauSeq_const_apply", "const_x_colon_to_b_i_eq_x", "Not an equality or iff proposition"),
    ("neg_limZero", "LimZero_minus_f", "Not an equality or iff proposition"),
    ("sub_limZero", "LimZero_f_minus_g", "Not an equality or iff proposition"),
    ("limZero_sub_rev", "LimZero_g_minus_f", "Not an equality or iff proposition"),
    ("add_equiv_add", "f1_plus_g1_f2_plus_g2", "Not an equality or iff proposition"),
    ("neg_equiv_neg", "minus_f_minus_g", "Not an equality or iff proposition"),
    ("sub_equiv_sub", "f1_minus_g1_f2_minus_g2", "Not an equality or iff proposition"),
    ("equiv_def_3", "exists_i_forall_j_ge_i_forall_k_ge_j_abv_f_k_minus_g_j_lt_e", "Not an equality or iff proposition"),
    ("abv_pos_of_not_limZero", "exists_K_gt_0_exists_i_forall_j_ge_i_K_le_abv_f_j", "Not an equality or iff proposition"),
    ("not_limZero_of_not_congr_zero", "not_LimZero_f", "Not an equality or iff proposition"),
    ("mul_equiv_zero", "g_star_f_0", "Not an equality or iff proposition"),
    ("mul_equiv_zero", "_unknown", "Empty proposition"),
    ("mul_not_equiv_zero", "not_f_star_g_0", "Not an equality or iff proposition"),
    ("mul_equiv_mul", "f1_star_g1_f2_star_g2", "Not an equality or iff proposition"),
    ("smul_equiv_smul", "c_f1_c_f2", "Not an equality or iff proposition"),
    ("pow_equiv_pow", "f1_pow_n_f2_pow_n", "Not an equality or iff proposition"),
    ("one_not_equiv_zero", "not_const_abv_1_const_abv_0", "Not an equality or iff proposition"),
]
