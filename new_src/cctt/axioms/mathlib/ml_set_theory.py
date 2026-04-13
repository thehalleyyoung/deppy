"""Mathlib: Set Theory — auto-generated from Mathlib4.

Contains 400 rewrite rules derived from Mathlib theorems.
Plus 310 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_set_theory"
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

def _r0000_cantorFunctionAux_false(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.cantorFunctionAux_false
    # cantorFunctionAux c f n = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cantorFunctionAux", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Cardinal_cantorFunctionAux_false"))
        except Exception:
            pass
    return results


def _r0001_ord_preAleph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ord_preAleph
    # (preAleph o).ord = preOmega o
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("preAleph_o_ord")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("preOmega", (OVar("o"),))
            results.append((rhs, "Mathlib: Cardinal_ord_preAleph"))
    except Exception:
        pass
    return results


def _r0002_type_lt_cardinal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.type_lt_cardinal
    # typeLT Cardinal = Ordinal.univ.{u, u + 1}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "typeLT", 1)
    if args is not None:
        try:
            rhs = OVar("Ordinal_univ_u_u_plus_1")
            results.append((rhs, "Mathlib: Ordinal_type_lt_cardinal"))
        except Exception:
            pass
    return results


def _r0003_succ_preAleph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.succ_preAleph
    # succ (preAleph o) = preAleph (o + 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 1)
    if args is not None:
        try:
            rhs = OOp("preAleph", (OOp("+", (OVar("o"), OLit(1))),))
            results.append((rhs, "Mathlib: Cardinal_succ_preAleph"))
        except Exception:
            pass
    return results


def _r0004_preAleph_add_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.preAleph_add_one
    # preAleph (o + 1) = succ (preAleph o)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preAleph", 1)
    if args is not None:
        try:
            rhs = OOp("succ", (OOp("preAleph", (OVar("o"),)),))
            results.append((rhs, "Mathlib: Cardinal_preAleph_add_one"))
        except Exception:
            pass
    return results


def _r0005_preAleph_omega0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.preAleph_omega0
    # preAleph ω = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preAleph", 1)
    if args is not None:
        try:
            rhs = OVar("_0")
            results.append((rhs, "Mathlib: Cardinal_preAleph_omega0"))
        except Exception:
            pass
    return results


def _r0006_ord_aleph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ord_aleph
    # (ℵ_ o).ord = ω_ o
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("o_ord")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("omega", (OVar("o"),))
            results.append((rhs, "Mathlib: Cardinal_ord_aleph"))
    except Exception:
        pass
    return results


def _r0007_aleph_add_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph_add_one
    # ℵ_ (o + 1) = succ (ℵ_ o)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OOp("succ", (OOp("_unknown", (OVar("o"),)),))
            results.append((rhs, "Mathlib: Cardinal_aleph_add_one"))
        except Exception:
            pass
    return results


def _r0008_lift_aleph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_aleph
    # lift.{v} (aleph o) = aleph (Ordinal.lift.{v} o)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("aleph", (OOp("Ordinal_lift_v", (OVar("o"),)),))
            results.append((rhs, "Mathlib: Cardinal_lift_aleph"))
        except Exception:
            pass
    return results


def _r0009_aleph_toENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph_toENat
    # toENat (ℵ_ o) = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toENat", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Cardinal_aleph_toENat"))
        except Exception:
            pass
    return results


def _r0010_preBeth_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.preBeth_inj
    # preBeth o₁ = preBeth o₂ ↔ o₁ = o₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preBeth", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("preBeth", (OVar("o_2"),)), args[0])), OVar("o_2")))
            results.append((rhs, "Mathlib: Cardinal_preBeth_inj"))
        except Exception:
            pass
    return results


def _r0011_preBeth_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.preBeth_zero
    # preBeth 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preBeth", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Cardinal_preBeth_zero"))
        except Exception:
            pass
    return results


def _r0012_preBeth_omega(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.preBeth_omega
    # preBeth ω = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preBeth", 1)
    if args is not None:
        try:
            rhs = OVar("_0")
            results.append((rhs, "Mathlib: Cardinal_preBeth_omega"))
        except Exception:
            pass
    return results


def _r0013_beth_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.beth_zero
    # ℶ_ 0 = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OVar("_0")
            results.append((rhs, "Mathlib: Cardinal_beth_zero"))
        except Exception:
            pass
    return results


def _r0014_beth_add_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.beth_add_one
    # ℶ_ (o + 1) = 2 ^ ℶ_ o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OLit(2), OOp("_unknown", (OVar("o"),))))
            results.append((rhs, "Mathlib: Cardinal_beth_add_one"))
        except Exception:
            pass
    return results


def _r0015_aleph_natCast_eq_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph_natCast_eq_lift
    # ℵ_ n = lift.{v} c ↔ ℵ_ n = c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("lift_v", (OVar("c"),)), OOp("_unknown", (args[0],)))), OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_aleph_natCast_eq_lift"))
        except Exception:
            pass
    return results


def _r0016_lift_eq_aleph_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_eq_aleph_natCast
    # lift.{v} c = ℵ_ n ↔ c = ℵ_ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("_unknown", (OVar("n"),)), args[0])), OOp("_unknown", (OVar("n"),))))
            results.append((rhs, "Mathlib: Cardinal_lift_eq_aleph_natCast"))
        except Exception:
            pass
    return results


def _r0017_aleph_ofNat_eq_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph_ofNat_eq_lift
    # ℵ_ ofNat(n) = lift.{v} c ↔ ℵ_ ofNat(n) = c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("lift_v", (OVar("c"),)), OOp("_unknown", (args[0],)))), OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_aleph_ofNat_eq_lift"))
        except Exception:
            pass
    return results


def _r0018_lift_eq_aleph_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_eq_aleph_ofNat
    # lift.{v} c = ℵ_ ofNat(n) ↔ c = ℵ_ ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("_unknown", (OVar("ofNat_n"),)), args[0])), OOp("_unknown", (OVar("ofNat_n"),))))
            results.append((rhs, "Mathlib: Cardinal_lift_eq_aleph_ofNat"))
        except Exception:
            pass
    return results


def _r0019_beth_natCast_eq_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.beth_natCast_eq_lift
    # ℶ_ n = lift.{v} c ↔ ℶ_ n = c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("lift_v", (OVar("c"),)), OOp("_unknown", (args[0],)))), OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_beth_natCast_eq_lift"))
        except Exception:
            pass
    return results


def _r0020_lift_eq_beth_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_eq_beth_natCast
    # lift.{v} c = ℶ_ n ↔ c = ℶ_ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("_unknown", (OVar("n"),)), args[0])), OOp("_unknown", (OVar("n"),))))
            results.append((rhs, "Mathlib: Cardinal_lift_eq_beth_natCast"))
        except Exception:
            pass
    return results


def _r0021_beth_ofNat_eq_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.beth_ofNat_eq_lift
    # ℶ_ ofNat(n) = lift.{v} c ↔ ℶ_ ofNat(n) = c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("lift_v", (OVar("c"),)), OOp("_unknown", (args[0],)))), OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_beth_ofNat_eq_lift"))
        except Exception:
            pass
    return results


def _r0022_lift_eq_beth_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_eq_beth_ofNat
    # lift.{v} c = ℶ_ ofNat(n) ↔ c = ℶ_ ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("_unknown", (OVar("ofNat_n"),)), args[0])), OOp("_unknown", (OVar("ofNat_n"),))))
            results.append((rhs, "Mathlib: Cardinal_lift_eq_beth_ofNat"))
        except Exception:
            pass
    return results


def _r0023_aleph_mul_aleph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph_mul_aleph
    # ℵ_ o₁ * ℵ_ o₂ = ℵ_ (max o₁ o₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OOp("max", (OVar("o_1"), OVar("o_2"),)),))
            results.append((rhs, "Mathlib: Cardinal_aleph_mul_aleph"))
        except Exception:
            pass
    return results


def _r0024_aleph0_mul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph0_mul_eq
    # ℵ₀ * a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Cardinal_aleph0_mul_eq"))
        except Exception:
            pass
    return results


def _r0025_mul_aleph0_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mul_aleph0_eq
    # a * ℵ₀ = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_mul_aleph0_eq"))
        except Exception:
            pass
    return results


def _r0026_aleph0_mul_mk_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph0_mul_mk_eq
    # ℵ₀ * #α = #α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Cardinal_aleph0_mul_mk_eq"))
        except Exception:
            pass
    return results


def _r0027_aleph_mul_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph_mul_aleph0
    # ℵ_ o * ℵ₀ = ℵ_ o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("o"),))
            results.append((rhs, "Mathlib: Cardinal_aleph_mul_aleph0"))
        except Exception:
            pass
    return results


def _r0028_lt_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lt_aleph0
    # c < ℵ₀ ↔ ∃ n : ℕ, c = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Cardinal_lt_aleph0"))
        except Exception:
            pass
    return results


def _r0029_mk_eq_nat_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_eq_nat_iff
    # #α = n ↔ Nonempty (α ≃ Fin n)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("n"), OOp("Nonempty", (OOp("a", (OVar("_unknown"), OVar("Fin"), OVar("n"),)),))))
            results.append((rhs, "Mathlib: Cardinal_mk_eq_nat_iff"))
    except Exception:
        pass
    return results


def _r0030_denumerable_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.denumerable_iff
    # Nonempty (Denumerable α) ↔ #α = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("_0")
            results.append((rhs, "Mathlib: Cardinal_denumerable_iff"))
        except Exception:
            pass
    return results


def _r0031_aleph0_mul_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph0_mul_aleph0
    # ℵ₀ * ℵ₀ = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Cardinal_aleph0_mul_aleph0"))
        except Exception:
            pass
    return results


def _r0032_ofNat_mul_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofNat_mul_aleph0
    # ofNat(n) * ℵ₀ = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Cardinal_ofNat_mul_aleph0"))
        except Exception:
            pass
    return results


def _r0033_aleph0_mul_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph0_mul_ofNat
    # ℵ₀ * ofNat(n) = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_aleph0_mul_ofNat"))
        except Exception:
            pass
    return results


def _r0034_nat_add_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.nat_add_aleph0
    # ↑n + ℵ₀ = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Cardinal_nat_add_aleph0"))
        except Exception:
            pass
    return results


def _r0035_ofNat_add_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofNat_add_aleph0
    # ofNat(n) + ℵ₀ = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Cardinal_ofNat_add_aleph0"))
        except Exception:
            pass
    return results


def _r0036_aleph0_add_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph0_add_ofNat
    # ℵ₀ + ofNat(n) = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_aleph0_add_ofNat"))
        except Exception:
            pass
    return results


def _r0037_exists_nat_eq_of_le_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.exists_nat_eq_of_le_nat
    # ∃ m, m ≤ n ∧ c = m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OVar("m")
            results.append((rhs, "Mathlib: Cardinal_exists_nat_eq_of_le_nat"))
        except Exception:
            pass
    return results


def _r0038_mk_multiplicative(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_multiplicative
    # #(Multiplicative α) = #α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Multiplicative_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_a")
            results.append((rhs, "Mathlib: Cardinal_mk_multiplicative"))
    except Exception:
        pass
    return results


def _r0039_mk_mulOpposite(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_mulOpposite
    # #(MulOpposite α) = #α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_MulOpposite_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_a")
            results.append((rhs, "Mathlib: Cardinal_mk_mulOpposite"))
    except Exception:
        pass
    return results


def _r0040_mk_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_singleton
    # #({x} : Set α) = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_x_colon_Set_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Cardinal_mk_singleton"))
    except Exception:
        pass
    return results


def _r0041_mk_list_eq_sum_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_list_eq_sum_pow
    # #(List α) = sum fun n ↦ #α ^ n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_List_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OOp("sum", (OVar("fun"), OVar("n"), OVar("_unknown"), OVar("hash_a"),)), OVar("n")))
            results.append((rhs, "Mathlib: Cardinal_mk_list_eq_sum_pow"))
    except Exception:
        pass
    return results


def _r0042_mk_setProd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_setProd
    # #(s ×ˢ t) = #s * #t
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_s_times_t")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("hash_s"), OVar("hash_t")))
            results.append((rhs, "Mathlib: Cardinal_mk_setProd"))
    except Exception:
        pass
    return results


def _r0043_mk_range_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_range_inr
    # #(range (@Sum.inr α β)) = lift.{u} #β
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_range_at_Sum_inr_a_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("lift_u", (OVar("hash_b"),))
            results.append((rhs, "Mathlib: Cardinal_mk_range_inr"))
    except Exception:
        pass
    return results


def _r0044_lift_continuum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_continuum
    # lift.{v} 𝔠 = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_lift_continuum"))
        except Exception:
            pass
    return results


def _r0045_continuum_toENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.continuum_toENat
    # toENat continuum = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toENat", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Cardinal_continuum_toENat"))
        except Exception:
            pass
    return results


def _r0046_continuum_add_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.continuum_add_aleph0
    # 𝔠 + ℵ₀ = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_continuum_add_aleph0"))
        except Exception:
            pass
    return results


def _r0047_continuum_add_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.continuum_add_self
    # 𝔠 + 𝔠 = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Cardinal_continuum_add_self"))
        except Exception:
            pass
    return results


def _r0048_nat_add_continuum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.nat_add_continuum
    # ↑n + 𝔠 = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Cardinal_nat_add_continuum"))
        except Exception:
            pass
    return results


def _r0049_continuum_add_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.continuum_add_nat
    # 𝔠 + n = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_continuum_add_nat"))
        except Exception:
            pass
    return results


def _r0050_ofNat_add_continuum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofNat_add_continuum
    # ofNat(n) + 𝔠 = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Cardinal_ofNat_add_continuum"))
        except Exception:
            pass
    return results


def _r0051_continuum_add_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.continuum_add_ofNat
    # 𝔠 + ofNat(n) = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_continuum_add_ofNat"))
        except Exception:
            pass
    return results


def _r0052_continuum_mul_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.continuum_mul_aleph0
    # 𝔠 * ℵ₀ = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_continuum_mul_aleph0"))
        except Exception:
            pass
    return results


def _r0053_aleph0_mul_continuum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph0_mul_continuum
    # ℵ₀ * 𝔠 = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Cardinal_aleph0_mul_continuum"))
        except Exception:
            pass
    return results


def _r0054_nat_mul_continuum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.nat_mul_continuum
    # ↑n * 𝔠 = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Cardinal_nat_mul_continuum"))
        except Exception:
            pass
    return results


def _r0055_continuum_mul_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.continuum_mul_nat
    # 𝔠 * n = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_continuum_mul_nat"))
        except Exception:
            pass
    return results


def _r0056_ofNat_mul_continuum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofNat_mul_continuum
    # ofNat(n) * 𝔠 = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Cardinal_ofNat_mul_continuum"))
        except Exception:
            pass
    return results


def _r0057_continuum_mul_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.continuum_mul_ofNat
    # 𝔠 * ofNat(n) = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_continuum_mul_ofNat"))
        except Exception:
            pass
    return results


def _r0058_nat_power_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.nat_power_aleph0
    # n ^ ℵ₀ = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("_unknown")
            results.append((rhs, "Mathlib: Cardinal_nat_power_aleph0"))
        except Exception:
            pass
    return results


def _r0059_continuum_power_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.continuum_power_aleph0
    # 𝔠 ^ ℵ₀ = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_continuum_power_aleph0"))
        except Exception:
            pass
    return results


def _r0060_power_aleph0_of_le_continuum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.power_aleph0_of_le_continuum
    # x ^ ℵ₀ = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("_unknown")
            results.append((rhs, "Mathlib: Cardinal_power_aleph0_of_le_continuum"))
        except Exception:
            pass
    return results


def _r0061__unknown(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_lift.
    # lift.{w} (lift.{v} a) = lift.{max v w} a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_w", 1)
    if args is not None:
        try:
            rhs = OOp("lift_max_v_w", (OVar("a"),))
            results.append((rhs, "Mathlib: Cardinal_lift_lift"))
        except Exception:
            pass
    return results


def _r0062_lift_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_zero
    # lift 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Cardinal_lift_zero"))
        except Exception:
            pass
    return results


def _r0063_mk_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_eq_zero_iff
    # #α = 0 ↔ IsEmpty α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OLit(0), OOp("IsEmpty", (OVar("a"),))))
            results.append((rhs, "Mathlib: Cardinal_mk_eq_zero_iff"))
    except Exception:
        pass
    return results


def _r0064_mk_option(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_option
    # #(Option α) = #α + 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Option_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("hash_a"), OLit(1)))
            results.append((rhs, "Mathlib: Cardinal_mk_option"))
    except Exception:
        pass
    return results


def _r0065_mk_psum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_psum
    # #(α ⊕' β) = lift.{v} #α + lift.{u} #β
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_a_prime_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OOp("lift_v", (OVar("hash_a"),)), OOp("lift_u", (OVar("hash_b"),))))
            results.append((rhs, "Mathlib: Cardinal_mk_psum"))
    except Exception:
        pass
    return results


def _r0066_power_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.power_one
    # a ^ (1 : Cardinal) = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_power_one"))
        except Exception:
            pass
    return results


def _r0067_power_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.power_add
    # a ^ (b + c) = a ^ b * a ^ c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (args[0], OVar("b"))), OOp("**", (args[0], OVar("c")))))
            results.append((rhs, "Mathlib: Cardinal_power_add"))
        except Exception:
            pass
    return results


def _r0068_zero_power(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.zero_power
    # a ≠ 0 → (0 : Cardinal) ^ a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Cardinal_zero_power"))
        except Exception:
            pass
    return results


def _r0069_lift_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_add
    # lift.{v} (a + b) = lift.{v} a + lift.{v} b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("lift_v", (OVar("a"),)), OOp("lift_v", (OVar("b"),))))
            results.append((rhs, "Mathlib: Cardinal_lift_add"))
        except Exception:
            pass
    return results


def _r0070_mk_sigma_congr_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_sigma_congr_lift
    # lift.{max v' w'} #(Σ i, f i) = lift.{max v w} #(Σ i, g i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_max_v_prime_w_prime", 1)
    if args is not None:
        try:
            rhs = OOp("lift_max_v_w", (OVar("hash_Sig_i_g_i"),))
            results.append((rhs, "Mathlib: Cardinal_mk_sigma_congr_lift"))
        except Exception:
            pass
    return results


def _r0071_mk_pi_congr_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_pi_congr_lift
    # lift.{max v' w'} #(Π i, f i) = lift.{max v w} #(Π i, g i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_max_v_prime_w_prime", 1)
    if args is not None:
        try:
            rhs = OOp("lift_max_v_w", (OVar("hash_Pi_i_g_i"),))
            results.append((rhs, "Mathlib: Cardinal_mk_pi_congr_lift"))
        except Exception:
            pass
    return results


def _r0072_lift_mk_fin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_mk_fin
    # lift #(Fin n) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Cardinal_lift_mk_fin"))
        except Exception:
            pass
    return results


def _r0073_ofENat_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofENat_nat
    # ofENat n = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofENat", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_ofENat_nat"))
        except Exception:
            pass
    return results


def _r0074_ofENat_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofENat_zero
    # ofENat 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofENat", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Cardinal_ofENat_zero"))
        except Exception:
            pass
    return results


def _r0075_ofENat_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofENat_one
    # ofENat 1 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofENat", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Cardinal_ofENat_one"))
        except Exception:
            pass
    return results


def _r0076_ofENat_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofENat_ofNat
    # ((ofNat(n) : ℕ∞) : Cardinal) = OfNat.ofNat n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofNat_n_colon_inf", 2)
    if args is not None:
        try:
            rhs = OOp("OfNat_ofNat", (OVar("n"),))
            results.append((rhs, "Mathlib: Cardinal_ofENat_ofNat"))
        except Exception:
            pass
    return results


def _r0077_ofENat_eq_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofENat_eq_nat
    # (m : Cardinal) = n ↔ m = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("n"), OVar("m"))), OVar("n")))
            results.append((rhs, "Mathlib: Cardinal_ofENat_eq_nat"))
        except Exception:
            pass
    return results


def _r0078_nat_eq_ofENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.nat_eq_ofENat
    # (m : Cardinal) = n ↔ m = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("n"), OVar("m"))), OVar("n")))
            results.append((rhs, "Mathlib: Cardinal_nat_eq_ofENat"))
        except Exception:
            pass
    return results


def _r0079_ofENat_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofENat_eq_zero
    # (m : Cardinal) = 0 ↔ m = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("m"))), OLit(0)))
            results.append((rhs, "Mathlib: Cardinal_ofENat_eq_zero"))
        except Exception:
            pass
    return results


def _r0080_zero_eq_ofENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.zero_eq_ofENat
    # 0 = (m : Cardinal) ↔ m = 0
    results: List[Tuple[OTerm, str]] = []
    if _is_lit(term, 0):
        try:
            rhs = OOp("==", (OOp("iff", (OOp("m", (OVar("colon"), OVar("Cardinal"),)), OVar("m"))), OLit(0)))
            results.append((rhs, "Mathlib: Cardinal_zero_eq_ofENat"))
        except Exception:
            pass
    return results


def _r0081_ofENat_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofENat_eq_one
    # (m : Cardinal) = 1 ↔ m = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), OVar("m"))), OLit(1)))
            results.append((rhs, "Mathlib: Cardinal_ofENat_eq_one"))
        except Exception:
            pass
    return results


def _r0082_one_eq_ofENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.one_eq_ofENat
    # 1 = (m : Cardinal) ↔ m = 1
    results: List[Tuple[OTerm, str]] = []
    if _is_lit(term, 1):
        try:
            rhs = OOp("==", (OOp("iff", (OOp("m", (OVar("colon"), OVar("Cardinal"),)), OVar("m"))), OLit(1)))
            results.append((rhs, "Mathlib: Cardinal_one_eq_ofENat"))
        except Exception:
            pass
    return results


def _r0083_ofENat_eq_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofENat_eq_ofNat
    # (m : Cardinal) = ofNat(n) ↔ m = OfNat.ofNat n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("ofNat_n"), OVar("m"))), OOp("OfNat_ofNat", (OVar("n"),))))
            results.append((rhs, "Mathlib: Cardinal_ofENat_eq_ofNat"))
        except Exception:
            pass
    return results


def _r0084_ofNat_eq_ofENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofNat_eq_ofENat
    # ofNat(m) = (n : Cardinal) ↔ OfNat.ofNat m = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofNat_m")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("n", (OVar("colon"), OVar("Cardinal"),)), OOp("OfNat_ofNat", (OVar("m"),)))), OVar("n")))
            results.append((rhs, "Mathlib: Cardinal_ofNat_eq_ofENat"))
    except Exception:
        pass
    return results


def _r0085_lift_ofENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_ofENat
    # ∀ m : ℕ∞, lift.{u, v} m = m   | (m : ℕ) => lift_natCast m   | ⊤ => lift_aleph0  @[simp] lemma lift_lt_ofENat {x : Cardin
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_u_v", 1)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("m", (OVar("pipe"), OOp("m", (OVar("colon"), OVar("_unknown"),)), OVar("eq_gt"), OVar("lift_natCast"), args[0], OVar("pipe"), OVar("top"), OVar("eq_gt"), OVar("lift_aleph0_at_simp"), OVar("lemma"), OVar("lift_lt_ofENat"), OVar("x_colon_Cardinal_v"), OVar("m_colon_inf"), OVar("colon"), OVar("lift_u"), OVar("x"),)), OOp("<", (OOp("iff", (args[0], OVar("x"))), args[0]))))
            results.append((rhs, "Mathlib: Cardinal_lift_ofENat"))
        except Exception:
            pass
    return results


def _r0086_lift_eq_ofENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_eq_ofENat
    # lift.{u} x = m ↔ x = m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_u", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("m"), args[0])), OVar("m")))
            results.append((rhs, "Mathlib: Cardinal_lift_eq_ofENat"))
        except Exception:
            pass
    return results


def _r0087_ofENat_eq_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofENat_eq_lift
    # m = lift.{u} x ↔ m = x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("lift_u", (OVar("x"),)), OVar("m"))), OVar("x")))
            results.append((rhs, "Mathlib: Cardinal_ofENat_eq_lift"))
    except Exception:
        pass
    return results


def _r0088_range_ofENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.range_ofENat
    # range ofENat = Iic ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OOp("Iic", (OVar("_0"),))
            results.append((rhs, "Mathlib: Cardinal_range_ofENat"))
        except Exception:
            pass
    return results


def _r0089_toENat_comp_ofENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toENat_comp_ofENat
    # toENat ∘ (↑) = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Cardinal_toENat_comp_ofENat"))
        except Exception:
            pass
    return results


def _r0090_toENat_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toENat_nat
    # toENat n = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toENat", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_toENat_nat"))
        except Exception:
            pass
    return results


def _r0091_toENat_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toENat_ofNat
    # toENat ofNat(n) = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toENat", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_toENat_ofNat"))
        except Exception:
            pass
    return results


def _r0092_toENat_eq_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toENat_eq_natCast
    # toENat c = n ↔ c = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toENat", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("n"), args[0])), OVar("n")))
            results.append((rhs, "Mathlib: Cardinal_toENat_eq_natCast"))
        except Exception:
            pass
    return results


def _r0093_toENat_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toENat_eq_zero
    # toENat c = 0 ↔ c = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toENat", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: Cardinal_toENat_eq_zero"))
        except Exception:
            pass
    return results


def _r0094_toENat_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toENat_eq_one
    # toENat c = 1 ↔ c = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toENat", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[0])), OLit(1)))
            results.append((rhs, "Mathlib: Cardinal_toENat_eq_one"))
        except Exception:
            pass
    return results


def _r0095_toENat_eq_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toENat_eq_ofNat
    # toENat c = ofNat(n) ↔ c = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toENat", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("ofNat_n"), args[0])), OVar("ofNat_n")))
            results.append((rhs, "Mathlib: Cardinal_toENat_eq_ofNat"))
        except Exception:
            pass
    return results


def _r0096_ofNat_eq_toENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofNat_eq_toENat
    # ofNat(n) = toENat c ↔ ofNat(n) = c
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofNat_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("toENat", (OVar("c"),)), OVar("ofNat_n"))), OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_ofNat_eq_toENat"))
    except Exception:
        pass
    return results


def _r0097_toENat_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toENat_eq_top
    # toENat c = ⊤ ↔ ℵ₀ ≤ c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toENat", 1)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("iff", (OVar("top"), OVar("_0"))), args[0]))
            results.append((rhs, "Mathlib: Cardinal_toENat_eq_top"))
        except Exception:
            pass
    return results


def _r0098_toENat_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toENat_lift
    # toENat (lift.{v} c) = toENat c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toENat", 1)
    if args is not None:
        try:
            rhs = OOp("toENat", (OVar("c"),))
            results.append((rhs, "Mathlib: Cardinal_toENat_lift"))
        except Exception:
            pass
    return results


def _r0099_aleph0_add_ofENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph0_add_ofENat
    # ℵ₀ + m = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_aleph0_add_ofENat"))
        except Exception:
            pass
    return results


def _r0100_ofENat_add_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofENat_add_aleph0
    # m + ℵ₀ = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Cardinal_ofENat_add_aleph0"))
        except Exception:
            pass
    return results


def _r0101_ofENat_mul_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofENat_mul_aleph0
    # ↑m * ℵ₀ = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Cardinal_ofENat_mul_aleph0"))
        except Exception:
            pass
    return results


def _r0102_ofENat_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofENat_mul
    # ofENat (m * n) = m * n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofENat", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("m"), OVar("n")))
            results.append((rhs, "Mathlib: Cardinal_ofENat_mul"))
        except Exception:
            pass
    return results


def _r0103_mk_freeGroup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_freeGroup
    # #(FreeGroup α) = max #α ℵ₀
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_FreeGroup_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("max", (OVar("hash_a"), OVar("_0"),))
            results.append((rhs, "Mathlib: Cardinal_mk_freeGroup"))
    except Exception:
        pass
    return results


def _r0104_mk_freeCommRing(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_freeCommRing
    # #(FreeCommRing α) = max #α ℵ₀
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_FreeCommRing_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("max", (OVar("hash_a"), OVar("_0"),))
            results.append((rhs, "Mathlib: Cardinal_mk_freeCommRing"))
    except Exception:
        pass
    return results


def _r0105_lift_max(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_max
    # lift.{u, v} (max a b) = max (lift.{u, v} a) (lift.{u, v} b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_u_v", 1)
    if args is not None:
        try:
            rhs = OOp("max", (OOp("lift_u_v", (OVar("a"),)), OOp("lift_u_v", (OVar("b"),)),))
            results.append((rhs, "Mathlib: Cardinal_lift_max"))
        except Exception:
            pass
    return results


def _r0106_mk_fintype(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_fintype
    # #α = Fintype.card α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Fintype_card", (OVar("a"),))
            results.append((rhs, "Mathlib: Cardinal_mk_fintype"))
    except Exception:
        pass
    return results


def _r0107_lift_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_eq_one
    # lift.{u} a = 1 ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_u", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[0])), OLit(1)))
            results.append((rhs, "Mathlib: Cardinal_lift_eq_one"))
        except Exception:
            pass
    return results


def _r0108_lift_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_mul
    # lift.{v} (a * b) = lift.{v} a * lift.{v} b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("lift_v", (OVar("a"),)), OOp("lift_v", (OVar("b"),))))
            results.append((rhs, "Mathlib: Cardinal_lift_mul"))
        except Exception:
            pass
    return results


def _r0109_lift_two_power(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_two_power
    # lift.{v} (2 ^ a) = 2 ^ lift.{v} a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OLit(2), OOp("lift_v", (OVar("a"),))))
            results.append((rhs, "Mathlib: Cardinal_lift_two_power"))
        except Exception:
            pass
    return results


def _r0110_aleph0_eq_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph0_eq_lift
    # ℵ₀ = lift.{v} c ↔ ℵ₀ = c
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("lift_v", (OVar("c"),)), OVar("_0"))), OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_aleph0_eq_lift"))
    except Exception:
        pass
    return results


def _r0111_lift_eq_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_eq_aleph0
    # lift.{v} c = ℵ₀ ↔ c = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("_0"), args[0])), OVar("_0")))
            results.append((rhs, "Mathlib: Cardinal_lift_eq_aleph0"))
        except Exception:
            pass
    return results


def _r0112_lift_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_ofNat
    # lift.{u} (ofNat(n) : Cardinal.{v}) = OfNat.ofNat n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_u", 1)
    if args is not None:
        try:
            rhs = OOp("OfNat_ofNat", (OVar("n"),))
            results.append((rhs, "Mathlib: Cardinal_lift_ofNat"))
        except Exception:
            pass
    return results


def _r0113_lift_eq_ofNat_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_eq_ofNat_iff
    # lift.{v} a = ofNat(n) ↔ a = OfNat.ofNat n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("ofNat_n"), args[0])), OOp("OfNat_ofNat", (OVar("n"),))))
            results.append((rhs, "Mathlib: Cardinal_lift_eq_ofNat_iff"))
        except Exception:
            pass
    return results


def _r0114_toNat_ofENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toNat_ofENat
    # toNat n = ENat.toNat n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toNat", 1)
    if args is not None:
        try:
            rhs = OOp("ENat_toNat", (args[0],))
            results.append((rhs, "Mathlib: Cardinal_toNat_ofENat"))
        except Exception:
            pass
    return results


def _r0115_toNat_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toNat_natCast
    # toNat n = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toNat", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_toNat_natCast"))
        except Exception:
            pass
    return results


def _r0116_toNat_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toNat_eq_zero
    # toNat c = 0 ↔ c = 0 ∨ ℵ₀ ≤ c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toNat", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OOp("<=", (OOp("or", (OLit(0), OVar("_0"))), args[0]))))
            results.append((rhs, "Mathlib: Cardinal_toNat_eq_zero"))
        except Exception:
            pass
    return results


def _r0117_cast_toNat_of_lt_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.cast_toNat_of_lt_aleph0
    # ↑(toNat c) = c
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("toNat_c")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("c")
            results.append((rhs, "Mathlib: Cardinal_cast_toNat_of_lt_aleph0"))
    except Exception:
        pass
    return results


def _r0118_aleph0_toNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph0_toNat
    # toNat ℵ₀ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toNat", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Cardinal_aleph0_toNat"))
        except Exception:
            pass
    return results


def _r0119_mk_toNat_eq_card(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_toNat_eq_card
    # toNat #α = Fintype.card α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toNat", 1)
    if args is not None:
        try:
            rhs = OOp("Fintype_card", (OVar("a"),))
            results.append((rhs, "Mathlib: Cardinal_mk_toNat_eq_card"))
        except Exception:
            pass
    return results


def _r0120_one_toNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.one_toNat
    # toNat 1 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toNat", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Cardinal_one_toNat"))
        except Exception:
            pass
    return results


def _r0121_toNat_eq_one_iff_unique(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toNat_eq_one_iff_unique
    # toNat #α = 1 ↔ Subsingleton α ∧ Nonempty α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toNat", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("iff", (OLit(1), OOp("Subsingleton", (OVar("a"),)))), OOp("Nonempty", (OVar("a"),))))
            results.append((rhs, "Mathlib: Cardinal_toNat_eq_one_iff_unique"))
        except Exception:
            pass
    return results


def _r0122_toNat_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toNat_congr
    # toNat #α = toNat #β
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toNat", 1)
    if args is not None:
        try:
            rhs = OOp("toNat", (OVar("hash_b"),))
            results.append((rhs, "Mathlib: Cardinal_toNat_congr"))
        except Exception:
            pass
    return results


def _r0123_ord_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ord_zero
    # ord 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ord", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Cardinal_ord_zero"))
        except Exception:
            pass
    return results


def _r0124_ord_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ord_nat
    # ord n = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ord", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_ord_nat"))
        except Exception:
            pass
    return results


def _r0125_ord_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ord_one
    # ord 1 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ord", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Cardinal_ord_one"))
        except Exception:
            pass
    return results


def _r0126_ord_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ord_eq_zero
    # a.ord = 0 ↔ a = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_ord")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("a"))), OLit(0)))
            results.append((rhs, "Mathlib: Cardinal_ord_eq_zero"))
    except Exception:
        pass
    return results


def _r0127_ord_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ord_eq_one
    # a.ord = 1 ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_ord")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(1), OVar("a"))), OLit(1)))
            results.append((rhs, "Mathlib: Cardinal_ord_eq_one"))
    except Exception:
        pass
    return results


def _r0128_ord_eq_omega0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ord_eq_omega0
    # a.ord = ω ↔ a = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_ord")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("omega"), OVar("a"))), OVar("_0")))
            results.append((rhs, "Mathlib: Cardinal_ord_eq_omega0"))
    except Exception:
        pass
    return results


def _r0129_univ_umax(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.univ_umax
    # univ.{u, max (u + 1) v} = univ.{u, v}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("univ_u_max_u_plus_1_v")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("univ_u_v")
            results.append((rhs, "Mathlib: Cardinal_univ_umax"))
    except Exception:
        pass
    return results


def _r0130_preAleph_lt_preAleph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.preAleph_lt_preAleph
    # preAleph o₁ < preAleph o₂ ↔ o₁ < o₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("o_1"), OVar("o_2")))
            results.append((rhs, "Mathlib: Cardinal_preAleph_lt_preAleph"))
        except Exception:
            pass
    return results


def _r0131_preAleph_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.preAleph_pos
    # 0 < preAleph o ↔ 0 < o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OLit(0), OVar("o")))
            results.append((rhs, "Mathlib: Cardinal_preAleph_pos"))
        except Exception:
            pass
    return results


def _r0132_aleph0_le_preAleph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph0_le_preAleph
    # ℵ₀ ≤ preAleph o ↔ ω ≤ o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("omega"), OVar("o")))
            results.append((rhs, "Mathlib: Cardinal_aleph0_le_preAleph"))
        except Exception:
            pass
    return results


def _r0133_aleph_lt_aleph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph_lt_aleph
    # ℵ_ o₁ < ℵ_ o₂ ↔ o₁ < o₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("o_1"), OVar("o_2")))
            results.append((rhs, "Mathlib: Cardinal_aleph_lt_aleph"))
        except Exception:
            pass
    return results


def _r0134_aleph_one_le_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph_one_le_iff
    # ℵ₁ ≤ c ↔ ℵ₀ < c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("_0"), args[1]))
            results.append((rhs, "Mathlib: Cardinal_aleph_one_le_iff"))
        except Exception:
            pass
    return results


def _r0135_lt_aleph_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lt_aleph_one_iff
    # c < ℵ₁ ↔ c ≤ ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (args[0], OVar("_0")))
            results.append((rhs, "Mathlib: Cardinal_lt_aleph_one_iff"))
        except Exception:
            pass
    return results


def _r0136_preBeth_le_preBeth(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.preBeth_le_preBeth
    # preBeth o₁ ≤ preBeth o₂ ↔ o₁ ≤ o₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("o_1"), OVar("o_2")))
            results.append((rhs, "Mathlib: Cardinal_preBeth_le_preBeth"))
        except Exception:
            pass
    return results


def _r0137_isStrongLimit_preBeth(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.isStrongLimit_preBeth
    # IsStrongLimit (preBeth o) ↔ IsSuccLimit o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsStrongLimit", 1)
    if args is not None:
        try:
            rhs = OOp("IsSuccLimit", (OVar("o"),))
            results.append((rhs, "Mathlib: Cardinal_isStrongLimit_preBeth"))
        except Exception:
            pass
    return results


def _r0138_beth_le_beth(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.beth_le_beth
    # ℶ_ o₁ ≤ ℶ_ o₂ ↔ o₁ ≤ o₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("o_1"), OVar("o_2")))
            results.append((rhs, "Mathlib: Cardinal_beth_le_beth"))
        except Exception:
            pass
    return results


def _r0139_lift_le_aleph_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_le_aleph_natCast
    # lift.{v} c ≤ ℵ_ n ↔ c ≤ ℵ_ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("c"), OOp("_unknown", (OVar("n"),))))
            results.append((rhs, "Mathlib: Cardinal_lift_le_aleph_natCast"))
        except Exception:
            pass
    return results


def _r0140_aleph_natCast_lt_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph_natCast_lt_lift
    # ℵ_ n < lift.{v} c ↔ ℵ_ n < c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("_unknown", (OVar("n"),)), OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_aleph_natCast_lt_lift"))
        except Exception:
            pass
    return results


def _r0141_lift_lt_aleph_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_lt_aleph_natCast
    # lift.{v} c < ℵ_ n ↔ c < ℵ_ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("c"), OOp("_unknown", (OVar("n"),))))
            results.append((rhs, "Mathlib: Cardinal_lift_lt_aleph_natCast"))
        except Exception:
            pass
    return results


def _r0142_aleph_ofNat_le_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph_ofNat_le_lift
    # ℵ_ ofNat(n) ≤ lift.{v} c ↔ ℵ_ ofNat(n) ≤ c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("_unknown", (OVar("ofNat_n"),)), OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_aleph_ofNat_le_lift"))
        except Exception:
            pass
    return results


def _r0143_lift_le_aleph_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_le_aleph_ofNat
    # lift.{v} c ≤ ℵ_ ofNat(n) ↔ c ≤ ℵ_ ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("c"), OOp("_unknown", (OVar("ofNat_n"),))))
            results.append((rhs, "Mathlib: Cardinal_lift_le_aleph_ofNat"))
        except Exception:
            pass
    return results


def _r0144_aleph_ofNat_lt_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph_ofNat_lt_lift
    # ℵ_ ofNat(n) < lift.{v} c ↔ ℵ_ ofNat(n) < c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("_unknown", (OVar("ofNat_n"),)), OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_aleph_ofNat_lt_lift"))
        except Exception:
            pass
    return results


def _r0145_lift_lt_aleph_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_lt_aleph_ofNat
    # lift.{v} c < ℵ_ ofNat(n) ↔ c < ℵ_ ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("c"), OOp("_unknown", (OVar("ofNat_n"),))))
            results.append((rhs, "Mathlib: Cardinal_lift_lt_aleph_ofNat"))
        except Exception:
            pass
    return results


def _r0146_beth_natCast_le_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.beth_natCast_le_lift
    # ℶ_ n ≤ lift.{v} c ↔ ℶ_ n ≤ c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("_unknown", (OVar("n"),)), OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_beth_natCast_le_lift"))
        except Exception:
            pass
    return results


def _r0147_lift_le_beth_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_le_beth_natCast
    # lift.{v} c ≤ ℶ_ n ↔ c ≤ ℶ_ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("c"), OOp("_unknown", (OVar("n"),))))
            results.append((rhs, "Mathlib: Cardinal_lift_le_beth_natCast"))
        except Exception:
            pass
    return results


def _r0148_beth_natCast_lt_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.beth_natCast_lt_lift
    # ℶ_ n < lift.{v} c ↔ ℶ_ n < c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("_unknown", (OVar("n"),)), OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_beth_natCast_lt_lift"))
        except Exception:
            pass
    return results


def _r0149_lift_lt_beth_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_lt_beth_natCast
    # lift.{v} c < ℶ_ n ↔ c < ℶ_ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("c"), OOp("_unknown", (OVar("n"),))))
            results.append((rhs, "Mathlib: Cardinal_lift_lt_beth_natCast"))
        except Exception:
            pass
    return results


def _r0150_beth_ofNat_le_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.beth_ofNat_le_lift
    # ℶ_ ofNat(n) ≤ lift.{v} c ↔ ℶ_ ofNat(n) ≤ c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("_unknown", (OVar("ofNat_n"),)), OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_beth_ofNat_le_lift"))
        except Exception:
            pass
    return results


def _r0151_lift_le_beth_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_le_beth_ofNat
    # lift.{v} c ≤ ℶ_ ofNat(n) ↔ c ≤ ℶ_ ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("c"), OOp("_unknown", (OVar("ofNat_n"),))))
            results.append((rhs, "Mathlib: Cardinal_lift_le_beth_ofNat"))
        except Exception:
            pass
    return results


def _r0152_beth_ofNat_lt_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.beth_ofNat_lt_lift
    # ℶ_ ofNat(n) < lift.{v} c ↔ ℶ_ ofNat(n) < c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("_unknown", (OVar("ofNat_n"),)), OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_beth_ofNat_lt_lift"))
        except Exception:
            pass
    return results


def _r0153_lift_lt_beth_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_lt_beth_ofNat
    # lift.{v} c < ℶ_ ofNat(n) ↔ c < ℶ_ ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("c"), OOp("_unknown", (OVar("ofNat_n"),))))
            results.append((rhs, "Mathlib: Cardinal_lift_lt_beth_ofNat"))
        except Exception:
            pass
    return results


def _r0154_mk_le_aleph0_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_le_aleph0_iff
    # #α ≤ ℵ₀ ↔ Countable α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("Countable", (OVar("a"),))
            results.append((rhs, "Mathlib: Cardinal_mk_le_aleph0_iff"))
        except Exception:
            pass
    return results


def _r0155_le_aleph0_iff_set_countable(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.le_aleph0_iff_set_countable
    # #s ≤ ℵ₀ ↔ s.Countable
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OVar("s_Countable")
            results.append((rhs, "Mathlib: Cardinal_le_aleph0_iff_set_countable"))
        except Exception:
            pass
    return results


def _r0156_add_le_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.add_le_aleph0
    # c₁ + c₂ ≤ ℵ₀ ↔ c₁ ≤ ℵ₀ ∧ c₂ ≤ ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("c_1"), OOp("<=", (OOp("and", (args[1], OVar("c_2"))), args[1]))))
            results.append((rhs, "Mathlib: Cardinal_add_le_aleph0"))
        except Exception:
            pass
    return results


def _r0157_two_le_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.two_le_iff
    # (2 : Cardinal) ≤ #α ↔ ∃ x y : α, x ≠ y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("exists", (OVar("x"), OVar("y"), OVar("colon"), OVar("a"), OVar("x"),)), OVar("y")))
            results.append((rhs, "Mathlib: Cardinal_two_le_iff"))
        except Exception:
            pass
    return results


def _r0158_continuum_le_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.continuum_le_lift
    # 𝔠 ≤ lift.{v} c ↔ 𝔠 ≤ c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (args[0], OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_continuum_le_lift"))
        except Exception:
            pass
    return results


def _r0159_lift_le_continuum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_le_continuum
    # lift.{v} c ≤ 𝔠 ↔ c ≤ 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("c"), args[1]))
            results.append((rhs, "Mathlib: Cardinal_lift_le_continuum"))
        except Exception:
            pass
    return results


def _r0160_continuum_lt_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.continuum_lt_lift
    # 𝔠 < lift.{v} c ↔ 𝔠 < c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (args[0], OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_continuum_lt_lift"))
        except Exception:
            pass
    return results


def _r0161_lift_lt_continuum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_lt_continuum
    # lift.{v} c < 𝔠 ↔ c < 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("c"), args[1]))
            results.append((rhs, "Mathlib: Cardinal_lift_lt_continuum"))
        except Exception:
            pass
    return results


def _r0162_ofENat_lt_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofENat_lt_nat
    # ofENat m < n ↔ m < n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("m"), args[1]))
            results.append((rhs, "Mathlib: Cardinal_ofENat_lt_nat"))
        except Exception:
            pass
    return results


def _r0163_ofENat_lt_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofENat_lt_ofNat
    # ofENat m < ofNat(n) ↔ m < OfNat.ofNat n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("m"), OOp("OfNat_ofNat", (OVar("n"),))))
            results.append((rhs, "Mathlib: Cardinal_ofENat_lt_ofNat"))
        except Exception:
            pass
    return results


def _r0164_nat_lt_ofENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.nat_lt_ofENat
    # (m : Cardinal) < n ↔ m < n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("m"), args[1]))
            results.append((rhs, "Mathlib: Cardinal_nat_lt_ofENat"))
        except Exception:
            pass
    return results


def _r0165_ofENat_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofENat_pos
    # 0 < (m : Cardinal) ↔ 0 < m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OLit(0), OVar("m")))
            results.append((rhs, "Mathlib: Cardinal_ofENat_pos"))
        except Exception:
            pass
    return results


def _r0166_one_lt_ofENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.one_lt_ofENat
    # 1 < (m : Cardinal) ↔ 1 < m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OLit(1), OVar("m")))
            results.append((rhs, "Mathlib: Cardinal_one_lt_ofENat"))
        except Exception:
            pass
    return results


def _r0167_ofNat_lt_ofENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofNat_lt_ofENat
    # (ofNat(m) : Cardinal) < n ↔ OfNat.ofNat m < n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("OfNat_ofNat", (OVar("m"),)), args[1]))
            results.append((rhs, "Mathlib: Cardinal_ofNat_lt_ofENat"))
        except Exception:
            pass
    return results


def _r0168_ofENat_le_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofENat_le_nat
    # ofENat m ≤ n ↔ m ≤ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("m"), args[1]))
            results.append((rhs, "Mathlib: Cardinal_ofENat_le_nat"))
        except Exception:
            pass
    return results


def _r0169_ofENat_le_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofENat_le_one
    # ofENat m ≤ 1 ↔ m ≤ 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("m"), OLit(1)))
            results.append((rhs, "Mathlib: Cardinal_ofENat_le_one"))
        except Exception:
            pass
    return results


def _r0170_ofENat_le_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofENat_le_ofNat
    # ofENat m ≤ ofNat(n) ↔ m ≤ OfNat.ofNat n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("m"), OOp("OfNat_ofNat", (OVar("n"),))))
            results.append((rhs, "Mathlib: Cardinal_ofENat_le_ofNat"))
        except Exception:
            pass
    return results


def _r0171_nat_le_ofENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.nat_le_ofENat
    # (m : Cardinal) ≤ n ↔ m ≤ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("m"), args[1]))
            results.append((rhs, "Mathlib: Cardinal_nat_le_ofENat"))
        except Exception:
            pass
    return results


def _r0172_one_le_ofENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.one_le_ofENat
    # 1 ≤ (n : Cardinal) ↔ 1 ≤ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OLit(1), OVar("n")))
            results.append((rhs, "Mathlib: Cardinal_one_le_ofENat"))
        except Exception:
            pass
    return results


def _r0173_ofNat_le_ofENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofNat_le_ofENat
    # (ofNat(m) : Cardinal) ≤ n ↔ OfNat.ofNat m ≤ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("OfNat_ofNat", (OVar("m"),)), args[1]))
            results.append((rhs, "Mathlib: Cardinal_ofNat_le_ofENat"))
        except Exception:
            pass
    return results


def _r0174_lift_lt_ofENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_lt_ofENat
    # lift.{u} x < m ↔ x < m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("x"), args[1]))
            results.append((rhs, "Mathlib: Cardinal_lift_lt_ofENat"))
        except Exception:
            pass
    return results


def _r0175_lift_le_ofENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_le_ofENat
    # lift.{u} x ≤ m ↔ x ≤ m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("x"), args[1]))
            results.append((rhs, "Mathlib: Cardinal_lift_le_ofENat"))
        except Exception:
            pass
    return results


def _r0176_ofENat_lt_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofENat_lt_lift
    # m < lift.{u} x ↔ m < x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (args[0], OVar("x")))
            results.append((rhs, "Mathlib: Cardinal_ofENat_lt_lift"))
        except Exception:
            pass
    return results


def _r0177_ofENat_le_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofENat_le_lift
    # m ≤ lift.{u} x ↔ m ≤ x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (args[0], OVar("x")))
            results.append((rhs, "Mathlib: Cardinal_ofENat_le_lift"))
        except Exception:
            pass
    return results


def _r0178_toENat_le_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toENat_le_natCast
    # toENat c ≤ n ↔ c ≤ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("c"), args[1]))
            results.append((rhs, "Mathlib: Cardinal_toENat_le_natCast"))
        except Exception:
            pass
    return results


def _r0179_toENat_le_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toENat_le_one
    # toENat c ≤ 1 ↔ c ≤ 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("c"), OLit(1)))
            results.append((rhs, "Mathlib: Cardinal_toENat_le_one"))
        except Exception:
            pass
    return results


def _r0180_toENat_le_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toENat_le_ofNat
    # toENat c ≤ ofNat(n) ↔ c ≤ ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("c"), args[1]))
            results.append((rhs, "Mathlib: Cardinal_toENat_le_ofNat"))
        except Exception:
            pass
    return results


def _r0181_one_le_toENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.one_le_toENat
    # 1 ≤ toENat c ↔ 1 ≤ c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OLit(1), OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_one_le_toENat"))
        except Exception:
            pass
    return results


def _r0182_ofNat_le_toENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofNat_le_toENat
    # ofNat(n) ≤ toENat c ↔ ofNat(n) ≤ c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (args[0], OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_ofNat_le_toENat"))
        except Exception:
            pass
    return results


def _r0183_toENat_lt_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toENat_lt_natCast
    # toENat c < n ↔ c < n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("c"), args[1]))
            results.append((rhs, "Mathlib: Cardinal_toENat_lt_natCast"))
        except Exception:
            pass
    return results


def _r0184_toENat_lt_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toENat_lt_one
    # toENat c < 1 ↔ c < 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("c"), OLit(1)))
            results.append((rhs, "Mathlib: Cardinal_toENat_lt_one"))
        except Exception:
            pass
    return results


def _r0185_toENat_lt_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toENat_lt_ofNat
    # toENat c < ofNat(n) ↔ c < ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("c"), args[1]))
            results.append((rhs, "Mathlib: Cardinal_toENat_lt_ofNat"))
        except Exception:
            pass
    return results


def _r0186_natCast_lt_toENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.natCast_lt_toENat
    # n < toENat c ↔ n < c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (args[0], OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_natCast_lt_toENat"))
        except Exception:
            pass
    return results


def _r0187_one_lt_toENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.one_lt_toENat
    # 1 < toENat c ↔ 1 < c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OLit(1), OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_one_lt_toENat"))
        except Exception:
            pass
    return results


def _r0188_ofNat_lt_toENat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ofNat_lt_toENat
    # ofNat(n) < toENat c ↔ ofNat(n) < c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (args[0], OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_ofNat_lt_toENat"))
        except Exception:
            pass
    return results


def _r0189_toENat_ne_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toENat_ne_top
    # toENat c ≠ ⊤ ↔ c < ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("c"), OVar("_0")))
            results.append((rhs, "Mathlib: Cardinal_toENat_ne_top"))
        except Exception:
            pass
    return results


def _r0190_toENat_lt_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toENat_lt_top
    # toENat c < ⊤ ↔ c < ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("c"), OVar("_0")))
            results.append((rhs, "Mathlib: Cardinal_toENat_lt_top"))
        except Exception:
            pass
    return results


def _r0191_lift_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_le
    # lift.{u} a ≤ lift.{u} b ↔ a ≤ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("a"), OVar("b")))
            results.append((rhs, "Mathlib: Cardinal_lift_le"))
        except Exception:
            pass
    return results


def _r0192_lift_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_lt
    # lift.{v, u} a < lift.{v, u} b ↔ a < b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("a"), OVar("b")))
            results.append((rhs, "Mathlib: Cardinal_lift_lt"))
        except Exception:
            pass
    return results


def _r0193_lift_le_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_le_aleph0
    # lift.{v} c ≤ ℵ₀ ↔ c ≤ ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("c"), args[1]))
            results.append((rhs, "Mathlib: Cardinal_lift_le_aleph0"))
        except Exception:
            pass
    return results


def _r0194_aleph0_lt_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph0_lt_lift
    # ℵ₀ < lift.{v} c ↔ ℵ₀ < c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (args[0], OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_aleph0_lt_lift"))
        except Exception:
            pass
    return results


def _r0195_lift_lt_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_lt_aleph0
    # lift.{v} c < ℵ₀ ↔ c < ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("c"), args[1]))
            results.append((rhs, "Mathlib: Cardinal_lift_lt_aleph0"))
        except Exception:
            pass
    return results


def _r0196_lift_le_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_le_one_iff
    # lift.{v} a ≤ 1 ↔ a ≤ 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("a"), OLit(1)))
            results.append((rhs, "Mathlib: Cardinal_lift_le_one_iff"))
        except Exception:
            pass
    return results


def _r0197_one_le_lift_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.one_le_lift_iff
    # (1 : Cardinal) ≤ lift.{v} a ↔ 1 ≤ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OLit(1), OVar("a")))
            results.append((rhs, "Mathlib: Cardinal_one_le_lift_iff"))
        except Exception:
            pass
    return results


def _r0198_lift_lt_ofNat_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_lt_ofNat_iff
    # lift.{v} a < ofNat(n) ↔ a < OfNat.ofNat n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("a"), OOp("OfNat_ofNat", (OVar("n"),))))
            results.append((rhs, "Mathlib: Cardinal_lift_lt_ofNat_iff"))
        except Exception:
            pass
    return results


def _r0199_zero_lt_lift_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.zero_lt_lift_iff
    # (0 : Cardinal) < lift.{v} a ↔ 0 < a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OLit(0), OVar("a")))
            results.append((rhs, "Mathlib: Cardinal_zero_lt_lift_iff"))
        except Exception:
            pass
    return results


def _r0200_toNat_ne_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.toNat_ne_zero
    # toNat c ≠ 0 ↔ c ≠ 0 ∧ c < ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OVar("c"), OOp("<", (OOp("and", (OLit(0), OVar("c"))), OVar("_0")))))
            results.append((rhs, "Mathlib: Cardinal_toNat_ne_zero"))
        except Exception:
            pass
    return results


def _r0201_ord_lt_ord(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ord_lt_ord
    # ord c₁ < ord c₂ ↔ c₁ < c₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("c_1"), OVar("c_2")))
            results.append((rhs, "Mathlib: Cardinal_ord_lt_ord"))
        except Exception:
            pass
    return results


def _r0202_ord_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ord_pos
    # 0 < a.ord ↔ 0 < a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OLit(0), OVar("a")))
            results.append((rhs, "Mathlib: Cardinal_ord_pos"))
        except Exception:
            pass
    return results


def _r0203_omega0_le_ord(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.omega0_le_ord
    # ω ≤ a.ord ↔ ℵ₀ ≤ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("_0"), OVar("a")))
            results.append((rhs, "Mathlib: Cardinal_omega0_le_ord"))
        except Exception:
            pass
    return results


def _r0204_ord_le_omega0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ord_le_omega0
    # a.ord ≤ ω ↔ a ≤ ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("a"), OVar("_0")))
            results.append((rhs, "Mathlib: Cardinal_ord_le_omega0"))
        except Exception:
            pass
    return results


def _r0205_ord_lt_omega0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.ord_lt_omega0
    # a.ord < ω ↔ a < ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("a"), OVar("_0")))
            results.append((rhs, "Mathlib: Cardinal_ord_lt_omega0"))
        except Exception:
            pass
    return results


def _r0206_omega0_lt_ord(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.omega0_lt_ord
    # ω < a.ord ↔ ℵ₀ < a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("_0"), OVar("a")))
            results.append((rhs, "Mathlib: Cardinal_omega0_lt_ord"))
        except Exception:
            pass
    return results


def _r0207_mk_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_inv
    # #↥(s⁻¹) = #s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_sinv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_s")
            results.append((rhs, "Mathlib: Cardinal_mk_inv"))
    except Exception:
        pass
    return results


def _r0208_mk_smul_set(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_smul_set
    # #↥(a • s) = #s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_a_s")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_s")
            results.append((rhs, "Mathlib: Cardinal_mk_smul_set"))
    except Exception:
        pass
    return results


def _r0209_pow_four(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.pow_four
    # #R ^ 4 = #R
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_pow_four"))
        except Exception:
            pass
    return results


def _r0210_mk_quaternionAlgebra(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_quaternionAlgebra
    # #(ℍ[R,c₁,c₂,c₃]) = #R ^ 4
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_R_c_1_c_2_c_3")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OVar("hash_R"), OLit(4)))
            results.append((rhs, "Mathlib: Cardinal_mk_quaternionAlgebra"))
    except Exception:
        pass
    return results


def _r0211_mk_quaternionAlgebra_of_infinite(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_quaternionAlgebra_of_infinite
    # #(ℍ[R,c₁,c₂,c₃]) = #R
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_R_c_1_c_2_c_3")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_R")
            results.append((rhs, "Mathlib: Cardinal_mk_quaternionAlgebra_of_infinite"))
    except Exception:
        pass
    return results


def _r0212_mk_univ_quaternionAlgebra(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_univ_quaternionAlgebra
    # #(Set.univ : Set ℍ[R,c₁,c₂,c₃]) = #R ^ 4
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Set_univ_colon_Set_R_c_1_c_2_c_3")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OVar("hash_R"), OLit(4)))
            results.append((rhs, "Mathlib: Cardinal_mk_univ_quaternionAlgebra"))
    except Exception:
        pass
    return results


def _r0213_mk_univ_quaternionAlgebra_of_infinite(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_univ_quaternionAlgebra_of_infinite
    # #(Set.univ : Set ℍ[R,c₁,c₂,c₃]) = #R
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Set_univ_colon_Set_R_c_1_c_2_c_3")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_R")
            results.append((rhs, "Mathlib: Cardinal_mk_univ_quaternionAlgebra_of_infinite"))
    except Exception:
        pass
    return results


def _r0214_mk_complex(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_complex
    # #ℂ = 𝔠
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("_unknown")
            results.append((rhs, "Mathlib: Cardinal_mk_complex"))
    except Exception:
        pass
    return results


def _r0215_mk_univ_complex(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_univ_complex
    # #(Set.univ : Set ℂ) = 𝔠
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Set_univ_colon_Set")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("_unknown")
            results.append((rhs, "Mathlib: Cardinal_mk_univ_complex"))
    except Exception:
        pass
    return results


def _r0216_cantorFunctionAux_true(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.cantorFunctionAux_true
    # cantorFunctionAux c f n = c ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cantorFunctionAux", 3)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], args[2]))
            results.append((rhs, "Mathlib: Cardinal_cantorFunctionAux_true"))
        except Exception:
            pass
    return results


def _r0217_cantorFunctionAux_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.cantorFunctionAux_eq
    # cantorFunctionAux c f n = cantorFunctionAux c g n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cantorFunctionAux", 3)
    if args is not None:
        try:
            rhs = OOp("cantorFunctionAux", (args[0], OVar("g"), args[2],))
            results.append((rhs, "Mathlib: Cardinal_cantorFunctionAux_eq"))
        except Exception:
            pass
    return results


def _r0218_cantorFunctionAux_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.cantorFunctionAux_zero
    # cantorFunctionAux c f 0 = cond (f 0) 1 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cantorFunctionAux", 3)
    if args is not None:
        try:
            rhs = OOp("cond", (OOp("f", (OLit(0),)), OLit(1), OLit(0),))
            results.append((rhs, "Mathlib: Cardinal_cantorFunctionAux_zero"))
        except Exception:
            pass
    return results


def _r0219_cantorFunctionAux_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.cantorFunctionAux_succ
    # (fun n => cantorFunctionAux c f (n + 1)) = fun n =>       c * cantorFunctionAux c (fun n => f (n + 1)) n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun", 6)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("fun", (args[0], args[1], args[3],)), OOp("cantorFunctionAux", (args[3], OOp("fun", (args[0], args[1], args[4], OOp("+", (args[0], OLit(1))),)), args[0],))))
            results.append((rhs, "Mathlib: Cardinal_cantorFunctionAux_succ"))
        except Exception:
            pass
    return results


def _r0220_cantorFunction_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.cantorFunction_succ
    # cantorFunction c f = cond (f 0) 1 0 + c * cantorFunction c fun n => f (n + 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cantorFunction", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("cond", (OOp("f", (OLit(0),)), OLit(1), OLit(0),)), OOp("*", (args[0], OOp("cantorFunction", (args[0], OVar("fun"), OVar("n"), OVar("eq_gt"), args[1], OOp("+", (OVar("n"), OLit(1))),))))))
            results.append((rhs, "Mathlib: Cardinal_cantorFunction_succ"))
        except Exception:
            pass
    return results


def _r0221_mk_real(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_real
    # #ℝ = 𝔠
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("_unknown")
            results.append((rhs, "Mathlib: Cardinal_mk_real"))
    except Exception:
        pass
    return results


def _r0222_mk_univ_real(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_univ_real
    # #(Set.univ : Set ℝ) = 𝔠
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Set_univ_colon_Set")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("_unknown")
            results.append((rhs, "Mathlib: Cardinal_mk_univ_real"))
    except Exception:
        pass
    return results


def _r0223_mk_Ioi_real(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_Ioi_real
    # #(Ioi a) = 𝔠
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Ioi_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("_unknown")
            results.append((rhs, "Mathlib: Cardinal_mk_Ioi_real"))
    except Exception:
        pass
    return results


def _r0224_mk_Ici_real(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_Ici_real
    # #(Ici a) = 𝔠
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Ici_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("_unknown")
            results.append((rhs, "Mathlib: Cardinal_mk_Ici_real"))
    except Exception:
        pass
    return results


def _r0225_mk_Iio_real(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_Iio_real
    # #(Iio a) = 𝔠
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Iio_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("_unknown")
            results.append((rhs, "Mathlib: Cardinal_mk_Iio_real"))
    except Exception:
        pass
    return results


def _r0226_mk_Iic_real(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_Iic_real
    # #(Iic a) = 𝔠
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Iic_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("_unknown")
            results.append((rhs, "Mathlib: Cardinal_mk_Iic_real"))
    except Exception:
        pass
    return results


def _r0227_mk_Ioo_real(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_Ioo_real
    # #(Ioo a b) = 𝔠
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Ioo_a_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("_unknown")
            results.append((rhs, "Mathlib: Cardinal_mk_Ioo_real"))
    except Exception:
        pass
    return results


def _r0228_mk_Ico_real(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_Ico_real
    # #(Ico a b) = 𝔠
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Ico_a_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("_unknown")
            results.append((rhs, "Mathlib: Cardinal_mk_Ico_real"))
    except Exception:
        pass
    return results


def _r0229_mk_Icc_real(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_Icc_real
    # #(Icc a b) = 𝔠
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Icc_a_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("_unknown")
            results.append((rhs, "Mathlib: Cardinal_mk_Icc_real"))
    except Exception:
        pass
    return results


def _r0230_mk_Ioc_real(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_Ioc_real
    # #(Ioc a b) = 𝔠
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Ioc_a_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("_unknown")
            results.append((rhs, "Mathlib: Cardinal_mk_Ioc_real"))
    except Exception:
        pass
    return results


def _r0231_mkRat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mkRat
    # #ℚ = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("_0")
            results.append((rhs, "Mathlib: Cardinal_mkRat"))
    except Exception:
        pass
    return results


def _r0232_mk_fractionRing(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_fractionRing
    # #(FractionRing R) = #R
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_FractionRing_R")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_R")
            results.append((rhs, "Mathlib: Cardinal_mk_fractionRing"))
    except Exception:
        pass
    return results


def _r0233_card_preOmega(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.card_preOmega
    # (preOmega o).card = preAleph o
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("preOmega_o_card")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("preAleph", (OVar("o"),))
            results.append((rhs, "Mathlib: Ordinal_card_preOmega"))
    except Exception:
        pass
    return results


def _r0234_mk_cardinal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_cardinal
    # #Cardinal = univ.{u, u + 1}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Cardinal")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("univ_u_u_plus_1")
            results.append((rhs, "Mathlib: Cardinal_mk_cardinal"))
    except Exception:
        pass
    return results


def _r0235_preAleph_max(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.preAleph_max
    # preAleph (max o₁ o₂) = max (preAleph o₁) (preAleph o₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preAleph", 1)
    if args is not None:
        try:
            rhs = OOp("max", (OOp("preAleph", (OVar("o_1"),)), OOp("preAleph", (OVar("o_2"),)),))
            results.append((rhs, "Mathlib: Cardinal_preAleph_max"))
        except Exception:
            pass
    return results


def _r0236_preAleph_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.preAleph_zero
    # preAleph 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preAleph", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Cardinal_preAleph_zero"))
        except Exception:
            pass
    return results


def _r0237_preAleph_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.preAleph_succ
    # preAleph (succ o) = succ (preAleph o)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preAleph", 1)
    if args is not None:
        try:
            rhs = OOp("succ", (OOp("preAleph", (OVar("o"),)),))
            results.append((rhs, "Mathlib: Cardinal_preAleph_succ"))
        except Exception:
            pass
    return results


def _r0238_preAleph_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.preAleph_nat
    # preAleph n = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preAleph", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_preAleph_nat"))
        except Exception:
            pass
    return results


def _r0239_lift_preAleph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_preAleph
    # lift.{v} (preAleph o) = preAleph (Ordinal.lift.{v} o)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("preAleph", (OOp("Ordinal_lift_v", (OVar("o"),)),))
            results.append((rhs, "Mathlib: Cardinal_lift_preAleph"))
        except Exception:
            pass
    return results


def _r0240_lift_preOmega(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.lift_preOmega
    # Ordinal.lift.{v} (preOmega o) = preOmega (Ordinal.lift.{v} o)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ordinal_lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("preOmega", (OOp("Ordinal_lift_v", (OVar("o"),)),))
            results.append((rhs, "Mathlib: Ordinal_lift_preOmega"))
        except Exception:
            pass
    return results


def _r0241_preAleph_limit(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.preAleph_limit
    # preAleph o = ⨆ a : Iio o, preAleph a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preAleph", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("a"), OVar("colon"), OVar("Iio"), args[0], OVar("preAleph"), OVar("a"),))
            results.append((rhs, "Mathlib: Cardinal_preAleph_limit"))
        except Exception:
            pass
    return results


def _r0242_aleph_eq_preAleph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph_eq_preAleph
    # ℵ_ o = preAleph (ω + o)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OOp("preAleph", (OOp("+", (OVar("omega"), args[0])),))
            results.append((rhs, "Mathlib: Cardinal_aleph_eq_preAleph"))
        except Exception:
            pass
    return results


def _r0243_card_omega(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.card_omega
    # (ω_ o).card = ℵ_ o
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("omega_o_card")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_unknown", (OVar("o"),))
            results.append((rhs, "Mathlib: Ordinal_card_omega"))
    except Exception:
        pass
    return results


def _r0244_aleph_max(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph_max
    # ℵ_ (max o₁ o₂) = max (ℵ_ o₁) (ℵ_ o₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OOp("max", (OOp("_unknown", (OVar("o_1"),)), OOp("_unknown", (OVar("o_2"),)),))
            results.append((rhs, "Mathlib: Cardinal_aleph_max"))
        except Exception:
            pass
    return results


def _r0245_succ_aleph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.succ_aleph
    # succ (ℵ_ o) = ℵ_ (o + 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OOp("+", (OVar("o"), OLit(1))),))
            results.append((rhs, "Mathlib: Cardinal_succ_aleph"))
        except Exception:
            pass
    return results


def _r0246_aleph_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph_succ
    # ℵ_ (succ o) = succ (ℵ_ o)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OOp("succ", (OOp("_unknown", (OVar("o"),)),))
            results.append((rhs, "Mathlib: Cardinal_aleph_succ"))
        except Exception:
            pass
    return results


def _r0247_aleph_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph_zero
    # ℵ_ 0 = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OVar("_0")
            results.append((rhs, "Mathlib: Cardinal_aleph_zero"))
        except Exception:
            pass
    return results


def _r0248_lift_omega(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.lift_omega
    # Ordinal.lift.{v} (ω_ o) = ω_ (Ordinal.lift.{v} o)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ordinal_lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("omega", (OOp("Ordinal_lift_v", (OVar("o"),)),))
            results.append((rhs, "Mathlib: Ordinal_lift_omega"))
        except Exception:
            pass
    return results


def _r0249_aleph_limit(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph_limit
    # ℵ_ o = ⨆ a : Iio o, ℵ_ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("a"), OVar("colon"), OVar("Iio"), args[0], OVar("_unknown"), OVar("a"),))
            results.append((rhs, "Mathlib: Cardinal_aleph_limit"))
        except Exception:
            pass
    return results


def _r0250_aleph_toNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph_toNat
    # toNat (ℵ_ o) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toNat", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Cardinal_aleph_toNat"))
        except Exception:
            pass
    return results


def _r0251_range_aleph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.range_aleph
    # range aleph = Set.Ici ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OOp("Set_Ici", (OVar("_0"),))
            results.append((rhs, "Mathlib: Cardinal_range_aleph"))
        except Exception:
            pass
    return results


def _r0252_succ_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.succ_aleph0
    # succ ℵ₀ = ℵ₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 1)
    if args is not None:
        try:
            rhs = OVar("_1")
            results.append((rhs, "Mathlib: Cardinal_succ_aleph0"))
        except Exception:
            pass
    return results


def _r0253_preBeth_add_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.preBeth_add_one
    # preBeth (o + 1) = 2 ^ preBeth o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preBeth", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OLit(2), OOp("preBeth", (OVar("o"),))))
            results.append((rhs, "Mathlib: Cardinal_preBeth_add_one"))
        except Exception:
            pass
    return results


def _r0254_preBeth_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.preBeth_succ
    # preBeth (succ o) = 2 ^ preBeth o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preBeth", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OLit(2), OOp("preBeth", (OVar("o"),))))
            results.append((rhs, "Mathlib: Cardinal_preBeth_succ"))
        except Exception:
            pass
    return results


def _r0255_preBeth_limit(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.preBeth_limit
    # preBeth o = ⨆ a : Iio o, preBeth a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preBeth", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("a"), OVar("colon"), OVar("Iio"), args[0], OVar("preBeth"), OVar("a"),))
            results.append((rhs, "Mathlib: Cardinal_preBeth_limit"))
        except Exception:
            pass
    return results


def _r0256_preBeth_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.preBeth_nat
    # ∀ n : ℕ, preBeth n = (2 ^ ·)^[n] (0 : ℕ)   | 0 =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preBeth", 1)
    if args is not None:
        try:
            rhs = OOp("_2_pow_pow_n", (OOp("_0", (OVar("colon"), OVar("_unknown"),)), OVar("pipe"), OLit(0), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: Cardinal_preBeth_nat"))
        except Exception:
            pass
    return results


def _r0257_preBeth_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.preBeth_one
    # preBeth 1 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preBeth", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Cardinal_preBeth_one"))
        except Exception:
            pass
    return results


def _r0258_preBeth_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.preBeth_eq_zero
    # preBeth o = 0 ↔ o = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preBeth", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: Cardinal_preBeth_eq_zero"))
        except Exception:
            pass
    return results


def _r0259_lift_preBeth(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_preBeth
    # lift.{v} (preBeth o) = preBeth (Ordinal.lift.{v} o)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("preBeth", (OOp("Ordinal_lift_v", (OVar("o"),)),))
            results.append((rhs, "Mathlib: Cardinal_lift_preBeth"))
        except Exception:
            pass
    return results


def _r0260_beth_eq_preBeth(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.beth_eq_preBeth
    # beth o = preBeth (ω + o)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "beth", 1)
    if args is not None:
        try:
            rhs = OOp("preBeth", (OOp("+", (OVar("omega"), args[0])),))
            results.append((rhs, "Mathlib: Cardinal_beth_eq_preBeth"))
        except Exception:
            pass
    return results


def _r0261_beth_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.beth_succ
    # ℶ_ (succ o) = 2 ^ ℶ_ o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OLit(2), OOp("_unknown", (OVar("o"),))))
            results.append((rhs, "Mathlib: Cardinal_beth_succ"))
        except Exception:
            pass
    return results


def _r0262_beth_limit(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.beth_limit
    # ℶ_ o = ⨆ a : Iio o, ℶ_ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("a"), OVar("colon"), OVar("Iio"), args[0], OVar("_unknown"), OVar("a"),))
            results.append((rhs, "Mathlib: Cardinal_beth_limit"))
        except Exception:
            pass
    return results


def _r0263_lift_beth(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_beth
    # lift.{v} (ℶ_ o) = ℶ_ (Ordinal.lift.{v} o)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OOp("Ordinal_lift_v", (OVar("o"),)),))
            results.append((rhs, "Mathlib: Cardinal_lift_beth"))
        except Exception:
            pass
    return results


def _r0264_aleph_one_eq_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph_one_eq_lift
    # ℵ₁ = lift.{v} c ↔ ℵ₁ = c
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("lift_v", (OVar("c"),)), OVar("_1"))), OVar("c")))
            results.append((rhs, "Mathlib: Cardinal_aleph_one_eq_lift"))
    except Exception:
        pass
    return results


def _r0265_lift_eq_aleph_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_eq_aleph_one
    # lift.{v} c = ℵ₁ ↔ c = ℵ₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("_1"), args[0])), OVar("_1")))
            results.append((rhs, "Mathlib: Cardinal_lift_eq_aleph_one"))
        except Exception:
            pass
    return results


def _r0266_mul_eq_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mul_eq_self
    # c * c = c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Cardinal_mul_eq_self"))
        except Exception:
            pass
    return results


def _r0267_mul_eq_max(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mul_eq_max
    # a * b = max a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("max", (args[0], args[1],))
            results.append((rhs, "Mathlib: Cardinal_mul_eq_max"))
        except Exception:
            pass
    return results


def _r0268_mul_mk_eq_max(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mul_mk_eq_max
    # #α * #β = max #α #β
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("max", (args[0], args[1],))
            results.append((rhs, "Mathlib: Cardinal_mul_mk_eq_max"))
        except Exception:
            pass
    return results


def _r0269_mk_mul_aleph0_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_mul_aleph0_eq
    # #α * ℵ₀ = #α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_mk_mul_aleph0_eq"))
        except Exception:
            pass
    return results


def _r0270_aleph0_mul_aleph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph0_mul_aleph
    # ℵ₀ * ℵ_ o = ℵ_ o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("o"),))
            results.append((rhs, "Mathlib: Cardinal_aleph0_mul_aleph"))
        except Exception:
            pass
    return results


def _r0271_mul_eq_max_of_aleph0_le_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mul_eq_max_of_aleph0_le_left
    # a * b = max a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("max", (args[0], args[1],))
            results.append((rhs, "Mathlib: Cardinal_mul_eq_max_of_aleph0_le_left"))
        except Exception:
            pass
    return results


def _r0272_mul_eq_max_of_aleph0_le_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mul_eq_max_of_aleph0_le_right
    # a * b = max a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("max", (args[0], args[1],))
            results.append((rhs, "Mathlib: Cardinal_mul_eq_max_of_aleph0_le_right"))
        except Exception:
            pass
    return results


def _r0273_mul_eq_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mul_eq_left
    # a * b = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_mul_eq_left"))
        except Exception:
            pass
    return results


def _r0274_mul_eq_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mul_eq_right
    # a * b = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Cardinal_mul_eq_right"))
        except Exception:
            pass
    return results


def _r0275_mul_eq_left_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mul_eq_left_iff
    # a * b = a ↔ max ℵ₀ b ≤ a ∧ b ≠ 0 ∨ b = 1 ∨ a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("!=", (OOp("<=", (OOp("iff", (args[0], OOp("max", (OVar("_0"), args[1],)))), OOp("and", (args[0], args[1])))), OOp("or", (OLit(0), args[1])))), OOp("==", (OOp("or", (OLit(1), args[0])), OLit(0)))))
            results.append((rhs, "Mathlib: Cardinal_mul_eq_left_iff"))
        except Exception:
            pass
    return results


def _r0276_mk_preimage_down(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_preimage_down
    # #(ULift.down.{v} ⁻¹' s) = lift.{v} (#s)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_ULift_down_v_inv_prime_s")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("lift_v", (OVar("hash_s"),))
            results.append((rhs, "Mathlib: Cardinal_mk_preimage_down"))
    except Exception:
        pass
    return results


def _r0277_lift_mk_shrink(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_mk_shrink
    # Cardinal.lift.{max u w} #(Shrink.{v} α) = Cardinal.lift.{max v w} #α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Cardinal_lift_max_u_w", 1)
    if args is not None:
        try:
            rhs = OOp("Cardinal_lift_max_v_w", (OVar("hash_a"),))
            results.append((rhs, "Mathlib: Cardinal_lift_mk_shrink"))
        except Exception:
            pass
    return results


def _r0278_prod_eq_of_fintype(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.prod_eq_of_fintype
    # prod f = Cardinal.lift.{u} (∏ i, f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prod", 1)
    if args is not None:
        try:
            rhs = OOp("Cardinal_lift_u", (OOp("_unknown", (OVar("i"), args[0], OVar("i"),)),))
            results.append((rhs, "Mathlib: Cardinal_prod_eq_of_fintype"))
        except Exception:
            pass
    return results


def _r0279_sInf_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.sInf_eq_zero_iff
    # sInf s = 0 ↔ s = ∅ ∨ ∃ a ∈ s, a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sInf", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OOp("==", (OOp("or", (OVar("empty"), OOp("in", (OOp("exists", (OVar("a"),)), OOp("s", (OVar("a"),)))))), OLit(0)))))
            results.append((rhs, "Mathlib: Cardinal_sInf_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0280_iInf_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.iInf_eq_zero_iff
    # (⨅ i, f i) = 0 ↔ IsEmpty ι ∨ ∃ i, f i = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OOp("iff", (OLit(0), OOp("IsEmpty", (args[2],)))), OOp("exists", (args[2], args[1], args[2],)))), OLit(0)))
            results.append((rhs, "Mathlib: Cardinal_iInf_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0281_iSup_of_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.iSup_of_empty
    # iSup f = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iSup", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Cardinal_iSup_of_empty"))
        except Exception:
            pass
    return results


def _r0282_lift_sInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_sInf
    # lift.{u, v} (sInf s) = sInf (lift.{u, v} '' s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_u_v", 1)
    if args is not None:
        try:
            rhs = OOp("sInf", (OOp("lift_u_v", (OVar("prime_prime"), OVar("s"),)),))
            results.append((rhs, "Mathlib: Cardinal_lift_sInf"))
        except Exception:
            pass
    return results


def _r0283_lift_iInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_iInf
    # lift.{u, v} (iInf f) = ⨅ i, lift.{u, v} (f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_u_v", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), OVar("lift_u_v"), OOp("f", (OVar("i"),)),))
            results.append((rhs, "Mathlib: Cardinal_lift_iInf"))
        except Exception:
            pass
    return results


def _r0284_lift_sSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_sSup
    # lift.{u} (sSup s) = sSup (lift.{u} '' s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_u", 1)
    if args is not None:
        try:
            rhs = OOp("sSup", (OOp("lift_u", (OVar("prime_prime"), OVar("s"),)),))
            results.append((rhs, "Mathlib: Cardinal_lift_sSup"))
        except Exception:
            pass
    return results


def _r0285_lift_iSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_iSup
    # lift.{u} (iSup f) = ⨆ i, lift.{u} (f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_u", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), OVar("lift_u"), OOp("f", (OVar("i"),)),))
            results.append((rhs, "Mathlib: Cardinal_lift_iSup"))
        except Exception:
            pass
    return results


def _r0286_mk_finset_of_fintype(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_finset_of_fintype
    # #(Finset α) = 2 ^ Fintype.card α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Finset_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OLit(2), OOp("Fintype_card", (OVar("a"),))))
            results.append((rhs, "Mathlib: Cardinal_mk_finset_of_fintype"))
    except Exception:
        pass
    return results


def _r0287_nat_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.nat_succ
    # (n.succ : Cardinal) = succ ↑n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n_succ", 2)
    if args is not None:
        try:
            rhs = OOp("succ", (OVar("n"),))
            results.append((rhs, "Mathlib: Cardinal_nat_succ"))
        except Exception:
            pass
    return results


def _r0288_succ_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.succ_natCast
    # Order.succ (n : Cardinal) = n + 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Order_succ", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("n"), OLit(1)))
            results.append((rhs, "Mathlib: Cardinal_succ_natCast"))
        except Exception:
            pass
    return results


def _r0289_succ_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.succ_zero
    # succ (0 : Cardinal) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Cardinal_succ_zero"))
        except Exception:
            pass
    return results


def _r0290_exists_finset_eq_card(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.exists_finset_eq_card
    # ∃ s : Finset α, n = s.card
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 5)
    if args is not None:
        try:
            rhs = OVar("s_card")
            results.append((rhs, "Mathlib: Cardinal_exists_finset_eq_card"))
        except Exception:
            pass
    return results


def _r0291_lt_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lt_one_iff
    # c < 1 ↔ c = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Cardinal_lt_one_iff"))
        except Exception:
            pass
    return results


def _r0292_le_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.le_one_iff
    # c ≤ 1 ↔ c = 0 ∨ c = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OLit(0), args[0])), OLit(1)))
            results.append((rhs, "Mathlib: Cardinal_le_one_iff"))
        except Exception:
            pass
    return results


def _r0293_succ_eq_of_lt_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.succ_eq_of_lt_aleph0
    # Order.succ c = c + 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Order_succ", 1)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], OLit(1)))
            results.append((rhs, "Mathlib: Cardinal_succ_eq_of_lt_aleph0"))
        except Exception:
            pass
    return results


def _r0294_not_isSuccLimit_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.not_isSuccLimit_natCast
    # (n : ℕ) → ¬ IsSuccLimit (n : Cardinal.{u})   | 0, e => e.1 isMin_bot   | Nat.succ n, e => Order.not_isSuccPrelimit_succ 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "not", 5)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("e_1"), OVar("isMin_bot"), args[2], OVar("Nat_succ"), OVar("n"), args[4], OVar("eq_gt"), OVar("Order_not_isSuccPrelimit_succ"), OVar("_unknown"), OVar("nat_succ_n_e_2_theorem"), OVar("not_isSuccLimit_of_lt_aleph0"), OVar("c_colon_Cardinal"), OOp("<", (OOp("h", (OVar("colon"), OVar("c"),)), args[3])), OVar("colon"), OOp("not", (OVar("_"),)), args[0], OVar("c"),))
            results.append((rhs, "Mathlib: Cardinal_not_isSuccLimit_natCast"))
        except Exception:
            pass
    return results


def _r0295_exists_eq_natCast_of_iSup_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.exists_eq_natCast_of_iSup_eq
    # ∃ i, f i = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 3)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Cardinal_exists_eq_natCast_of_iSup_eq"))
        except Exception:
            pass
    return results


def _r0296_nsmul_lt_aleph0_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.nsmul_lt_aleph0_iff
    # ∀ {n : ℕ}, n • a < ℵ₀ ↔ n = 0 ∨ a < ℵ₀   | 0 =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("or", (OLit(0), OVar("a"))), OOp("_0", (OVar("pipe"), OLit(0), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: Cardinal_nsmul_lt_aleph0_iff"))
        except Exception:
            pass
    return results


def _r0297_mul_lt_aleph0_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mul_lt_aleph0_iff
    # a * b < ℵ₀ ↔ a = 0 ∨ b = 0 ∨ a < ℵ₀ ∧ b < ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OLit(0), OVar("b"))), OOp("<", (OOp("or", (OLit(0), OVar("a"))), OOp("<", (OOp("and", (OVar("_0"), OVar("b"))), OVar("_0")))))))
            results.append((rhs, "Mathlib: Cardinal_mul_lt_aleph0_iff"))
        except Exception:
            pass
    return results


def _r0298_eq_one_iff_unique(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.eq_one_iff_unique
    # #α = 1 ↔ Subsingleton α ∧ Nonempty α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("and", (OOp("iff", (OLit(1), OOp("Subsingleton", (OVar("a"),)))), OOp("Nonempty", (OVar("a"),))))
            results.append((rhs, "Mathlib: Cardinal_eq_one_iff_unique"))
    except Exception:
        pass
    return results


def _r0299_mk_eq_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_eq_aleph0
    # #α = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("_0")
            results.append((rhs, "Mathlib: Cardinal_mk_eq_aleph0"))
    except Exception:
        pass
    return results


def _r0300_mk_denumerable(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_denumerable
    # #α = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("_0")
            results.append((rhs, "Mathlib: Cardinal_mk_denumerable"))
    except Exception:
        pass
    return results


def _r0301_aleph0_add_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph0_add_aleph0
    # ℵ₀ + ℵ₀ = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Cardinal_aleph0_add_aleph0"))
        except Exception:
            pass
    return results


def _r0302_nat_mul_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.nat_mul_aleph0
    # ↑n * ℵ₀ = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Cardinal_nat_mul_aleph0"))
        except Exception:
            pass
    return results


def _r0303_aleph0_mul_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph0_mul_nat
    # ℵ₀ * n = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_aleph0_mul_nat"))
        except Exception:
            pass
    return results


def _r0304_aleph0_add_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph0_add_nat
    # ℵ₀ + n = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_aleph0_add_nat"))
        except Exception:
            pass
    return results


def _r0305_mk_int(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_int
    # #ℤ = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("_0")
            results.append((rhs, "Mathlib: Cardinal_mk_int"))
    except Exception:
        pass
    return results


def _r0306_mk_pnat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_pnat
    # #ℕ+ = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_plus")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("_0")
            results.append((rhs, "Mathlib: Cardinal_mk_pnat"))
    except Exception:
        pass
    return results


def _r0307_mk_additive(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_additive
    # #(Additive α) = #α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Additive_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_a")
            results.append((rhs, "Mathlib: Cardinal_mk_additive"))
    except Exception:
        pass
    return results


def _r0308_mk_vector(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_vector
    # #(List.Vector α n) = #α ^ n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_List_Vector_a_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OVar("hash_a"), OVar("n")))
            results.append((rhs, "Mathlib: Cardinal_mk_vector"))
    except Exception:
        pass
    return results


def _r0309_sum_zero_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.sum_zero_pow
    # sum (fun n ↦ (0 : Cardinal) ^ n) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sum", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Cardinal_sum_zero_pow"))
        except Exception:
            pass
    return results


def _r0310_mk_emptyCollection(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_emptyCollection
    # #(∅ : Set α) = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_empty_colon_Set_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Cardinal_mk_emptyCollection"))
    except Exception:
        pass
    return results


def _r0311_mk_set_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_set_eq_zero_iff
    # #s = 0 ↔ s = ∅
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_s")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("s"))), OVar("empty")))
            results.append((rhs, "Mathlib: Cardinal_mk_set_eq_zero_iff"))
    except Exception:
        pass
    return results


def _r0312_mk_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_univ
    # #(@univ α) = #α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_at_univ_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_a")
            results.append((rhs, "Mathlib: Cardinal_mk_univ"))
    except Exception:
        pass
    return results


def _r0313_mk_range_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_range_eq
    # #(range f) = #α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_range_f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_a")
            results.append((rhs, "Mathlib: Cardinal_mk_range_eq"))
    except Exception:
        pass
    return results


def _r0314_mk_range_eq_of_injective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_range_eq_of_injective
    # lift.{u} #(range f) = lift.{v} #α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_u", 1)
    if args is not None:
        try:
            rhs = OOp("lift_v", (OVar("hash_a"),))
            results.append((rhs, "Mathlib: Cardinal_mk_range_eq_of_injective"))
        except Exception:
            pass
    return results


def _r0315_mk_range_eq_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_range_eq_lift
    # lift.{max u w} #(range f) = lift.{max v w} #α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_max_u_w", 1)
    if args is not None:
        try:
            rhs = OOp("lift_max_v_w", (OVar("hash_a"),))
            results.append((rhs, "Mathlib: Cardinal_mk_range_eq_lift"))
        except Exception:
            pass
    return results


def _r0316_mk_image_eq_of_injOn(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_image_eq_of_injOn
    # #(f '' s) = #s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_f_prime_prime_s")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_s")
            results.append((rhs, "Mathlib: Cardinal_mk_image_eq_of_injOn"))
    except Exception:
        pass
    return results


def _r0317_mk_image_eq_of_injOn_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_image_eq_of_injOn_lift
    # lift.{u} #(f '' s) = lift.{v} #s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_u", 1)
    if args is not None:
        try:
            rhs = OOp("lift_v", (OVar("hash_s"),))
            results.append((rhs, "Mathlib: Cardinal_mk_image_eq_of_injOn_lift"))
        except Exception:
            pass
    return results


def _r0318_mk_image_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_image_eq
    # #(f '' s) = #s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_f_prime_prime_s")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_s")
            results.append((rhs, "Mathlib: Cardinal_mk_image_eq"))
    except Exception:
        pass
    return results


def _r0319_mk_image_eq_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_image_eq_lift
    # lift.{u} #(f '' s) = lift.{v} #s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_u", 1)
    if args is not None:
        try:
            rhs = OOp("lift_v", (OVar("hash_s"),))
            results.append((rhs, "Mathlib: Cardinal_mk_image_eq_lift"))
        except Exception:
            pass
    return results


def _r0320_mk_image_embedding_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_image_embedding_lift
    # lift.{u} #(f '' s) = lift.{v} #s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_u", 1)
    if args is not None:
        try:
            rhs = OOp("lift_v", (OVar("hash_s"),))
            results.append((rhs, "Mathlib: Cardinal_mk_image_embedding_lift"))
        except Exception:
            pass
    return results


def _r0321_mk_image_embedding(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_image_embedding
    # #(f '' s) = #s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_f_prime_prime_s")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_s")
            results.append((rhs, "Mathlib: Cardinal_mk_image_embedding"))
    except Exception:
        pass
    return results


def _r0322_mk_iUnion_le_sum_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_iUnion_le_sum_mk
    # #(⋃ i, f i) ≤ sum fun i => #(f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("hash_f_i"),))
            results.append((rhs, "Mathlib: Cardinal_mk_iUnion_le_sum_mk"))
        except Exception:
            pass
    return results


def _r0323_mk_iUnion_le_sum_mk_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_iUnion_le_sum_mk_lift
    # lift.{v} #(⋃ i, f i) ≤ sum fun i => #(f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("hash_f_i"),))
            results.append((rhs, "Mathlib: Cardinal_mk_iUnion_le_sum_mk_lift"))
        except Exception:
            pass
    return results


def _r0324_mk_iUnion_eq_sum_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_iUnion_eq_sum_mk
    # #(⋃ i, f i) = sum fun i => #(f i)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_i_f_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("sum", (OVar("fun"), OVar("i"), OVar("eq_gt"), OVar("hash_f_i"),))
            results.append((rhs, "Mathlib: Cardinal_mk_iUnion_eq_sum_mk"))
    except Exception:
        pass
    return results


def _r0325_mk_iUnion_eq_sum_mk_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_iUnion_eq_sum_mk_lift
    # lift.{v} #(⋃ i, f i) = sum fun i => #(f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("sum", (OVar("fun"), OVar("i"), OVar("eq_gt"), OVar("hash_f_i"),))
            results.append((rhs, "Mathlib: Cardinal_mk_iUnion_eq_sum_mk_lift"))
        except Exception:
            pass
    return results


def _r0326_mk_set_eq_nat_iff_finset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_set_eq_nat_iff_finset
    # #s = n ↔ ∃ t : Finset α, (t : Set α) = s ∧ t.card = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_s")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("n"), OOp("exists", (OVar("t"), OVar("colon"), OVar("Finset"), OVar("a"), OOp("t", (OVar("colon"), OVar("Set"), OVar("a"),)),)))), OOp("==", (OOp("and", (OVar("s"), OVar("t_card"))), OVar("n")))))
            results.append((rhs, "Mathlib: Cardinal_mk_set_eq_nat_iff_finset"))
    except Exception:
        pass
    return results


def _r0327_mk_eq_nat_iff_finset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_eq_nat_iff_finset
    # #α = n ↔ ∃ t : Finset α, (t : Set α) = univ ∧ t.card = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("n"), OOp("exists", (OVar("t"), OVar("colon"), OVar("Finset"), OVar("a"), OOp("t", (OVar("colon"), OVar("Set"), OVar("a"),)),)))), OOp("==", (OOp("and", (OVar("univ"), OVar("t_card"))), OVar("n")))))
            results.append((rhs, "Mathlib: Cardinal_mk_eq_nat_iff_finset"))
    except Exception:
        pass
    return results


def _r0328_mk_eq_nat_iff_fintype(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_eq_nat_iff_fintype
    # #α = n ↔ ∃ h : Fintype α, @Fintype.card α h = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("n"), OOp("exists", (OVar("h"), OVar("colon"), OVar("Fintype"), OVar("a"), OVar("at_Fintype_card"), OVar("a"), OVar("h"),)))), OVar("n")))
            results.append((rhs, "Mathlib: Cardinal_mk_eq_nat_iff_fintype"))
    except Exception:
        pass
    return results


def _r0329_mk_set_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_set_eq_one_iff
    # #s = 1 ↔ ∃ x, s = {x}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_s")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(1), OOp("exists", (OVar("x"), OVar("s"),)))), OVar("x")))
            results.append((rhs, "Mathlib: Cardinal_mk_set_eq_one_iff"))
    except Exception:
        pass
    return results


def _r0330_mk_union_add_mk_inter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_union_add_mk_inter
    # #(S ∪ T : Set α) + #(S ∩ T : Set α) = #S + #T
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("hash_S"), OVar("hash_T")))
            results.append((rhs, "Mathlib: Cardinal_mk_union_add_mk_inter"))
        except Exception:
            pass
    return results


def _r0331_mk_union_of_disjoint(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_union_of_disjoint
    # #(S ∪ T : Set α) = #S + #T
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_S_union_T_colon_Set_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("hash_S"), OVar("hash_T")))
            results.append((rhs, "Mathlib: Cardinal_mk_union_of_disjoint"))
    except Exception:
        pass
    return results


def _r0332_mk_insert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_insert
    # #(insert a s : Set α) = #s + 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_insert_a_s_colon_Set_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("hash_s"), OLit(1)))
            results.append((rhs, "Mathlib: Cardinal_mk_insert"))
    except Exception:
        pass
    return results


def _r0333_mk_sum_compl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_sum_compl
    # #s + #(sᶜ : Set α) = #α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OVar("hash_a")
            results.append((rhs, "Mathlib: Cardinal_mk_sum_compl"))
        except Exception:
            pass
    return results


def _r0334_mk_diff_add_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_diff_add_mk
    # #(S \\ T : Set α) + #T = #S
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OVar("hash_S")
            results.append((rhs, "Mathlib: Cardinal_mk_diff_add_mk"))
        except Exception:
            pass
    return results


def _r0335_mk_sep(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_sep
    # #({ x ∈ s | t x } : Set α) = #{ x : s | t x.1 }
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_x_in_s_pipe_t_x_colon_Set_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_x_colon_s_pipe_t_x_1")
            results.append((rhs, "Mathlib: Cardinal_mk_sep"))
    except Exception:
        pass
    return results


def _r0336_mk_preimage_of_injective_of_subset_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_preimage_of_injective_of_subset_range_lift
    # lift.{v} #(f ⁻¹' s) = lift.{u} #s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("lift_u", (OVar("hash_s"),))
            results.append((rhs, "Mathlib: Cardinal_mk_preimage_of_injective_of_subset_range_lift"))
        except Exception:
            pass
    return results


def _r0337_mk_preimage_of_injective_of_subset_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_preimage_of_injective_of_subset_range
    # #(f ⁻¹' s) = #s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_f_inv_prime_s")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_s")
            results.append((rhs, "Mathlib: Cardinal_mk_preimage_of_injective_of_subset_range"))
    except Exception:
        pass
    return results


def _r0338_mk_preimage_equiv_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_preimage_equiv_lift
    # lift.{v} #(f ⁻¹' s) = lift.{u} #s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("lift_u", (OVar("hash_s"),))
            results.append((rhs, "Mathlib: Cardinal_mk_preimage_equiv_lift"))
        except Exception:
            pass
    return results


def _r0339_mk_preimage_equiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_preimage_equiv
    # #(f ⁻¹' s) = #s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_f_inv_prime_s")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_s")
            results.append((rhs, "Mathlib: Cardinal_mk_preimage_equiv"))
    except Exception:
        pass
    return results


def _r0340_le_mk_iff_exists_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.le_mk_iff_exists_subset
    # c ≤ #s ↔ ∃ p : Set α, p ⊆ s ∧ #p = c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_le_mk_iff_exists_subset"))
        except Exception:
            pass
    return results


def _r0341_mk_range_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_range_inl
    # #(range (@Sum.inl α β)) = lift.{v} #α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_range_at_Sum_inl_a_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("lift_v", (OVar("hash_a"),))
            results.append((rhs, "Mathlib: Cardinal_mk_range_inl"))
    except Exception:
        pass
    return results


def _r0342_mk_eq_two_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_eq_two_iff
    # #α = 2 ↔ ∃ x y : α, x ≠ y ∧ ({x, y} : Set α) = univ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("!=", (OOp("iff", (OLit(2), OOp("exists", (OVar("x"), OVar("y"), OVar("colon"), OVar("a"), OVar("x"),)))), OOp("and", (OVar("y"), OOp("x_y", (OVar("colon"), OVar("Set"), OVar("a"),)))))), OVar("univ")))
            results.append((rhs, "Mathlib: Cardinal_mk_eq_two_iff"))
    except Exception:
        pass
    return results


def _r0343_powerlt_mono_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.powerlt_mono_left
    # Monotone fun c => a ^< c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Monotone", 2)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("a"), OVar("pow_lt"), args[1],))
            results.append((rhs, "Mathlib: Cardinal_powerlt_mono_left"))
        except Exception:
            pass
    return results


def _r0344_powerlt_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.powerlt_succ
    # a ^< succ b = a ^ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 3)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("a"), args[2]))
            results.append((rhs, "Mathlib: Cardinal_powerlt_succ"))
        except Exception:
            pass
    return results


def _r0345_powerlt_min(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.powerlt_min
    # a ^< min b c = min (a ^< b) (a ^< c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 4)
    if args is not None:
        try:
            rhs = OOp("min", (OOp("a", (args[0], args[2],)), OOp("a", (args[0], args[3],)),))
            results.append((rhs, "Mathlib: Cardinal_powerlt_min"))
        except Exception:
            pass
    return results


def _r0346_powerlt_max(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.powerlt_max
    # a ^< max b c = max (a ^< b) (a ^< c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 4)
    if args is not None:
        try:
            rhs = OOp("max", (OOp("a", (args[0], args[2],)), OOp("a", (args[0], args[3],)),))
            results.append((rhs, "Mathlib: Cardinal_powerlt_max"))
        except Exception:
            pass
    return results


def _r0347_zero_powerlt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.zero_powerlt
    # 0 ^< a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Cardinal_zero_powerlt"))
        except Exception:
            pass
    return results


def _r0348_powerlt_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.powerlt_zero
    # a ^< 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Cardinal_powerlt_zero"))
        except Exception:
            pass
    return results


def _r0349_mk_bounded_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_bounded_subset
    # #{ s : Set α // Bounded r s } = #α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_s_colon_Set_a_slash_slash_Bounded_r_s")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_a")
            results.append((rhs, "Mathlib: Cardinal_mk_bounded_subset"))
    except Exception:
        pass
    return results


def _r0350_mk_subset_mk_lt_cof(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_subset_mk_lt_cof
    # #{ s : Set α // #s < cof (#α).ord } = #α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_s_colon_Set_a_slash_slash_hash_s_lt_cof_hash_a_ord")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_a")
            results.append((rhs, "Mathlib: Cardinal_mk_subset_mk_lt_cof"))
    except Exception:
        pass
    return results


def _r0351_two_power_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.two_power_aleph0
    # 2 ^ ℵ₀ = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("_unknown")
            results.append((rhs, "Mathlib: Cardinal_two_power_aleph0"))
        except Exception:
            pass
    return results


def _r0352_beth_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.beth_one
    # ℶ_ 1 = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OVar("_unknown")
            results.append((rhs, "Mathlib: Cardinal_beth_one"))
        except Exception:
            pass
    return results


def _r0353_mk_set_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_set_nat
    # #(Set ℕ) = 𝔠
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Set")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("_unknown")
            results.append((rhs, "Mathlib: Cardinal_mk_set_nat"))
    except Exception:
        pass
    return results


def _r0354_continuum_toNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.continuum_toNat
    # toNat continuum = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toNat", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Cardinal_continuum_toNat"))
        except Exception:
            pass
    return results


def _r0355_aleph0_add_continuum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph0_add_continuum
    # ℵ₀ + 𝔠 = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Cardinal_aleph0_add_continuum"))
        except Exception:
            pass
    return results


def _r0356_continuum_mul_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.continuum_mul_self
    # 𝔠 * 𝔠 = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Cardinal_continuum_mul_self"))
        except Exception:
            pass
    return results


def _r0357_aleph0_power_aleph0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.aleph0_power_aleph0
    # ℵ₀ ^ ℵ₀ = 𝔠
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("_unknown")
            results.append((rhs, "Mathlib: Cardinal_aleph0_power_aleph0"))
        except Exception:
            pass
    return results


def _r0358_mk_of_countable_eventually_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_of_countable_eventually_mem
    # #α = a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Cardinal_mk_of_countable_eventually_mem"))
    except Exception:
        pass
    return results


def _r0359_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.eq
    # #α = #β ↔ Nonempty (α ≃ β)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("hash_b"), OOp("Nonempty", (OOp("a", (OVar("_unknown"), OVar("b"),)),))))
            results.append((rhs, "Mathlib: Cardinal_eq"))
    except Exception:
        pass
    return results


def _r0360_mk_out(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_out
    # #c.out = c
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_c_out")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("c")
            results.append((rhs, "Mathlib: Cardinal_mk_out"))
    except Exception:
        pass
    return results


def _r0361_mk_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_congr
    # #α = #β
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_b")
            results.append((rhs, "Mathlib: Cardinal_mk_congr"))
    except Exception:
        pass
    return results


def _r0362_map_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.map_mk
    # map f hf #α = #(f α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 3)
    if args is not None:
        try:
            rhs = OVar("hash_f_a")
            results.append((rhs, "Mathlib: Cardinal_map_mk"))
        except Exception:
            pass
    return results


def _r0363_mk_uLift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_uLift
    # #(ULift.{v, u} α) = lift.{v} #α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_ULift_v_u_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("lift_v", (OVar("hash_a"),))
            results.append((rhs, "Mathlib: Cardinal_mk_uLift"))
    except Exception:
        pass
    return results


def _r0364_lift_umax(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_umax
    # lift.{max u v, u} = lift.{v, u}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("lift_max_u_v_u")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("lift_v_u")
            results.append((rhs, "Mathlib: Cardinal_lift_umax"))
    except Exception:
        pass
    return results


def _r0365_lift_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_id
    # lift.{u, u} a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_u_u", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_lift_id"))
        except Exception:
            pass
    return results


def _r0366_lift_uzero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_uzero
    # lift.{0} a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_0", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Cardinal_lift_uzero"))
        except Exception:
            pass
    return results


def _r0367_lift_mk_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_mk_eq
    # lift.{max v w} #α = lift.{max u w} #β ↔ Nonempty (α ≃ β)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_max_v_w", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OOp("lift_max_u_w", (OVar("hash_b"),)), OOp("Nonempty", (OOp("a", (OVar("_unknown"), OVar("b"),)),))))
            results.append((rhs, "Mathlib: Cardinal_lift_mk_eq"))
        except Exception:
            pass
    return results


def _r0368_mk_congr_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_congr_lift
    # lift.{v} #α = lift.{u} #β
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("lift_u", (OVar("hash_b"),))
            results.append((rhs, "Mathlib: Cardinal_mk_congr_lift"))
        except Exception:
            pass
    return results


def _r0369_mk_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_eq_zero
    # #α = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Cardinal_mk_eq_zero"))
    except Exception:
        pass
    return results


def _r0370_mk_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_eq_one
    # #α = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Cardinal_mk_eq_one"))
    except Exception:
        pass
    return results


def _r0371_add_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.add_def
    # #α + #β = #(α ⊕ β)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OVar("hash_a_b")
            results.append((rhs, "Mathlib: Cardinal_add_def"))
        except Exception:
            pass
    return results


def _r0372_mk_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_sum
    # #(α ⊕ β) = lift.{v, u} #α + lift.{u, v} #β
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_a_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OOp("lift_v_u", (OVar("hash_a"),)), OOp("lift_u_v", (OVar("hash_b"),))))
            results.append((rhs, "Mathlib: Cardinal_mk_sum"))
    except Exception:
        pass
    return results


def _r0373_mul_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mul_def
    # #α * #β = #(α × β)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("hash_a_times_b")
            results.append((rhs, "Mathlib: Cardinal_mul_def"))
        except Exception:
            pass
    return results


def _r0374_mk_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_prod
    # #(α × β) = lift.{v, u} #α * lift.{u, v} #β
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_a_times_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OOp("lift_v_u", (OVar("hash_a"),)), OOp("lift_u_v", (OVar("hash_b"),))))
            results.append((rhs, "Mathlib: Cardinal_mk_prod"))
    except Exception:
        pass
    return results


def _r0375_power_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.power_def
    # #α ^ #β = #(β → α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("hash_b_to_a")
            results.append((rhs, "Mathlib: Cardinal_power_def"))
        except Exception:
            pass
    return results


def _r0376_lift_power(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_power
    # lift.{v} (a ^ b) = lift.{v} a ^ lift.{v} b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("lift_v", (OVar("a"),)), OOp("lift_v", (OVar("b"),))))
            results.append((rhs, "Mathlib: Cardinal_lift_power"))
        except Exception:
            pass
    return results


def _r0377_power_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.power_zero
    # a ^ (0 : Cardinal) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Cardinal_power_zero"))
        except Exception:
            pass
    return results


def _r0378_one_power(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.one_power
    # (1 : Cardinal) ^ a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Cardinal_one_power"))
        except Exception:
            pass
    return results


def _r0379_mul_power(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mul_power
    # (a * b) ^ c = a ^ c * b ^ c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("a"), args[1])), OOp("**", (OVar("b"), args[1]))))
            results.append((rhs, "Mathlib: Cardinal_mul_power"))
        except Exception:
            pass
    return results


def _r0380_lift_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_one
    # lift 1 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Cardinal_lift_one"))
        except Exception:
            pass
    return results


def _r0381_mk_sigma(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_sigma
    # #(Σ i, f i) = sum fun i => #(f i)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Sig_i_f_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("sum", (OVar("fun"), OVar("i"), OVar("eq_gt"), OVar("hash_f_i"),))
            results.append((rhs, "Mathlib: Cardinal_mk_sigma"))
    except Exception:
        pass
    return results


def _r0382_mk_sigma_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_sigma_congr
    # #(Σ i, f i) = #(Σ i, g i)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Sig_i_f_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_Sig_i_g_i")
            results.append((rhs, "Mathlib: Cardinal_mk_sigma_congr"))
    except Exception:
        pass
    return results


def _r0383_mk_sigma_congrRight(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_sigma_congrRight
    # #(Σ i, f i) = #(Σ i, g i)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Sig_i_f_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_Sig_i_g_i")
            results.append((rhs, "Mathlib: Cardinal_mk_sigma_congrRight"))
    except Exception:
        pass
    return results


def _r0384_mk_psigma_congrRight(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_psigma_congrRight
    # #(Σ' i, f i) = #(Σ' i, g i)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Sig_prime_i_f_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_Sig_prime_i_g_i")
            results.append((rhs, "Mathlib: Cardinal_mk_psigma_congrRight"))
    except Exception:
        pass
    return results


def _r0385_mk_psigma_congrRight_prop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_psigma_congrRight_prop
    # #(Σ' i, f i) = #(Σ' i, g i)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Sig_prime_i_f_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_Sig_prime_i_g_i")
            results.append((rhs, "Mathlib: Cardinal_mk_psigma_congrRight_prop"))
    except Exception:
        pass
    return results


def _r0386_sum_const(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.sum_const
    # (sum fun _ : ι => a) = lift.{v} #ι * lift.{u} a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sum", 6)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("lift_v", (OVar("hash_i"),)), OOp("lift_u", (args[5],))))
            results.append((rhs, "Mathlib: Cardinal_sum_const"))
        except Exception:
            pass
    return results


def _r0387_lift_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_sum
    # Cardinal.lift.{w} (Cardinal.sum f) = Cardinal.sum fun i => Cardinal.lift.{w} (f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Cardinal_lift_w", 1)
    if args is not None:
        try:
            rhs = OOp("Cardinal_sum", (OVar("fun"), OVar("i"), OVar("eq_gt"), OVar("Cardinal_lift_w"), OOp("f", (OVar("i"),)),))
            results.append((rhs, "Mathlib: Cardinal_lift_sum"))
        except Exception:
            pass
    return results


def _r0388_sum_nat_eq_add_sum_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.sum_nat_eq_add_sum_succ
    # Cardinal.sum f = f 0 + Cardinal.sum fun i => f (i + 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Cardinal_sum", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("f", (OLit(0),)), OOp("Cardinal_sum", (OVar("fun"), OVar("i"), OVar("eq_gt"), args[0], OOp("+", (OVar("i"), OLit(1))),))))
            results.append((rhs, "Mathlib: Cardinal_sum_nat_eq_add_sum_succ"))
        except Exception:
            pass
    return results


def _r0389_mk_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_pi
    # #(Π i, α i) = prod fun i => #(α i)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Pi_i_a_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("prod", (OVar("fun"), OVar("i"), OVar("eq_gt"), OVar("hash_a_i"),))
            results.append((rhs, "Mathlib: Cardinal_mk_pi"))
    except Exception:
        pass
    return results


def _r0390_mk_pi_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_pi_congr
    # #(Π i, f i) = #(Π i, g i)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Pi_i_f_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_Pi_i_g_i")
            results.append((rhs, "Mathlib: Cardinal_mk_pi_congr"))
    except Exception:
        pass
    return results


def _r0391_mk_pi_congr_prop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_pi_congr_prop
    # #(Π i, f i) = #(Π i, g i)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Pi_i_f_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_Pi_i_g_i")
            results.append((rhs, "Mathlib: Cardinal_mk_pi_congr_prop"))
    except Exception:
        pass
    return results


def _r0392_mk_pi_congrRight(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_pi_congrRight
    # #(Π i, f i) = #(Π i, g i)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Pi_i_f_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_Pi_i_g_i")
            results.append((rhs, "Mathlib: Cardinal_mk_pi_congrRight"))
    except Exception:
        pass
    return results


def _r0393_mk_pi_congrRight_prop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_pi_congrRight_prop
    # #(Π i, f i) = #(Π i, g i)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Pi_i_f_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_Pi_i_g_i")
            results.append((rhs, "Mathlib: Cardinal_mk_pi_congrRight_prop"))
    except Exception:
        pass
    return results


def _r0394_prod_const(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.prod_const
    # (prod fun _ : ι => a) = lift.{u} a ^ lift.{v} #ι
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prod", 6)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("lift_u", (args[5],)), OOp("lift_v", (OVar("hash_i"),))))
            results.append((rhs, "Mathlib: Cardinal_prod_const"))
        except Exception:
            pass
    return results


def _r0395_prod_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.prod_eq_zero
    # prod f = 0 ↔ ∃ i, f i = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prod", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OOp("exists", (OVar("i"), args[0], OVar("i"),)))), OLit(0)))
            results.append((rhs, "Mathlib: Cardinal_prod_eq_zero"))
        except Exception:
            pass
    return results


def _r0396_lift_power_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_power_sum
    # lift.{u, v} a ^ sum f = prod fun i ↦ a ^ f i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("prod", (OVar("fun"), OVar("i"), OVar("_unknown"), OVar("a"),)), OOp("f", (OVar("i"),))))
            results.append((rhs, "Mathlib: Cardinal_lift_power_sum"))
        except Exception:
            pass
    return results


def _r0397_power_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.power_sum
    # a ^ sum f = prod fun i ↦ a ^ f i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("prod", (OVar("fun"), OVar("i"), OVar("_unknown"), args[0],)), OOp("f", (OVar("i"),))))
            results.append((rhs, "Mathlib: Cardinal_power_sum"))
        except Exception:
            pass
    return results


def _r0398_lift_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.lift_prod
    # lift.{w} (prod c) = prod fun i => lift.{w} (c i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_w", 1)
    if args is not None:
        try:
            rhs = OOp("prod", (OVar("fun"), OVar("i"), OVar("eq_gt"), OVar("lift_w"), OOp("c", (OVar("i"),)),))
            results.append((rhs, "Mathlib: Cardinal_lift_prod"))
        except Exception:
            pass
    return results


def _r0399_mk_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cardinal.mk_nat
    # #ℕ = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("_0")
            results.append((rhs, "Mathlib: Cardinal_mk_nat"))
    except Exception:
        pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_set_theory rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("!=", "*", "**", "+", "<", "<=", "Cardinal_lift_max_u_w", "Cardinal_lift_w", "Cardinal_sum", "Denumerable", "IsStrongLimit", "Monotone", "Nonempty", "Order_succ", "Ordinal_lift_v", "_0", "_1", "_2", "_unknown", "a", "aleph", "and", "beth", "cantorFunction", "cantorFunctionAux", "comp", "exists", "fun", "iInf", "iSup", "iff", "lift", "lift_0", "lift_max_u_w", "lift_max_v_prime_w_prime", "lift_max_v_w", "lift_u", "lift_u_u", "lift_u_v", "lift_v", "lift_v_u", "lift_w", "m", "map", "max", "n", "n_succ", "not", "ofENat", "ofNat_m",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_set_theory axioms."""
    if recognizes(term):
        return 0.6
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_set_theory rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_cantorFunctionAux_false(term, ctx))
    results.extend(_r0001_ord_preAleph(term, ctx))
    results.extend(_r0002_type_lt_cardinal(term, ctx))
    results.extend(_r0003_succ_preAleph(term, ctx))
    results.extend(_r0004_preAleph_add_one(term, ctx))
    results.extend(_r0005_preAleph_omega0(term, ctx))
    results.extend(_r0006_ord_aleph(term, ctx))
    results.extend(_r0007_aleph_add_one(term, ctx))
    results.extend(_r0008_lift_aleph(term, ctx))
    results.extend(_r0009_aleph_toENat(term, ctx))
    results.extend(_r0010_preBeth_inj(term, ctx))
    results.extend(_r0011_preBeth_zero(term, ctx))
    results.extend(_r0012_preBeth_omega(term, ctx))
    results.extend(_r0013_beth_zero(term, ctx))
    results.extend(_r0014_beth_add_one(term, ctx))
    results.extend(_r0015_aleph_natCast_eq_lift(term, ctx))
    results.extend(_r0016_lift_eq_aleph_natCast(term, ctx))
    results.extend(_r0017_aleph_ofNat_eq_lift(term, ctx))
    results.extend(_r0018_lift_eq_aleph_ofNat(term, ctx))
    results.extend(_r0019_beth_natCast_eq_lift(term, ctx))
    results.extend(_r0020_lift_eq_beth_natCast(term, ctx))
    results.extend(_r0021_beth_ofNat_eq_lift(term, ctx))
    results.extend(_r0022_lift_eq_beth_ofNat(term, ctx))
    results.extend(_r0023_aleph_mul_aleph(term, ctx))
    results.extend(_r0024_aleph0_mul_eq(term, ctx))
    results.extend(_r0025_mul_aleph0_eq(term, ctx))
    results.extend(_r0026_aleph0_mul_mk_eq(term, ctx))
    results.extend(_r0027_aleph_mul_aleph0(term, ctx))
    results.extend(_r0028_lt_aleph0(term, ctx))
    results.extend(_r0029_mk_eq_nat_iff(term, ctx))
    results.extend(_r0030_denumerable_iff(term, ctx))
    results.extend(_r0031_aleph0_mul_aleph0(term, ctx))
    results.extend(_r0032_ofNat_mul_aleph0(term, ctx))
    results.extend(_r0033_aleph0_mul_ofNat(term, ctx))
    results.extend(_r0034_nat_add_aleph0(term, ctx))
    results.extend(_r0035_ofNat_add_aleph0(term, ctx))
    results.extend(_r0036_aleph0_add_ofNat(term, ctx))
    results.extend(_r0037_exists_nat_eq_of_le_nat(term, ctx))
    results.extend(_r0038_mk_multiplicative(term, ctx))
    results.extend(_r0039_mk_mulOpposite(term, ctx))
    results.extend(_r0040_mk_singleton(term, ctx))
    results.extend(_r0041_mk_list_eq_sum_pow(term, ctx))
    results.extend(_r0042_mk_setProd(term, ctx))
    results.extend(_r0043_mk_range_inr(term, ctx))
    results.extend(_r0044_lift_continuum(term, ctx))
    results.extend(_r0045_continuum_toENat(term, ctx))
    results.extend(_r0046_continuum_add_aleph0(term, ctx))
    results.extend(_r0047_continuum_add_self(term, ctx))
    results.extend(_r0048_nat_add_continuum(term, ctx))
    results.extend(_r0049_continuum_add_nat(term, ctx))
    results.extend(_r0050_ofNat_add_continuum(term, ctx))
    results.extend(_r0051_continuum_add_ofNat(term, ctx))
    results.extend(_r0052_continuum_mul_aleph0(term, ctx))
    results.extend(_r0053_aleph0_mul_continuum(term, ctx))
    results.extend(_r0054_nat_mul_continuum(term, ctx))
    results.extend(_r0055_continuum_mul_nat(term, ctx))
    results.extend(_r0056_ofNat_mul_continuum(term, ctx))
    results.extend(_r0057_continuum_mul_ofNat(term, ctx))
    results.extend(_r0058_nat_power_aleph0(term, ctx))
    results.extend(_r0059_continuum_power_aleph0(term, ctx))
    results.extend(_r0060_power_aleph0_of_le_continuum(term, ctx))
    results.extend(_r0061__unknown(term, ctx))
    results.extend(_r0062_lift_zero(term, ctx))
    results.extend(_r0063_mk_eq_zero_iff(term, ctx))
    results.extend(_r0064_mk_option(term, ctx))
    results.extend(_r0065_mk_psum(term, ctx))
    results.extend(_r0066_power_one(term, ctx))
    results.extend(_r0067_power_add(term, ctx))
    results.extend(_r0068_zero_power(term, ctx))
    results.extend(_r0069_lift_add(term, ctx))
    results.extend(_r0070_mk_sigma_congr_lift(term, ctx))
    results.extend(_r0071_mk_pi_congr_lift(term, ctx))
    results.extend(_r0072_lift_mk_fin(term, ctx))
    results.extend(_r0073_ofENat_nat(term, ctx))
    results.extend(_r0074_ofENat_zero(term, ctx))
    results.extend(_r0075_ofENat_one(term, ctx))
    results.extend(_r0076_ofENat_ofNat(term, ctx))
    results.extend(_r0077_ofENat_eq_nat(term, ctx))
    results.extend(_r0078_nat_eq_ofENat(term, ctx))
    results.extend(_r0079_ofENat_eq_zero(term, ctx))
    results.extend(_r0080_zero_eq_ofENat(term, ctx))
    results.extend(_r0081_ofENat_eq_one(term, ctx))
    results.extend(_r0082_one_eq_ofENat(term, ctx))
    results.extend(_r0083_ofENat_eq_ofNat(term, ctx))
    results.extend(_r0084_ofNat_eq_ofENat(term, ctx))
    results.extend(_r0085_lift_ofENat(term, ctx))
    results.extend(_r0086_lift_eq_ofENat(term, ctx))
    results.extend(_r0087_ofENat_eq_lift(term, ctx))
    results.extend(_r0088_range_ofENat(term, ctx))
    results.extend(_r0089_toENat_comp_ofENat(term, ctx))
    results.extend(_r0090_toENat_nat(term, ctx))
    results.extend(_r0091_toENat_ofNat(term, ctx))
    results.extend(_r0092_toENat_eq_natCast(term, ctx))
    results.extend(_r0093_toENat_eq_zero(term, ctx))
    results.extend(_r0094_toENat_eq_one(term, ctx))
    results.extend(_r0095_toENat_eq_ofNat(term, ctx))
    results.extend(_r0096_ofNat_eq_toENat(term, ctx))
    results.extend(_r0097_toENat_eq_top(term, ctx))
    results.extend(_r0098_toENat_lift(term, ctx))
    results.extend(_r0099_aleph0_add_ofENat(term, ctx))
    results.extend(_r0100_ofENat_add_aleph0(term, ctx))
    results.extend(_r0101_ofENat_mul_aleph0(term, ctx))
    results.extend(_r0102_ofENat_mul(term, ctx))
    results.extend(_r0103_mk_freeGroup(term, ctx))
    results.extend(_r0104_mk_freeCommRing(term, ctx))
    results.extend(_r0105_lift_max(term, ctx))
    results.extend(_r0106_mk_fintype(term, ctx))
    results.extend(_r0107_lift_eq_one(term, ctx))
    results.extend(_r0108_lift_mul(term, ctx))
    results.extend(_r0109_lift_two_power(term, ctx))
    results.extend(_r0110_aleph0_eq_lift(term, ctx))
    results.extend(_r0111_lift_eq_aleph0(term, ctx))
    results.extend(_r0112_lift_ofNat(term, ctx))
    results.extend(_r0113_lift_eq_ofNat_iff(term, ctx))
    results.extend(_r0114_toNat_ofENat(term, ctx))
    results.extend(_r0115_toNat_natCast(term, ctx))
    results.extend(_r0116_toNat_eq_zero(term, ctx))
    results.extend(_r0117_cast_toNat_of_lt_aleph0(term, ctx))
    results.extend(_r0118_aleph0_toNat(term, ctx))
    results.extend(_r0119_mk_toNat_eq_card(term, ctx))
    results.extend(_r0120_one_toNat(term, ctx))
    results.extend(_r0121_toNat_eq_one_iff_unique(term, ctx))
    results.extend(_r0122_toNat_congr(term, ctx))
    results.extend(_r0123_ord_zero(term, ctx))
    results.extend(_r0124_ord_nat(term, ctx))
    results.extend(_r0125_ord_one(term, ctx))
    results.extend(_r0126_ord_eq_zero(term, ctx))
    results.extend(_r0127_ord_eq_one(term, ctx))
    results.extend(_r0128_ord_eq_omega0(term, ctx))
    results.extend(_r0129_univ_umax(term, ctx))
    results.extend(_r0130_preAleph_lt_preAleph(term, ctx))
    results.extend(_r0131_preAleph_pos(term, ctx))
    results.extend(_r0132_aleph0_le_preAleph(term, ctx))
    results.extend(_r0133_aleph_lt_aleph(term, ctx))
    results.extend(_r0134_aleph_one_le_iff(term, ctx))
    results.extend(_r0135_lt_aleph_one_iff(term, ctx))
    results.extend(_r0136_preBeth_le_preBeth(term, ctx))
    results.extend(_r0137_isStrongLimit_preBeth(term, ctx))
    results.extend(_r0138_beth_le_beth(term, ctx))
    results.extend(_r0139_lift_le_aleph_natCast(term, ctx))
    results.extend(_r0140_aleph_natCast_lt_lift(term, ctx))
    results.extend(_r0141_lift_lt_aleph_natCast(term, ctx))
    results.extend(_r0142_aleph_ofNat_le_lift(term, ctx))
    results.extend(_r0143_lift_le_aleph_ofNat(term, ctx))
    results.extend(_r0144_aleph_ofNat_lt_lift(term, ctx))
    results.extend(_r0145_lift_lt_aleph_ofNat(term, ctx))
    results.extend(_r0146_beth_natCast_le_lift(term, ctx))
    results.extend(_r0147_lift_le_beth_natCast(term, ctx))
    results.extend(_r0148_beth_natCast_lt_lift(term, ctx))
    results.extend(_r0149_lift_lt_beth_natCast(term, ctx))
    results.extend(_r0150_beth_ofNat_le_lift(term, ctx))
    results.extend(_r0151_lift_le_beth_ofNat(term, ctx))
    results.extend(_r0152_beth_ofNat_lt_lift(term, ctx))
    results.extend(_r0153_lift_lt_beth_ofNat(term, ctx))
    results.extend(_r0154_mk_le_aleph0_iff(term, ctx))
    results.extend(_r0155_le_aleph0_iff_set_countable(term, ctx))
    results.extend(_r0156_add_le_aleph0(term, ctx))
    results.extend(_r0157_two_le_iff(term, ctx))
    results.extend(_r0158_continuum_le_lift(term, ctx))
    results.extend(_r0159_lift_le_continuum(term, ctx))
    results.extend(_r0160_continuum_lt_lift(term, ctx))
    results.extend(_r0161_lift_lt_continuum(term, ctx))
    results.extend(_r0162_ofENat_lt_nat(term, ctx))
    results.extend(_r0163_ofENat_lt_ofNat(term, ctx))
    results.extend(_r0164_nat_lt_ofENat(term, ctx))
    results.extend(_r0165_ofENat_pos(term, ctx))
    results.extend(_r0166_one_lt_ofENat(term, ctx))
    results.extend(_r0167_ofNat_lt_ofENat(term, ctx))
    results.extend(_r0168_ofENat_le_nat(term, ctx))
    results.extend(_r0169_ofENat_le_one(term, ctx))
    results.extend(_r0170_ofENat_le_ofNat(term, ctx))
    results.extend(_r0171_nat_le_ofENat(term, ctx))
    results.extend(_r0172_one_le_ofENat(term, ctx))
    results.extend(_r0173_ofNat_le_ofENat(term, ctx))
    results.extend(_r0174_lift_lt_ofENat(term, ctx))
    results.extend(_r0175_lift_le_ofENat(term, ctx))
    results.extend(_r0176_ofENat_lt_lift(term, ctx))
    results.extend(_r0177_ofENat_le_lift(term, ctx))
    results.extend(_r0178_toENat_le_natCast(term, ctx))
    results.extend(_r0179_toENat_le_one(term, ctx))
    results.extend(_r0180_toENat_le_ofNat(term, ctx))
    results.extend(_r0181_one_le_toENat(term, ctx))
    results.extend(_r0182_ofNat_le_toENat(term, ctx))
    results.extend(_r0183_toENat_lt_natCast(term, ctx))
    results.extend(_r0184_toENat_lt_one(term, ctx))
    results.extend(_r0185_toENat_lt_ofNat(term, ctx))
    results.extend(_r0186_natCast_lt_toENat(term, ctx))
    results.extend(_r0187_one_lt_toENat(term, ctx))
    results.extend(_r0188_ofNat_lt_toENat(term, ctx))
    results.extend(_r0189_toENat_ne_top(term, ctx))
    results.extend(_r0190_toENat_lt_top(term, ctx))
    results.extend(_r0191_lift_le(term, ctx))
    results.extend(_r0192_lift_lt(term, ctx))
    results.extend(_r0193_lift_le_aleph0(term, ctx))
    results.extend(_r0194_aleph0_lt_lift(term, ctx))
    results.extend(_r0195_lift_lt_aleph0(term, ctx))
    results.extend(_r0196_lift_le_one_iff(term, ctx))
    results.extend(_r0197_one_le_lift_iff(term, ctx))
    results.extend(_r0198_lift_lt_ofNat_iff(term, ctx))
    results.extend(_r0199_zero_lt_lift_iff(term, ctx))
    results.extend(_r0200_toNat_ne_zero(term, ctx))
    results.extend(_r0201_ord_lt_ord(term, ctx))
    results.extend(_r0202_ord_pos(term, ctx))
    results.extend(_r0203_omega0_le_ord(term, ctx))
    results.extend(_r0204_ord_le_omega0(term, ctx))
    results.extend(_r0205_ord_lt_omega0(term, ctx))
    results.extend(_r0206_omega0_lt_ord(term, ctx))
    results.extend(_r0207_mk_inv(term, ctx))
    results.extend(_r0208_mk_smul_set(term, ctx))
    results.extend(_r0209_pow_four(term, ctx))
    results.extend(_r0210_mk_quaternionAlgebra(term, ctx))
    results.extend(_r0211_mk_quaternionAlgebra_of_infinite(term, ctx))
    results.extend(_r0212_mk_univ_quaternionAlgebra(term, ctx))
    results.extend(_r0213_mk_univ_quaternionAlgebra_of_infinite(term, ctx))
    results.extend(_r0214_mk_complex(term, ctx))
    results.extend(_r0215_mk_univ_complex(term, ctx))
    results.extend(_r0216_cantorFunctionAux_true(term, ctx))
    results.extend(_r0217_cantorFunctionAux_eq(term, ctx))
    results.extend(_r0218_cantorFunctionAux_zero(term, ctx))
    results.extend(_r0219_cantorFunctionAux_succ(term, ctx))
    results.extend(_r0220_cantorFunction_succ(term, ctx))
    results.extend(_r0221_mk_real(term, ctx))
    results.extend(_r0222_mk_univ_real(term, ctx))
    results.extend(_r0223_mk_Ioi_real(term, ctx))
    results.extend(_r0224_mk_Ici_real(term, ctx))
    results.extend(_r0225_mk_Iio_real(term, ctx))
    results.extend(_r0226_mk_Iic_real(term, ctx))
    results.extend(_r0227_mk_Ioo_real(term, ctx))
    results.extend(_r0228_mk_Ico_real(term, ctx))
    results.extend(_r0229_mk_Icc_real(term, ctx))
    results.extend(_r0230_mk_Ioc_real(term, ctx))
    results.extend(_r0231_mkRat(term, ctx))
    results.extend(_r0232_mk_fractionRing(term, ctx))
    results.extend(_r0233_card_preOmega(term, ctx))
    results.extend(_r0234_mk_cardinal(term, ctx))
    results.extend(_r0235_preAleph_max(term, ctx))
    results.extend(_r0236_preAleph_zero(term, ctx))
    results.extend(_r0237_preAleph_succ(term, ctx))
    results.extend(_r0238_preAleph_nat(term, ctx))
    results.extend(_r0239_lift_preAleph(term, ctx))
    results.extend(_r0240_lift_preOmega(term, ctx))
    results.extend(_r0241_preAleph_limit(term, ctx))
    results.extend(_r0242_aleph_eq_preAleph(term, ctx))
    results.extend(_r0243_card_omega(term, ctx))
    results.extend(_r0244_aleph_max(term, ctx))
    results.extend(_r0245_succ_aleph(term, ctx))
    results.extend(_r0246_aleph_succ(term, ctx))
    results.extend(_r0247_aleph_zero(term, ctx))
    results.extend(_r0248_lift_omega(term, ctx))
    results.extend(_r0249_aleph_limit(term, ctx))
    results.extend(_r0250_aleph_toNat(term, ctx))
    results.extend(_r0251_range_aleph(term, ctx))
    results.extend(_r0252_succ_aleph0(term, ctx))
    results.extend(_r0253_preBeth_add_one(term, ctx))
    results.extend(_r0254_preBeth_succ(term, ctx))
    results.extend(_r0255_preBeth_limit(term, ctx))
    results.extend(_r0256_preBeth_nat(term, ctx))
    results.extend(_r0257_preBeth_one(term, ctx))
    results.extend(_r0258_preBeth_eq_zero(term, ctx))
    results.extend(_r0259_lift_preBeth(term, ctx))
    results.extend(_r0260_beth_eq_preBeth(term, ctx))
    results.extend(_r0261_beth_succ(term, ctx))
    results.extend(_r0262_beth_limit(term, ctx))
    results.extend(_r0263_lift_beth(term, ctx))
    results.extend(_r0264_aleph_one_eq_lift(term, ctx))
    results.extend(_r0265_lift_eq_aleph_one(term, ctx))
    results.extend(_r0266_mul_eq_self(term, ctx))
    results.extend(_r0267_mul_eq_max(term, ctx))
    results.extend(_r0268_mul_mk_eq_max(term, ctx))
    results.extend(_r0269_mk_mul_aleph0_eq(term, ctx))
    results.extend(_r0270_aleph0_mul_aleph(term, ctx))
    results.extend(_r0271_mul_eq_max_of_aleph0_le_left(term, ctx))
    results.extend(_r0272_mul_eq_max_of_aleph0_le_right(term, ctx))
    results.extend(_r0273_mul_eq_left(term, ctx))
    results.extend(_r0274_mul_eq_right(term, ctx))
    results.extend(_r0275_mul_eq_left_iff(term, ctx))
    results.extend(_r0276_mk_preimage_down(term, ctx))
    results.extend(_r0277_lift_mk_shrink(term, ctx))
    results.extend(_r0278_prod_eq_of_fintype(term, ctx))
    results.extend(_r0279_sInf_eq_zero_iff(term, ctx))
    results.extend(_r0280_iInf_eq_zero_iff(term, ctx))
    results.extend(_r0281_iSup_of_empty(term, ctx))
    results.extend(_r0282_lift_sInf(term, ctx))
    results.extend(_r0283_lift_iInf(term, ctx))
    results.extend(_r0284_lift_sSup(term, ctx))
    results.extend(_r0285_lift_iSup(term, ctx))
    results.extend(_r0286_mk_finset_of_fintype(term, ctx))
    results.extend(_r0287_nat_succ(term, ctx))
    results.extend(_r0288_succ_natCast(term, ctx))
    results.extend(_r0289_succ_zero(term, ctx))
    results.extend(_r0290_exists_finset_eq_card(term, ctx))
    results.extend(_r0291_lt_one_iff(term, ctx))
    results.extend(_r0292_le_one_iff(term, ctx))
    results.extend(_r0293_succ_eq_of_lt_aleph0(term, ctx))
    results.extend(_r0294_not_isSuccLimit_natCast(term, ctx))
    results.extend(_r0295_exists_eq_natCast_of_iSup_eq(term, ctx))
    results.extend(_r0296_nsmul_lt_aleph0_iff(term, ctx))
    results.extend(_r0297_mul_lt_aleph0_iff(term, ctx))
    results.extend(_r0298_eq_one_iff_unique(term, ctx))
    results.extend(_r0299_mk_eq_aleph0(term, ctx))
    results.extend(_r0300_mk_denumerable(term, ctx))
    results.extend(_r0301_aleph0_add_aleph0(term, ctx))
    results.extend(_r0302_nat_mul_aleph0(term, ctx))
    results.extend(_r0303_aleph0_mul_nat(term, ctx))
    results.extend(_r0304_aleph0_add_nat(term, ctx))
    results.extend(_r0305_mk_int(term, ctx))
    results.extend(_r0306_mk_pnat(term, ctx))
    results.extend(_r0307_mk_additive(term, ctx))
    results.extend(_r0308_mk_vector(term, ctx))
    results.extend(_r0309_sum_zero_pow(term, ctx))
    results.extend(_r0310_mk_emptyCollection(term, ctx))
    results.extend(_r0311_mk_set_eq_zero_iff(term, ctx))
    results.extend(_r0312_mk_univ(term, ctx))
    results.extend(_r0313_mk_range_eq(term, ctx))
    results.extend(_r0314_mk_range_eq_of_injective(term, ctx))
    results.extend(_r0315_mk_range_eq_lift(term, ctx))
    results.extend(_r0316_mk_image_eq_of_injOn(term, ctx))
    results.extend(_r0317_mk_image_eq_of_injOn_lift(term, ctx))
    results.extend(_r0318_mk_image_eq(term, ctx))
    results.extend(_r0319_mk_image_eq_lift(term, ctx))
    results.extend(_r0320_mk_image_embedding_lift(term, ctx))
    results.extend(_r0321_mk_image_embedding(term, ctx))
    results.extend(_r0322_mk_iUnion_le_sum_mk(term, ctx))
    results.extend(_r0323_mk_iUnion_le_sum_mk_lift(term, ctx))
    results.extend(_r0324_mk_iUnion_eq_sum_mk(term, ctx))
    results.extend(_r0325_mk_iUnion_eq_sum_mk_lift(term, ctx))
    results.extend(_r0326_mk_set_eq_nat_iff_finset(term, ctx))
    results.extend(_r0327_mk_eq_nat_iff_finset(term, ctx))
    results.extend(_r0328_mk_eq_nat_iff_fintype(term, ctx))
    results.extend(_r0329_mk_set_eq_one_iff(term, ctx))
    results.extend(_r0330_mk_union_add_mk_inter(term, ctx))
    results.extend(_r0331_mk_union_of_disjoint(term, ctx))
    results.extend(_r0332_mk_insert(term, ctx))
    results.extend(_r0333_mk_sum_compl(term, ctx))
    results.extend(_r0334_mk_diff_add_mk(term, ctx))
    results.extend(_r0335_mk_sep(term, ctx))
    results.extend(_r0336_mk_preimage_of_injective_of_subset_range(term, ctx))
    results.extend(_r0337_mk_preimage_of_injective_of_subset_range(term, ctx))
    results.extend(_r0338_mk_preimage_equiv_lift(term, ctx))
    results.extend(_r0339_mk_preimage_equiv(term, ctx))
    results.extend(_r0340_le_mk_iff_exists_subset(term, ctx))
    results.extend(_r0341_mk_range_inl(term, ctx))
    results.extend(_r0342_mk_eq_two_iff(term, ctx))
    results.extend(_r0343_powerlt_mono_left(term, ctx))
    results.extend(_r0344_powerlt_succ(term, ctx))
    results.extend(_r0345_powerlt_min(term, ctx))
    results.extend(_r0346_powerlt_max(term, ctx))
    results.extend(_r0347_zero_powerlt(term, ctx))
    results.extend(_r0348_powerlt_zero(term, ctx))
    results.extend(_r0349_mk_bounded_subset(term, ctx))
    results.extend(_r0350_mk_subset_mk_lt_cof(term, ctx))
    results.extend(_r0351_two_power_aleph0(term, ctx))
    results.extend(_r0352_beth_one(term, ctx))
    results.extend(_r0353_mk_set_nat(term, ctx))
    results.extend(_r0354_continuum_toNat(term, ctx))
    results.extend(_r0355_aleph0_add_continuum(term, ctx))
    results.extend(_r0356_continuum_mul_self(term, ctx))
    results.extend(_r0357_aleph0_power_aleph0(term, ctx))
    results.extend(_r0358_mk_of_countable_eventually_mem(term, ctx))
    results.extend(_r0359_eq(term, ctx))
    results.extend(_r0360_mk_out(term, ctx))
    results.extend(_r0361_mk_congr(term, ctx))
    results.extend(_r0362_map_mk(term, ctx))
    results.extend(_r0363_mk_uLift(term, ctx))
    results.extend(_r0364_lift_umax(term, ctx))
    results.extend(_r0365_lift_id(term, ctx))
    results.extend(_r0366_lift_uzero(term, ctx))
    results.extend(_r0367_lift_mk_eq(term, ctx))
    results.extend(_r0368_mk_congr_lift(term, ctx))
    results.extend(_r0369_mk_eq_zero(term, ctx))
    results.extend(_r0370_mk_eq_one(term, ctx))
    results.extend(_r0371_add_def(term, ctx))
    results.extend(_r0372_mk_sum(term, ctx))
    results.extend(_r0373_mul_def(term, ctx))
    results.extend(_r0374_mk_prod(term, ctx))
    results.extend(_r0375_power_def(term, ctx))
    results.extend(_r0376_lift_power(term, ctx))
    results.extend(_r0377_power_zero(term, ctx))
    results.extend(_r0378_one_power(term, ctx))
    results.extend(_r0379_mul_power(term, ctx))
    results.extend(_r0380_lift_one(term, ctx))
    results.extend(_r0381_mk_sigma(term, ctx))
    results.extend(_r0382_mk_sigma_congr(term, ctx))
    results.extend(_r0383_mk_sigma_congrRight(term, ctx))
    results.extend(_r0384_mk_psigma_congrRight(term, ctx))
    results.extend(_r0385_mk_psigma_congrRight_prop(term, ctx))
    results.extend(_r0386_sum_const(term, ctx))
    results.extend(_r0387_lift_sum(term, ctx))
    results.extend(_r0388_sum_nat_eq_add_sum_succ(term, ctx))
    results.extend(_r0389_mk_pi(term, ctx))
    results.extend(_r0390_mk_pi_congr(term, ctx))
    results.extend(_r0391_mk_pi_congr_prop(term, ctx))
    results.extend(_r0392_mk_pi_congrRight(term, ctx))
    results.extend(_r0393_mk_pi_congrRight_prop(term, ctx))
    results.extend(_r0394_prod_const(term, ctx))
    results.extend(_r0395_prod_eq_zero(term, ctx))
    results.extend(_r0396_lift_power_sum(term, ctx))
    results.extend(_r0397_power_sum(term, ctx))
    results.extend(_r0398_lift_prod(term, ctx))
    results.extend(_r0399_mk_nat(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_set_theory rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("Cardinal_mk_div_le", "hash_s_slash_t_le_hash_s_star_hash_t", "Not an equality or iff proposition"),
    ("Cardinal_mk_le_of_module", "Cardinal_lift_v_hash_R_le_Cardinal_lift_u_hash_E", "Not an equality or iff proposition"),
    ("Cardinal_cantorFunctionAux_nonneg", "_0_le_cantorFunctionAux_c_f_n", "Not an equality or iff proposition"),
    ("Cardinal_summable_cantor_function", "Summable_cantorFunctionAux_c_f", "Not an equality or iff proposition"),
    ("Cardinal_cantorFunction_le", "cantorFunction_c_f_le_cantorFunction_c_g", "Not an equality or iff proposition"),
    ("Cardinal_increasing_cantorFunction", "cantorFunction_c_f_lt_cantorFunction_c_g", "Not an equality or iff proposition"),
    ("Cardinal_cantorFunction_injective", "Function_Injective_cantorFunction_c", "Not an equality or iff proposition"),
    ("Cardinal_not_countable_real", "not_Set_univ_colon_Set_Countable", "Not an equality or iff proposition"),
    ("Cardinal_Categorical_isComplete", "T_IsComplete", "Not an equality or iff proposition"),
    ("Cardinal_empty_theory_categorical", "k_Categorical_T", "Not an equality or iff proposition"),
    ("Cardinal_empty_infinite_Theory_isComplete", "Language_empty_infiniteTheory_IsComplete", "Not an equality or iff proposition"),
    ("CardinalInterFilter_toCountableInterFilter", "CountableInterFilter_l", "Not an equality or iff proposition"),
    ("CardinalInterFilter_of_cardinalInterFilter_of_le", "CardinalInterFilter_l_a", "Not an equality or iff proposition"),
    ("CardinalInterFilter_of_cardinalInterFilter_of_lt", "CardinalInterFilter_l_a", "Not an equality or iff proposition"),
    ("Ordinal_card_le_preAleph", "o_card_le_preAleph_o", "Not an equality or iff proposition"),
    ("Cardinal_le_preAleph_ord", "c_le_preAleph_c_ord", "Not an equality or iff proposition"),
    ("Cardinal_isNormal_preAleph", "Order_IsNormal_preAleph", "Not an equality or iff proposition"),
    ("Cardinal_preAleph_le_of_strictMono", "preAleph_o_le_f_o", "Not an equality or iff proposition"),
    ("Cardinal_preAleph_le_aleph", "preAleph_o_le_o", "Not an equality or iff proposition"),
    ("Cardinal_isNormal_aleph", "Order_IsNormal_aleph", "Not an equality or iff proposition"),
    ("Cardinal_aleph0_le_aleph", "_0_le_o", "Not an equality or iff proposition"),
    ("Cardinal_aleph_pos", "_0_lt_o", "Not an equality or iff proposition"),
    ("Ordinal_card_le_aleph", "o_card_le_o", "Not an equality or iff proposition"),
    ("Cardinal_le_aleph_ord", "c_le_c_ord", "Not an equality or iff proposition"),
    ("Cardinal_isSuccLimit_omega", "IsSuccLimit_omega_o", "Not an equality or iff proposition"),
    ("Cardinal_aleph0_lt_aleph_one", "_0_lt_1", "Not an equality or iff proposition"),
    ("Cardinal_aleph1_le_mk", "_1_le_hash_a", "Not an equality or iff proposition"),
    ("Cardinal_preBeth_strictMono", "StrictMono_preBeth", "Not an equality or iff proposition"),
    ("Cardinal_preBeth_mono", "Monotone_preBeth", "Not an equality or iff proposition"),
    ("Cardinal_preAleph_le_preBeth", "preAleph_o_le_preBeth_o", "Not an equality or iff proposition"),
    ("Cardinal_isNormal_preBeth", "Order_IsNormal_preBeth", "Not an equality or iff proposition"),
    ("Ordinal_card_le_preBeth", "o_card_le_preBeth_o", "Not an equality or iff proposition"),
    ("Cardinal_le_preBeth_ord", "c_le_preBeth_c_ord", "Not an equality or iff proposition"),
    ("Cardinal_preBeth_le_beth", "preBeth_o_le_o", "Not an equality or iff proposition"),
    ("Cardinal_beth_strictMono", "StrictMono_beth", "Not an equality or iff proposition"),
    ("Cardinal_beth_mono", "Monotone_beth", "Not an equality or iff proposition"),
    ("Cardinal_isNormal_beth", "Order_IsNormal_beth", "Not an equality or iff proposition"),
    ("Cardinal_aleph_le_beth", "o_le_o", "Not an equality or iff proposition"),
    ("Cardinal_aleph0_le_beth", "_0_le_o", "Not an equality or iff proposition"),
    ("Cardinal_beth_pos", "_0_lt_o", "Not an equality or iff proposition"),
    ("Cardinal_beth_ne_zero", "o_ne_0", "Not an equality or iff proposition"),
    ("Ordinal_card_le_beth", "o_card_le_o", "Not an equality or iff proposition"),
    ("Cardinal_le_beth_ord", "c_le_c_ord", "Not an equality or iff proposition"),
    ("Cardinal_mul_lt_of_lt", "a_star_b_lt_c", "Not an equality or iff proposition"),
    ("Cardinal_mul_le_max_of_aleph0_le_left", "a_star_b_le_max_a_b", "Not an equality or iff proposition"),
    ("Cardinal_mul_le_max_of_aleph0_le_right", "a_star_b_le_max_a_b", "Not an equality or iff proposition"),
    ("Cardinal_mul_eq_max", "_unknown", "Empty proposition"),
    ("Cardinal_mul_le_max", "a_star_b_le_max_max_a_b_0", "Not an equality or iff proposition"),
    ("Cardinal_le_mul_left", "a_le_b_star_a", "Not an equality or iff proposition"),
    ("Cardinal_le_mul_right", "a_le_a_star_b", "Not an equality or iff proposition"),
    ("Cardinal_lift_mk_shrink", "_unknown", "Empty proposition"),
    ("Cardinal_lift_mk_shrink", "_unknown", "Empty proposition"),
    ("Cardinal_bddAbove_of_small", "BddAbove_s", "Not an equality or iff proposition"),
    ("Cardinal_bddAbove_range", "BddAbove_Set_range_f", "Not an equality or iff proposition"),
    ("Cardinal_bddAbove_image", "BddAbove_f_prime_prime_s", "Not an equality or iff proposition"),
    ("Cardinal_bddAbove_range_comp", "BddAbove_range_g_comp_f", "Not an equality or iff proposition"),
    ("not_small_cardinal", "not_Small_u_Cardinal_max_u_v", "Not an equality or iff proposition"),
    ("Cardinal_sum_le_lift_mk_mul_iSup_lift", "sum_f_le_lift_hash_i_star_i_lift_f_i", "Not an equality or iff proposition"),
    ("Cardinal_sum_le_lift_mk_mul_iSup", "sum_f_le_lift_hash_i_star_i_f_i", "Not an equality or iff proposition"),
    ("Cardinal_sum_le_mk_mul_iSup", "sum_f_le_hash_i_star_i_f_i", "Not an equality or iff proposition"),
    ("Cardinal_lift_iSup_le", "lift_u_iSup_f_le_t", "Not an equality or iff proposition"),
    ("Cardinal_lift_iSup_le_lift_iSup", "lift_w_prime_iSup_f_le_lift_w_iSup_f_prime", "Not an equality or iff proposition"),
    ("Cardinal_lift_iSup_le_lift_iSup", "_unknown", "Empty proposition"),
    ("Cardinal_lift_iSup_le_sum", "lift_i_f_i_le_sum_f", "Not an equality or iff proposition"),
    ("Cardinal_one_lt_two", "_1_colon_Cardinal_lt_2", "Not an equality or iff proposition"),
    ("Cardinal_exists_finset_le_card", "exists_s_colon_Finset_a_n_le_s_card", "Not an equality or iff proposition"),
    ("Cardinal_card_le_of", "hash_a_le_n", "Not an equality or iff proposition"),
    ("Cardinal_cantor", "_unknown", "Empty proposition"),
    ("Cardinal_natCast_lt_aleph0", "n_colon_Cardinal_u_lt_0", "Not an equality or iff proposition"),
    ("Cardinal_nat_lt_aleph0", "n_colon_Cardinal_u_lt_0", "Not an equality or iff proposition"),
    ("Cardinal_natCast_le_aleph0", "n_colon_Cardinal_u_le_0", "Not an equality or iff proposition"),
    ("Cardinal_ofNat_lt_aleph0", "ofNat_n_lt_0", "Not an equality or iff proposition"),
    ("Cardinal_ofNat_le_aleph0", "ofNat_n_le_0", "Not an equality or iff proposition"),
    ("Cardinal_one_lt_aleph0", "_1_lt_0", "Not an equality or iff proposition"),
    ("Cardinal_one_le_aleph0", "_1_le_0", "Not an equality or iff proposition"),
    ("Cardinal_isSuccPrelimit_aleph0", "IsSuccPrelimit_0", "Not an equality or iff proposition"),
    ("Cardinal_isSuccLimit_aleph0", "IsSuccLimit_0", "Not an equality or iff proposition"),
    ("Cardinal_not_isSuccLimit_of_lt_aleph0", "not_IsSuccLimit_c", "Not an equality or iff proposition"),
    ("Cardinal_aleph0_le_of_isSuccLimit", "_0_le_c", "Not an equality or iff proposition"),
    ("Cardinal_isStrongLimit_aleph0", "IsStrongLimit_0", "Not an equality or iff proposition"),
    ("Cardinal_IsStrongLimit_aleph0_le", "_0_le_c", "Not an equality or iff proposition"),
    ("Cardinal_range_natCast", "range_colon_to_Cardinal_eq_Iio_0", "Not an equality or iff proposition"),
    ("Cardinal_lt_aleph0_of_finite", "hash_a_lt_0", "Not an equality or iff proposition"),
    ("Cardinal_mk_le_aleph0", "hash_a_le_0", "Not an equality or iff proposition"),
    ("Cardinal_aleph0_lt_mk", "_0_lt_hash_a", "Not an equality or iff proposition"),
    ("Cardinal_add_lt_aleph0", "a_plus_b_lt_0", "Not an equality or iff proposition"),
    ("Cardinal_mul_lt_aleph0", "a_star_b_lt_0", "Not an equality or iff proposition"),
    ("Cardinal_aleph0_le_mul_iff", "_unknown", "Empty proposition"),
    ("Cardinal_power_lt_aleph0", "a_pow_b_lt_0", "Not an equality or iff proposition"),
    ("Cardinal_mk_lt_aleph0", "hash_a_lt_0", "Not an equality or iff proposition"),
    ("Cardinal_aleph0_le_mk", "_0_le_hash_a", "Not an equality or iff proposition"),
    ("Infinite_of_cardinalMk_le", "Infinite_b", "Not an equality or iff proposition"),
    ("Cardinal_mk_quot_le", "hash_Quot_r_le_hash_a", "Not an equality or iff proposition"),
    ("Cardinal_mk_quotient_le", "hash_Quotient_s_le_hash_a", "Not an equality or iff proposition"),
    ("Cardinal_mk_subtype_le_of_subset", "hash_Subtype_p_le_hash_Subtype_q", "Not an equality or iff proposition"),
    ("Cardinal_mk_le_mk_of_subset", "hash_s_le_hash_t", "Not an equality or iff proposition"),
    ("Cardinal_mk_monotone", "Monotone_a_colon_eq_Set_a_mk_comp", "Not an equality or iff proposition"),
    ("Cardinal_mk_image_le", "hash_f_prime_prime_s_le_hash_s", "Not an equality or iff proposition"),
    ("Cardinal_mk_image2_le", "hash_image2_f_s_t_le_hash_s_star_hash_t", "Not an equality or iff proposition"),
    ("Cardinal_mk_image_le_lift", "lift_u_hash_f_prime_prime_s_le_lift_v_hash_s", "Not an equality or iff proposition"),
    ("Cardinal_mk_range_le", "hash_range_f_le_hash_a", "Not an equality or iff proposition"),
    ("Cardinal_mk_range_le_lift", "lift_u_hash_range_f_le_lift_v_hash_a", "Not an equality or iff proposition"),
    ("Cardinal_lift_mk_le_lift_mk_of_injective", "Cardinal_lift_v_hash_a_le_Cardinal_lift_u_hash_b", "Not an equality or iff proposition"),
    ("Cardinal_lift_mk_le_lift_mk_of_surjective", "Cardinal_lift_u_hash_b_le_Cardinal_lift_v_hash_a", "Not an equality or iff proposition"),
    ("Cardinal_iSup_mk_le_mk_iUnion", "i_hash_f_i_le_hash_i_f_i", "Not an equality or iff proposition"),
    ("Cardinal_mk_iUnion_le", "hash_i_f_i_le_hash_i_star_i_hash_f_i", "Not an equality or iff proposition"),
    ("Cardinal_mk_iUnion_le_lift", "lift_v_hash_i_f_i_le_lift_u_hash_i_star_i_lift_v_hash_f_i", "Not an equality or iff proposition"),
    ("Cardinal_mk_sUnion_le", "hash_0_A_le_hash_A_star_s_colon_A_hash_s", "Not an equality or iff proposition"),
    ("Cardinal_mk_biUnion_le", "hash_x_in_s_A_x_le_hash_s_star_x_colon_s_hash_A_x_1", "Not an equality or iff proposition"),
    ("Cardinal_mk_biUnion_le_lift", "lift_v_hash_x_in_s_A_x_le_lift_u_hash_s_star_x_colon_s_lift_v_hash_A_x_1", "Not an equality or iff proposition"),
    ("Cardinal_finset_card_lt_aleph0", "hash_s_colon_Set_a_lt_0", "Not an equality or iff proposition"),
    ("Cardinal_mk_union_le", "hash_S_union_T_colon_Set_a_le_hash_S_plus_hash_T", "Not an equality or iff proposition"),
    ("Cardinal_mk_insert_le", "hash_insert_a_s_colon_Set_a_le_hash_s_plus_1", "Not an equality or iff proposition"),
    ("Cardinal_mk_subtype_mono", "hash_x_slash_slash_p_x_le_hash_x_slash_slash_q_x", "Not an equality or iff proposition"),
    ("Cardinal_card_lt_card_of_right_finite", "hash_A_lt_hash_B", "Not an equality or iff proposition"),
    ("Cardinal_card_lt_card_of_left_finite", "hash_A_lt_hash_B", "Not an equality or iff proposition"),
    ("Cardinal_mk_strictMono", "StrictMono_a_colon_eq_Set_a_mk_comp", "Not an equality or iff proposition"),
    ("Cardinal_mk_strictMonoOn", "StrictMonoOn_mk_comp_s_colon_Set_a_pipe_s_Finite", "Not an equality or iff proposition"),
    ("Cardinal_le_mk_diff_add_mk", "hash_S_le_hash_S_bsl_T_colon_Set_a_plus_hash_T", "Not an equality or iff proposition"),
    ("Cardinal_diff_nonempty_of_mk_lt_mk", "T_bsl_S_Nonempty", "Not an equality or iff proposition"),
    ("Cardinal_compl_nonempty_of_mk_lt_mk", "S_Nonempty", "Not an equality or iff proposition"),
    ("Cardinal_mk_preimage_of_injective_lift", "lift_v_hash_f_inv_prime_s_le_lift_u_hash_s", "Not an equality or iff proposition"),
    ("Cardinal_mk_preimage_of_subset_range_lift", "lift_u_hash_s_le_lift_v_hash_f_inv_prime_s", "Not an equality or iff proposition"),
    ("Cardinal_mk_preimage_of_injective", "hash_f_inv_prime_s_le_hash_s", "Not an equality or iff proposition"),
    ("Cardinal_mk_preimage_of_subset_range", "hash_s_le_hash_f_inv_prime_s", "Not an equality or iff proposition"),
    ("Cardinal_mk_subset_ge_of_subset_image_lift", "lift_u_hash_t_le_lift_v_hash_x_in_s_pipe_f_x_in_t_colon_Set_a", "Not an equality or iff proposition"),
    ("Cardinal_mk_subset_ge_of_subset_image", "hash_t_le_hash_x_in_s_pipe_f_x_in_t_colon_Set_a", "Not an equality or iff proposition"),
    ("Cardinal_two_le_iff", "_unknown", "Empty proposition"),
    ("Cardinal_mk_eq_two_iff", "_unknown", "Empty proposition"),
    ("Cardinal_exists_notMem_of_length_lt", "exists_z_colon_a_z_notin_l", "Not an equality or iff proposition"),
    ("Cardinal_exists_ne_ne_of_three_le", "exists_z_colon_a_z_ne_x_and_z_ne_y", "Not an equality or iff proposition"),
    ("Cardinal_le_powerlt", "a_pow_c_le_a_pow_lt_b", "Not an equality or iff proposition"),
    ("Cardinal_powerlt_le_powerlt_left", "a_pow_lt_b_le_a_pow_lt_c", "Not an equality or iff proposition"),
    ("WellFounded_cardinalMk_subtype_lt_min_compl_le", "hash_x_slash_slash_r_x_wf_min_s_hs_le_hash_s", "Not an equality or iff proposition"),
    ("Cardinal_sSup_lt_of_lt_cof_ord", "sSup_s_lt_a", "Not an equality or iff proposition"),
    ("Cardinal_lift_iSup_lt_of_lt_cof_ord", "i_f_i_lt_a", "Not an equality or iff proposition"),
    ("Cardinal_iSup_lt_of_lt_cof_ord", "i_f_i_lt_a", "Not an equality or iff proposition"),
    ("Cardinal_lt_power_cof_ord", "c_lt_c_pow_c_ord_cof", "Not an equality or iff proposition"),
    ("Cardinal_lt_cof_ord_power", "a_lt_b_pow_a_ord_cof", "Not an equality or iff proposition"),
    ("Cardinal_aleph0_lt_continuum", "_0_lt", "Not an equality or iff proposition"),
    ("Cardinal_aleph0_le_continuum", "_0_le", "Not an equality or iff proposition"),
    ("Cardinal_nat_lt_continuum", "n_lt", "Not an equality or iff proposition"),
    ("Cardinal_continuum_pos", "_0_lt", "Not an equality or iff proposition"),
    ("Cardinal_continuum_ne_zero", "ne_0", "Not an equality or iff proposition"),
    ("Cardinal_aleph_one_le_continuum", "_1_le", "Not an equality or iff proposition"),
    ("Cardinal_mk_subtype_le_of_countable_eventually_mem_aux", "hash_t_le_a", "Not an equality or iff proposition"),
    ("Cardinal_mk_subtype_le_of_countable_eventually_mem", "hash_t_le_a", "Not an equality or iff proposition"),
    ("Cardinal_mk_le_of_countable_eventually_mem", "hash_a_le_a", "Not an equality or iff proposition"),
    ("Cardinal_inductionOn", "motive_c", "Not an equality or iff proposition"),
    ("Cardinal_inductionOn_2", "motive_c_1_c_2", "Not an equality or iff proposition"),
    ("Cardinal_inductionOn_3", "motive_c_1_c_2_c_3", "Not an equality or iff proposition"),
    ("Cardinal_induction_on_pi", "motive_f", "Not an equality or iff proposition"),
    ("Cardinal_lift_id", "_unknown", "Empty proposition"),
    ("Cardinal_out_lift_equiv", "Nonempty_lift_v_a_out_a_out", "Not an equality or iff proposition"),
    ("Cardinal_lift_mk_eq", "_unknown", "Empty proposition"),
    ("Cardinal_mk_ne_zero", "hash_a_ne_0", "Not an equality or iff proposition"),
    ("Cardinal_nonempty_out", "Nonempty_x_out", "Not an equality or iff proposition"),
    ("Cardinal_mk_arrow", "hash_a_to_b_eq_lift_u_hash_b_pow_lift_v_hash_a", "Not an equality or iff proposition"),
    ("Cardinal_power_ne_zero", "a_ne_0_to_a_pow_b_ne_0", "Not an equality or iff proposition"),
    ("Cardinal_mk_sigma_congr", "_unknown", "Empty proposition"),
    ("Cardinal_mk_sigma_arrow", "hash_Sigma_f_to_a_eq_hash_Pi_i_f_i_to_a", "Not an equality or iff proposition"),
    ("Cardinal_sum_const", "_unknown", "Empty proposition"),
    ("Cardinal_mk_pi_congr", "_unknown", "Empty proposition"),
    ("Cardinal_prod_const", "_unknown", "Empty proposition"),
    ("Cardinal_aleph0_ne_zero", "_0_ne_0", "Not an equality or iff proposition"),
    ("Cardinal_le_of_dvd", "a_le_b", "Not an equality or iff proposition"),
    ("Cardinal_dvd_of_le_of_aleph0_le", "a_b", "Not an equality or iff proposition"),
    ("Cardinal_prime_of_aleph0_le", "Prime_a", "Not an equality or iff proposition"),
    ("Cardinal_not_irreducible_of_aleph0_le", "not_Irreducible_a", "Not an equality or iff proposition"),
    ("Cardinal_ofENat_strictMono", "StrictMono_ofENat", "Not an equality or iff proposition"),
    ("Cardinal_ofENat_mono", "Monotone_ofENat", "Not an equality or iff proposition"),
    ("Cardinal_ofENat_le_aleph0", "n_le_0", "Not an equality or iff proposition"),
    ("Cardinal_ofENat_injective", "Injective_ofENat", "Not an equality or iff proposition"),
    ("Cardinal_toENatAux_gc", "GaloisConnection_toENatAux", "Not an equality or iff proposition"),
    ("Cardinal_enat_gc", "GaloisConnection_toENat", "Not an equality or iff proposition"),
    ("Cardinal_toENat_strictMonoOn", "StrictMonoOn_toENat_Iic_0", "Not an equality or iff proposition"),
    ("Cardinal_toENat_injOn", "InjOn_toENat_Iic_0", "Not an equality or iff proposition"),
    ("Cardinal_ofENat_toENat_le", "toENat_a_le_a", "Not an equality or iff proposition"),
    ("Cardinal_mk_finsupp_lift_of_fintype", "hash_a_to_0_b_eq_lift_u_hash_b_pow_Fintype_card_a", "Not an equality or iff proposition"),
    ("Cardinal_mk_finsupp_of_fintype", "hash_a_to_0_b_eq_hash_b_pow_Fintype_card_a", "Not an equality or iff proposition"),
    ("Cardinal_mk_finsupp_lift_of_infinite", "hash_a_to_0_b_eq_max_lift_v_hash_a_lift_u_hash_b", "Not an equality or iff proposition"),
    ("Cardinal_mk_finsupp_of_infinite", "hash_a_to_0_b_eq_max_hash_a_hash_b", "Not an equality or iff proposition"),
    ("Cardinal_mk_finsupp_lift_of_infinite", "_unknown", "Empty proposition"),
    ("Cardinal_mk_finsupp_of_infinite", "_unknown", "Empty proposition"),
    ("Cardinal_mk_finsupp_nat", "hash_a_to_0_eq_max_hash_a_0", "Not an equality or iff proposition"),
    ("Cardinal_mk_abelianization_le", "hash_Abelianization_G_le_hash_G", "Not an equality or iff proposition"),
    ("Cardinal_mk_le_of_injective", "hash_a_le_hash_b", "Not an equality or iff proposition"),
    ("Function_Embedding_cardinal_le", "hash_a_le_hash_b", "Not an equality or iff proposition"),
    ("Cardinal_mk_le_of_surjective", "hash_b_le_hash_a", "Not an equality or iff proposition"),
    ("Cardinal_mk_subtype_le", "hash_Subtype_p_le_hash_a", "Not an equality or iff proposition"),
    ("Cardinal_mk_set_le", "hash_s_le_hash_a", "Not an equality or iff proposition"),
    ("Cardinal_lift_mk_le", "_unknown", "Empty proposition"),
    ("Cardinal_mem_range_lift_of_le", "b_le_lift_v_u_a_to_b_in_Set_range_lift_v_u", "Not an equality or iff proposition"),
    ("Cardinal_lift_injective", "Injective_lift_u_v", "Not an equality or iff proposition"),
    ("Cardinal_lift_strictMono", "StrictMono_lift", "Not an equality or iff proposition"),
    ("Cardinal_lift_monotone", "Monotone_lift", "Not an equality or iff proposition"),
    ("Cardinal_zero_le", "forall_a_colon_Cardinal_0_le_a", "Not an equality or iff proposition"),
    ("Cardinal_add_le_add", "_unknown", "Empty proposition"),
    ("Cardinal_zero_power_le", "_0_colon_Cardinal_u_pow_c_le_1", "Not an equality or iff proposition"),
    ("Cardinal_power_le_power_left", "forall_a_b_c_colon_Cardinal_a_ne_0_to_b_le_c_to_a_pow_b_le_a_pow_c", "Not an equality or iff proposition"),
]
