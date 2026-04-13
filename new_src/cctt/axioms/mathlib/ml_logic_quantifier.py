"""Mathlib: Logic Quantifier — auto-generated from Mathlib4.

Contains 8 rewrite rules derived from Mathlib theorems.
Plus 10 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_logic_quantifier"
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
# Rewrite rules (8 total)
# ════════════════════════════════════════════════════════════

def _r0000_exists_index(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ExistsHomHomCompEqCompAux.exists_index
    # ∃ (i' : I) (hii' : i' ⟶ A.i),     ((D.map hii' ≫ pullback.lift A.a A.b (A.ha.symm.trans A.hb)) ⁻¹'       ((Scheme.Pullba
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 3)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: ExistsHomHomCompEqCompAux_exists_index"))
        except Exception:
            pass
    return results


def _r0001_exists_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ExistsHomHomCompEqCompAux.exists_eq
    # ∃ (k : I) (hki' : k ⟶ A.i'),     (A.𝒰D.pullback₁ (D.map hki')).f j ≫ D.map (hki' ≫ A.hii') ≫ A.a =       (A.𝒰D.pullback₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 9)
    if args is not None:
        try:
            rhs = OOp("A_D_pullback_1_D_map_hki_prime_f", (args[3], args[7], args[5], OOp("hki_prime", (args[7], OVar("A_hii_prime"),)), args[7], OVar("A_b"),))
            results.append((rhs, "Mathlib: ExistsHomHomCompEqCompAux_exists_eq"))
        except Exception:
            pass
    return results


def _r0002_u_exists(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ExistsContDiffBumpBase.u_exists
    # ∃ u : E → ℝ,       ContDiff ℝ ∞ u ∧ (∀ x, u x ∈ Icc (0 : ℝ) 1) ∧ support u = ball 0 1 ∧ ∀ x, u (-x) = u x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("and", (OOp("ball", (OLit(0), OLit(1),)), OOp("forall", (OVar("x"), OVar("u"), OVar("minus_x"),)))), OOp("u", (OVar("x"),))))
            results.append((rhs, "Mathlib: ExistsContDiffBumpBase_u_exists"))
        except Exception:
            pass
    return results


def _r0003_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Exists.snd
    # ∀ h : Exists p, p h.fst   | ⟨_, h⟩ => h  theorem Prop.exists_iff {p : Prop → Prop} : (∃ h, p h) ↔ p False ∨ p True
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p", 3)
    if args is not None:
        try:
            rhs = OOp("or", (OOp("iff", (OOp("gt", (OVar("h_theorem"), OVar("Prop_exists_iff"), OVar("p_colon_Prop_to_Prop"), OVar("colon"), OOp("exists", (args[2], OVar("p"), args[2],)),)), OOp("p", (OLit(False),)))), OOp("p", (OLit(True),))))
            results.append((rhs, "Mathlib: Exists_snd"))
        except Exception:
            pass
    return results


def _r0004_choose_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Classical.choose_eq
    # @Exists.choose _ (· = a) ⟨a, rfl⟩ = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_Exists_choose", 3)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Classical_choose_eq"))
        except Exception:
            pass
    return results


def _r0005_unique(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ExistsUnique.unique
    # y₁ = y₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("y_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("y_2")
            results.append((rhs, "Mathlib: ExistsUnique_unique"))
    except Exception:
        pass
    return results


def _r0006_unique_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ExistsUnique.unique₂
    # y₁ = y₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("y_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("y_2")
            results.append((rhs, "Mathlib: ExistsUnique_unique_2"))
    except Exception:
        pass
    return results


def _r0007_fst(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Exists.fst
    # Exists p → b   | ⟨h, _⟩ => h  theorem Exists.snd {b : Prop} {p : b → Prop} : ∀ h : Exists p, p h.fst   | ⟨_, h⟩ => h  th
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "implies", 2)
    if args is not None:
        try:
            rhs = OOp("or", (OOp("p", (OLit(False),)), OOp("p", (OLit(True),))))
            results.append((rhs, "Mathlib: Exists_fst"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_logic_quantifier rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("==", "D_map_hii_prime_pullback_lift_A_a_A_b_A_ha_symm_trans_A_hb", "Exists", "Icc", "_0", "_unknown", "and", "at_Exists_choose", "b", "exists", "forall", "hki_prime", "i_prime", "implies", "in", "k", "p", "support",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_logic_quantifier axioms."""
    if recognizes(term):
        return 0.5
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_logic_quantifier rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_exists_index(term, ctx))
    results.extend(_r0001_exists_eq(term, ctx))
    results.extend(_r0002_u_exists(term, ctx))
    results.extend(_r0003_snd(term, ctx))
    results.extend(_r0004_choose_eq(term, ctx))
    results.extend(_r0005_unique(term, ctx))
    results.extend(_r0006_unique_2(term, ctx))
    results.extend(_r0007_fst(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_logic_quantifier rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("Exists_2_imp", "exists_a_b_p_a_b_to_exists_a_b_q_a_b", "Not an equality or iff proposition"),
    ("Exists_3_imp", "exists_a_b_c_p_a_b_c_to_exists_a_b_c_q_a_b_c", "Not an equality or iff proposition"),
    ("ExistsUnique_intro", "exists_bang_x_p_x", "Not an equality or iff proposition"),
    ("ExistsUnique_elim", "b", "Proposition too short"),
    ("ExistsUnique_exists", "exists_bang_x_p_x_to_exists_x_p_x_pipe_x_h_eq_gt_x_h_theorem_ExistsUnique_unique_p_colon_a", "Not an equality or iff proposition"),
    ("ExistsUnique_elim_2", "b", "Proposition too short"),
    ("ExistsUnique_intro_2", "exists_bang_x_exists_bang_hx_colon_p_x_q_x_hx", "Not an equality or iff proposition"),
    ("ExistsUnique_exists_2", "exists_x_colon_hx_colon_p_x_q_x_hx", "Not an equality or iff proposition"),
    ("PSet_Equiv_exists_left", "forall_i_exists_j_Equiv_x_Func_i_y_Func_j", "Not an equality or iff proposition"),
    ("PSet_Equiv_exists_right", "forall_j_exists_i_Equiv_x_Func_i_y_Func_j", "Not an equality or iff proposition"),
]
