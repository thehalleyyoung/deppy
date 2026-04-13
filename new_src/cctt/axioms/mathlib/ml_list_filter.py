"""Mathlib: List Filter — auto-generated from Mathlib4.

Contains 4 rewrite rules derived from Mathlib theorems.
Plus 1 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_list_filter"
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
# Rewrite rules (4 total)
# ════════════════════════════════════════════════════════════

def _r0000_toFinset_filter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset_filter
    # (s.filter p).toFinset = s.toFinset.filter (p ·)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_filter_p_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("filter", (OOp("p", (OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: List_toFinset_filter"))
    except Exception:
        pass
    return results


def _r0001_filter_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.filter_lt
    # ((Ico n m).filter fun x => x < l) = Ico n (min m l)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("Ico", (OVar("n"), OOp("min", (OVar("m"), args[1],)),))
            results.append((rhs, "Mathlib: List_Ico_filter_lt"))
        except Exception:
            pass
    return results


def _r0002_filter_lt_of_succ_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.filter_lt_of_succ_bot
    # ((Ico n m).filter fun x => x < n + 1) = [n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OSeq((OVar("n"),))
            results.append((rhs, "Mathlib: List_Ico_filter_lt_of_succ_bot"))
        except Exception:
            pass
    return results


def _r0003_diff_eq_filter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nodup.diff_eq_filter
    # ∀ {l₁ l₂ : List α} (_ : l₁.Nodup), l₁.diff l₂ = l₁.filter (· ∉ l₂)   | l₁, [], _ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_1_diff", 1)
    if args is not None:
        try:
            rhs = OOp("l_1_filter", (OOp("not_in", (OVar("_unknown"), args[0])), OVar("pipe"), OVar("l_1"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_Nodup_diff_eq_filter"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_list_filter rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("+", "<", "Ico_n_m_filter", "l_1_diff",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_list_filter axioms."""
    if recognizes(term):
        return 0.5
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_list_filter rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_toFinset_filter(term, ctx))
    results.extend(_r0001_filter_lt(term, ctx))
    results.extend(_r0002_filter_lt_of_succ_bot(term, ctx))
    results.extend(_r0003_diff_eq_filter(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_list_filter rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("List_Nodup_filter", "Nodup_l_to_Nodup_filter_p_l", "Not an equality or iff proposition"),
]
