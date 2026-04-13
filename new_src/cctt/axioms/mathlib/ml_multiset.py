"""Mathlib: Multiset — auto-generated from Mathlib4.

Contains 400 rewrite rules derived from Mathlib theorems.
Plus 198 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_multiset"
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

def _r0000_prod_nsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_nsmul
    # ∀ n : ℕ, (n • m).prod = m.prod ^ n   | 0 =>
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_m_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OVar("m_prod"), OOp("n", (OVar("pipe"), OLit(0), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: Multiset_prod_nsmul"))
    except Exception:
        pass
    return results


def _r0001_prod_map_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_map_pow
    # (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_map_fun_i_eq_gt_f_i_pow_n_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OVar("m_map_f_prod"), OVar("n")))
            results.append((rhs, "Mathlib: Multiset_prod_map_pow"))
    except Exception:
        pass
    return results


def _r0002_prod_toList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_toList
    # s.toList.prod = s.prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_toList_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_prod")
            results.append((rhs, "Mathlib: Multiset_prod_toList"))
    except Exception:
        pass
    return results


def _r0003_prod_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_zero
    # @prod M _ 0 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_prod", 3)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Multiset_prod_zero"))
        except Exception:
            pass
    return results


def _r0004_prod_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_cons
    # prod (a ::ₘ s) = a * prod s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prod", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("a"), OOp("prod", (OVar("s"),))))
            results.append((rhs, "Mathlib: Multiset_prod_cons"))
        except Exception:
            pass
    return results


def _r0005_prod_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_singleton
    # prod {a} = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prod", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Multiset_prod_singleton"))
        except Exception:
            pass
    return results


def _r0006_prod_pair(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_pair
    # ({a, b} : Multiset M).prod = a * b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_b_colon_Multiset_M_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("a"), OVar("b")))
            results.append((rhs, "Mathlib: Multiset_prod_pair"))
    except Exception:
        pass
    return results


def _r0007_pow_count(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.pow_count
    # a ^ s.count a = (s.filter (Eq a)).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("s_filter_Eq_a_prod")
            results.append((rhs, "Mathlib: Multiset_pow_count"))
        except Exception:
            pass
    return results


def _r0008_lcm_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.lcm_cons
    # (a ::ₘ s).lcm = GCDMonoid.lcm a s.lcm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_colon_colon_s_lcm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("GCDMonoid_lcm", (OVar("a"), OVar("s_lcm"),))
            results.append((rhs, "Mathlib: Multiset_lcm_cons"))
    except Exception:
        pass
    return results


def _r0009_lcm_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.lcm_singleton
    # ({a} : Multiset α).lcm = normalize a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_colon_Multiset_a_lcm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("normalize", (OVar("a"),))
            results.append((rhs, "Mathlib: Multiset_lcm_singleton"))
    except Exception:
        pass
    return results


def _r0010_lcm_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.lcm_add
    # (s₁ + s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_1_plus_s_2_lcm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("GCDMonoid_lcm", (OVar("s_1_lcm"), OVar("s_2_lcm"),))
            results.append((rhs, "Mathlib: Multiset_lcm_add"))
    except Exception:
        pass
    return results


def _r0011_map_nsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_nsmul
    # map f (n • s) = n • map f s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("_unknown"), OVar("map"), args[0], OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_map_nsmul"))
        except Exception:
            pass
    return results


def _r0012_bell_mul_eq_lemma(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.bell_mul_eq_lemma
    # ∀ c, x ! ^ c * c ! * ∏ j ∈ Finset.range c, (j * x + x - 1).choose (x - 1) = (x * c)!   | 0 =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("x_star_c_bang", (OVar("pipe"), OLit(0), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: Multiset_bell_mul_eq_lemma"))
        except Exception:
            pass
    return results


def _r0013_toDFinsupp_support(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toDFinsupp_support
    # s.toDFinsupp.support = s.toFinset
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_toDFinsupp_support")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_toFinset")
            results.append((rhs, "Mathlib: Multiset_toDFinsupp_support"))
    except Exception:
        pass
    return results


def _r0014_toDFinsupp_replicate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toDFinsupp_replicate
    # toDFinsupp (Multiset.replicate n a) = DFinsupp.single a n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toDFinsupp", 1)
    if args is not None:
        try:
            rhs = OOp("DFinsupp_single", (OVar("a"), OVar("n"),))
            results.append((rhs, "Mathlib: Multiset_toDFinsupp_replicate"))
        except Exception:
            pass
    return results


def _r0015_toDFinsupp_toMultiset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toDFinsupp_toMultiset
    # DFinsupp.toMultiset (Multiset.toDFinsupp s) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "DFinsupp_toMultiset", 1)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Multiset_toDFinsupp_toMultiset"))
        except Exception:
            pass
    return results


def _r0016_toDFinsupp_inter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toDFinsupp_inter
    # toDFinsupp (s ∩ t) = toDFinsupp s ⊓ toDFinsupp t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toDFinsupp", 1)
    if args is not None:
        try:
            rhs = OOp("toDFinsupp", (OVar("s"), OVar("_unknown"), OVar("toDFinsupp"), OVar("t"),))
            results.append((rhs, "Mathlib: Multiset_toDFinsupp_inter"))
        except Exception:
            pass
    return results


def _r0017_toDFinsupp_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toDFinsupp_union
    # toDFinsupp (s ∪ t) = toDFinsupp s ⊔ toDFinsupp t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toDFinsupp", 1)
    if args is not None:
        try:
            rhs = OOp("toDFinsupp", (OVar("s"), OVar("_unknown"), OVar("toDFinsupp"), OVar("t"),))
            results.append((rhs, "Mathlib: Multiset_toDFinsupp_union"))
        except Exception:
            pass
    return results


def _r0018_antidiagonalTuple_zero_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.Nat.antidiagonalTuple_zero_succ
    # antidiagonalTuple 0 n.succ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "antidiagonalTuple", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Multiset_Nat_antidiagonalTuple_zero_succ"))
        except Exception:
            pass
    return results


def _r0019_mem_antidiagonalTuple(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.Nat.mem_antidiagonalTuple
    # x ∈ antidiagonalTuple k n ↔ ∑ i, x i = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Multiset_Nat_mem_antidiagonalTuple"))
        except Exception:
            pass
    return results


def _r0020_antidiagonalTuple_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.Nat.antidiagonalTuple_two
    # antidiagonalTuple 2 n = (antidiagonal n).map fun i => ![i.1, i.2]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "antidiagonalTuple", 2)
    if args is not None:
        try:
            rhs = OOp("antidiagonal_n_map", (OVar("fun"), OVar("i"), OVar("eq_gt"), OOp("not", (OVar("i_1_i_2"),)),))
            results.append((rhs, "Mathlib: Multiset_Nat_antidiagonalTuple_two"))
        except Exception:
            pass
    return results


def _r0021_keys_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.keys_zero
    # keys (0 : Multiset (Sigma β)) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "keys", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Multiset_keys_zero"))
        except Exception:
            pass
    return results


def _r0022_keys_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.keys_cons
    # keys (⟨a, b⟩ ::ₘ s) = a ::ₘ keys s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "keys", 1)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("colon_colon"), OVar("keys"), OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_keys_cons"))
        except Exception:
            pass
    return results


def _r0023_toFinset_inter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_inter
    # (s ∩ t).toFinset = s.toFinset ∩ t.toFinset
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_inter_t_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("inter", (OVar("s_toFinset"), OVar("t_toFinset")))
            results.append((rhs, "Mathlib: Multiset_toFinset_inter"))
    except Exception:
        pass
    return results


def _r0024_toFinset_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_union
    # (s ∪ t).toFinset = s.toFinset ∪ t.toFinset
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_union_t_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("union", (OVar("s_toFinset"), OVar("t_toFinset")))
            results.append((rhs, "Mathlib: Multiset_toFinset_union"))
    except Exception:
        pass
    return results


def _r0025_toFinset_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_eq_empty
    # m.toFinset = ∅ ↔ m = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("empty"), OVar("m"))), OLit(0)))
            results.append((rhs, "Mathlib: Multiset_toFinset_eq_empty"))
    except Exception:
        pass
    return results


def _r0026_toFinset_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_eq
    # Finset.mk s n = s.toFinset
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Finset_mk", 2)
    if args is not None:
        try:
            rhs = OVar("s_toFinset")
            results.append((rhs, "Mathlib: Multiset_toFinset_eq"))
        except Exception:
            pass
    return results


def _r0027_exists_multiset_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CovBy.exists_multiset_cons
    # ∃ a, a ::ₘ s = t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 4)
    if args is not None:
        try:
            rhs = OVar("t")
            results.append((rhs, "Mathlib: CovBy_exists_multiset_cons"))
        except Exception:
            pass
    return results


def _r0028_toFinset_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_cons
    # toFinset (a ::ₘ s) = insert a (toFinset s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFinset", 1)
    if args is not None:
        try:
            rhs = OOp("insert", (OVar("a"), OOp("toFinset", (OVar("s"),)),))
            results.append((rhs, "Mathlib: Multiset_toFinset_cons"))
        except Exception:
            pass
    return results


def _r0029_toFinset_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_singleton
    # toFinset ({a} : Multiset α) = {a}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFinset", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Multiset_toFinset_singleton"))
        except Exception:
            pass
    return results


def _r0030_noncommFoldr_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.noncommFoldr_cons
    # noncommFoldr f (a ::ₘ s) h b = f a (noncommFoldr f s h' b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "noncommFoldr", 4)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("a"), OOp("noncommFoldr", (args[0], OVar("s"), OVar("h_prime"), args[3],)),))
            results.append((rhs, "Mathlib: Multiset_noncommFoldr_cons"))
        except Exception:
            pass
    return results


def _r0031_noncommFold_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.noncommFold_empty
    # noncommFold op (0 : Multiset α) h a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "noncommFold", 4)
    if args is not None:
        try:
            rhs = args[3]
            results.append((rhs, "Mathlib: Multiset_noncommFold_empty"))
        except Exception:
            pass
    return results


def _r0032_noncommFold_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.noncommFold_cons
    # noncommFold op (a ::ₘ s) h x = op a (noncommFold op s h' x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "noncommFold", 4)
    if args is not None:
        try:
            rhs = OOp("op", (OVar("a"), OOp("noncommFold", (args[0], OVar("s"), OVar("h_prime"), args[3],)),))
            results.append((rhs, "Mathlib: Multiset_noncommFold_cons"))
        except Exception:
            pass
    return results


def _r0033_toFinsupp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinsupp_apply
    # toFinsupp s a = s.count a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFinsupp", 2)
    if args is not None:
        try:
            rhs = OOp("s_count", (args[1],))
            results.append((rhs, "Mathlib: Multiset_toFinsupp_apply"))
        except Exception:
            pass
    return results


def _r0034_toFinsupp_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinsupp_zero
    # toFinsupp (0 : Multiset α) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFinsupp", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Multiset_toFinsupp_zero"))
        except Exception:
            pass
    return results


def _r0035_toFinsupp_toMultiset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinsupp_toMultiset
    # Finsupp.toMultiset (toFinsupp s) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Finsupp_toMultiset", 1)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Multiset_toFinsupp_toMultiset"))
        except Exception:
            pass
    return results


def _r0036_toFinsupp_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinsupp_eq_iff
    # toFinsupp s = f ↔ s = Finsupp.toMultiset f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFinsupp", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("f"), args[0])), OOp("Finsupp_toMultiset", (OVar("f"),))))
            results.append((rhs, "Mathlib: Multiset_toFinsupp_eq_iff"))
        except Exception:
            pass
    return results


def _r0037_map_univ_val_equiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_univ_val_equiv
    # map e univ.val = univ.val
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Multiset_map_univ_val_equiv"))
        except Exception:
            pass
    return results


def _r0038_singleton_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.singleton_add
    # {a} + s = a ::ₘ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("colon_colon"), args[1],))
            results.append((rhs, "Mathlib: Multiset_singleton_add"))
        except Exception:
            pass
    return results


def _r0039_add_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.add_zero
    # s + 0 = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Multiset_add_zero"))
        except Exception:
            pass
    return results


def _r0040_add_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.add_cons
    # s + a ::ₘ t = a ::ₘ (s + t)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("colon_colon"), OOp("+", (args[0], OVar("t"))),))
            results.append((rhs, "Mathlib: Multiset_add_cons"))
        except Exception:
            pass
    return results


def _r0041_add_left_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.add_left_inj
    # s + u = t + u ↔ s = t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("+", (OVar("t"), args[1])), args[0])), OVar("t")))
            results.append((rhs, "Mathlib: Multiset_add_left_inj"))
        except Exception:
            pass
    return results


def _r0042_antidiagonal_map_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.antidiagonal_map_snd
    # (antidiagonal s).map Prod.snd = powerset s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "antidiagonal_s_map", 1)
    if args is not None:
        try:
            rhs = OOp("powerset", (OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_antidiagonal_map_snd"))
        except Exception:
            pass
    return results


def _r0043_antidiagonal_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.antidiagonal_zero
    # @antidiagonal α 0 = {(0, 0)}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_antidiagonal", 2)
    if args is not None:
        try:
            rhs = OVar("_0_0")
            results.append((rhs, "Mathlib: Multiset_antidiagonal_zero"))
        except Exception:
            pass
    return results


def _r0044_antidiagonal_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.antidiagonal_cons
    # antidiagonal (a ::ₘ s) =       map (Prod.map id (cons a)) (antidiagonal s) + map (Prod.map (cons a) id) (antidiagonal s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "antidiagonal", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("map", (OOp("Prod_map", (OVar("id"), OOp("cons", (OVar("a"),)),)), OOp("antidiagonal", (OVar("s"),)),)), OOp("map", (OOp("Prod_map", (OOp("cons", (OVar("a"),)), OVar("id"),)), OOp("antidiagonal", (OVar("s"),)),))))
            results.append((rhs, "Mathlib: Multiset_antidiagonal_cons"))
        except Exception:
            pass
    return results


def _r0045_toList_eq_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toList_eq_nil
    # s.toList = [] ↔ s = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_toList")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OSeq(()), OVar("s"))), OLit(0)))
            results.append((rhs, "Mathlib: Multiset_toList_eq_nil"))
    except Exception:
        pass
    return results


def _r0046_empty_toList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.empty_toList
    # s.toList.isEmpty ↔ s = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Multiset_empty_toList"))
        except Exception:
            pass
    return results


def _r0047_toList_eq_singleton_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toList_eq_singleton_iff
    # m.toList = [a] ↔ m = {a}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_toList")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OSeq((OVar("a"),)), OVar("m"))), OVar("a")))
            results.append((rhs, "Mathlib: Multiset_toList_eq_singleton_iff"))
    except Exception:
        pass
    return results


def _r0048_toList_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toList_singleton
    # ({a} : Multiset α).toList = [a]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_colon_Multiset_a_toList")
        if term.canon() == lhs_pattern.canon():
            rhs = OSeq((OVar("a"),))
            results.append((rhs, "Mathlib: Multiset_toList_singleton"))
    except Exception:
        pass
    return results


def _r0049_length_toList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.length_toList
    # s.toList.length = card s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_toList_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("len", (OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_length_toList"))
    except Exception:
        pass
    return results


def _r0050_join_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.join_cons
    # @join α (s ::ₘ S) = s + join S
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_join", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("s"), OOp("flatten", (OVar("S"),))))
            results.append((rhs, "Mathlib: Multiset_join_cons"))
        except Exception:
            pass
    return results


def _r0051_join_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.join_add
    # @join α (S + T) = join S + join T
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_join", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("flatten", (OVar("S"),)), OOp("flatten", (OVar("T"),))))
            results.append((rhs, "Mathlib: Multiset_join_add"))
        except Exception:
            pass
    return results


def _r0052_singleton_join(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.singleton_join
    # join ({a} : Multiset (Multiset α)) = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "flatten", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Multiset_singleton_join"))
        except Exception:
            pass
    return results


def _r0053_map_join(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_join
    # map f (join S) = join (map (map f) S)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("flatten", (OOp("map", (OOp("map", (args[0],)), OVar("S"),)),))
            results.append((rhs, "Mathlib: Multiset_map_join"))
        except Exception:
            pass
    return results


def _r0054_cons_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.cons_bind
    # (a ::ₘ s).bind f = f a + s.bind f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_colon_colon_s_bind", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("f", (OVar("a"),)), OOp("s_bind", (args[0],))))
            results.append((rhs, "Mathlib: Multiset_cons_bind"))
        except Exception:
            pass
    return results


def _r0055_singleton_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.singleton_bind
    # bind {a} f = f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "flat_map", 2)
    if args is not None:
        try:
            rhs = OOp("f", (args[0],))
            results.append((rhs, "Mathlib: Multiset_singleton_bind"))
        except Exception:
            pass
    return results


def _r0056_add_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.add_bind
    # (s + t).bind f = s.bind f + t.bind f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_plus_t_bind", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("s_bind", (args[0],)), OOp("t_bind", (args[0],))))
            results.append((rhs, "Mathlib: Multiset_add_bind"))
        except Exception:
            pass
    return results


def _r0057_bind_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.bind_add
    # (s.bind fun a => f a + g a) = s.bind f + s.bind g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("s_bind", (OVar("f"),)), OOp("s_bind", (OVar("g"),))))
            results.append((rhs, "Mathlib: Multiset_bind_add"))
        except Exception:
            pass
    return results


def _r0058_bind_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.bind_cons
    # (s.bind fun a => f a ::ₘ g a) = map f s + s.bind g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_bind", 8)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("map", (args[3], OVar("s"),)), OOp("s_bind", (args[6],))))
            results.append((rhs, "Mathlib: Multiset_bind_cons"))
        except Exception:
            pass
    return results


def _r0059_card_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.card_bind
    # card (s.bind f) = (s.map (card ∘ f)).sum
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OVar("s_map_card_comp_f_sum")
            results.append((rhs, "Mathlib: Multiset_card_bind"))
        except Exception:
            pass
    return results


def _r0060_bind_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.bind_congr
    # (∀ a ∈ m, f a = g a) → bind m f = bind m g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "flat_map", 2)
    if args is not None:
        try:
            rhs = OOp("flat_map", (args[0], OVar("g"),))
            results.append((rhs, "Mathlib: Multiset_bind_congr"))
        except Exception:
            pass
    return results


def _r0061_countP_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.countP_zero
    # countP p 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "countP", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Multiset_countP_zero"))
        except Exception:
            pass
    return results


def _r0062_countP_cons_of_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.countP_cons_of_neg
    # ¬p a → countP p (a ::ₘ s) = countP p s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "countP", 2)
    if args is not None:
        try:
            rhs = OOp("countP", (args[0], OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_countP_cons_of_neg"))
        except Exception:
            pass
    return results


def _r0063_countP_False(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.countP_False
    # countP (fun _ => False) s = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "countP", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Multiset_countP_False"))
        except Exception:
            pass
    return results


def _r0064_countP_attach(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.countP_attach
    # s.attach.countP (fun a : {a // a ∈ s} ↦ p a) = s.countP p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_attach_countP", 1)
    if args is not None:
        try:
            rhs = OOp("s_countP", (OVar("p"),))
            results.append((rhs, "Mathlib: Multiset_countP_attach"))
        except Exception:
            pass
    return results


def _r0065_dedup_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.dedup_zero
    # @dedup α _ 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_dedup", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Multiset_dedup_zero"))
        except Exception:
            pass
    return results


def _r0066_dedup_cons_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.dedup_cons_of_mem
    # a ∈ s → dedup (a ::ₘ s) = dedup s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OOp("dedup", (OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_dedup_cons_of_mem"))
        except Exception:
            pass
    return results


def _r0067_dedup_cons_of_notMem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.dedup_cons_of_notMem
    # a ∉ s → dedup (a ::ₘ s) = a ::ₘ dedup s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("colon_colon"), OVar("dedup"), OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_dedup_cons_of_notMem"))
        except Exception:
            pass
    return results


def _r0068_dedup_eq_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.dedup_eq_self
    # dedup s = s ↔ Nodup s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (args[0], OOp("nodup", (args[0],))))
            results.append((rhs, "Mathlib: Multiset_dedup_eq_self"))
        except Exception:
            pass
    return results


def _r0069_dedup_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.dedup_eq_zero
    # dedup s = 0 ↔ s = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: Multiset_dedup_eq_zero"))
        except Exception:
            pass
    return results


def _r0070_lift_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.lift_coe
    # Quotient.lift f h (x : Multiset α) = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Quotient_lift", 3)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("x"),))
            results.append((rhs, "Mathlib: Multiset_lift_coe"))
        except Exception:
            pass
    return results


def _r0071_filter_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_zero
    # filter p 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Multiset_filter_zero"))
        except Exception:
            pass
    return results


def _r0072_filter_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_congr
    # (∀ x ∈ s, p x ↔ q x) → filter p s = filter q s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter", 2)
    if args is not None:
        try:
            rhs = OOp("filter", (OVar("q"), args[1],))
            results.append((rhs, "Mathlib: Multiset_filter_congr"))
        except Exception:
            pass
    return results


def _r0073_filter_cons_of_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_cons_of_neg
    # ¬p a → filter p (a ::ₘ s) = filter p s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter", 2)
    if args is not None:
        try:
            rhs = OOp("filter", (args[0], OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_filter_cons_of_neg"))
        except Exception:
            pass
    return results


def _r0074_filter_false(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_false
    # s.filter (fun _ ↦ False) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_filter", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Multiset_filter_false"))
        except Exception:
            pass
    return results


def _r0075_filterMap_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filterMap_zero
    # filterMap f 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter_map", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Multiset_filterMap_zero"))
        except Exception:
            pass
    return results


def _r0076_filterMap_cons_none(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filterMap_cons_none
    # filterMap f (a ::ₘ s) = filterMap f s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter_map", 2)
    if args is not None:
        try:
            rhs = OOp("filter_map", (args[0], OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_filterMap_cons_none"))
        except Exception:
            pass
    return results


def _r0077_mem_filterMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.mem_filterMap
    # b ∈ filterMap f s ↔ ∃ a, a ∈ s ∧ f a = some b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("some", (OVar("b"),))
            results.append((rhs, "Mathlib: Multiset_mem_filterMap"))
        except Exception:
            pass
    return results


def _r0078_countP_eq_countP_filter_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.countP_eq_countP_filter_add
    # countP p s = (filter q s).countP p + (filter (fun a => ¬q a) s).countP p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "countP", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("filter_q_s_countP", (args[0],)), OOp("filter_fun_a_eq_gt_not_q_a_s_countP", (args[0],))))
            results.append((rhs, "Mathlib: Multiset_countP_eq_countP_filter_add"))
        except Exception:
            pass
    return results


def _r0079_ndinsert_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.ndinsert_zero
    # ndinsert a 0 = {a}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ndinsert", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Multiset_ndinsert_zero"))
        except Exception:
            pass
    return results


def _r0080_ndinsert_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.ndinsert_of_mem
    # a ∈ s → ndinsert a s = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ndinsert", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Multiset_ndinsert_of_mem"))
        except Exception:
            pass
    return results


def _r0081_ndinsert_of_notMem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.ndinsert_of_notMem
    # a ∉ s → ndinsert a s = a ::ₘ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ndinsert", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("colon_colon"), args[1],))
            results.append((rhs, "Mathlib: Multiset_ndinsert_of_notMem"))
        except Exception:
            pass
    return results


def _r0082_mem_ndinsert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.mem_ndinsert
    # a ∈ ndinsert b s ↔ a = b ∨ a ∈ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("or", (OVar("b"), OOp("in", (args[1], OVar("s")))))
            results.append((rhs, "Mathlib: Multiset_mem_ndinsert"))
        except Exception:
            pass
    return results


def _r0083_dedup_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.dedup_add
    # dedup (s + t) = ndunion s (dedup t)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OOp("ndunion", (OVar("s"), OOp("dedup", (OVar("t"),)),))
            results.append((rhs, "Mathlib: Multiset_dedup_add"))
        except Exception:
            pass
    return results


def _r0084_cons_ndinter_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.cons_ndinter_of_mem
    # ndinter (a ::ₘ s) t = a ::ₘ ndinter s t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ndinter", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("colon_colon"), OVar("ndinter"), OVar("s"), args[1],))
            results.append((rhs, "Mathlib: Multiset_cons_ndinter_of_mem"))
        except Exception:
            pass
    return results


def _r0085_ndinter_cons_of_notMem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.ndinter_cons_of_notMem
    # ndinter (a ::ₘ s) t = ndinter s t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ndinter", 2)
    if args is not None:
        try:
            rhs = OOp("ndinter", (OVar("s"), args[1],))
            results.append((rhs, "Mathlib: Multiset_ndinter_cons_of_notMem"))
        except Exception:
            pass
    return results


def _r0086_map_toEnumFinset_fst(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_toEnumFinset_fst
    # m.toEnumFinset.val.map Prod.fst = m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m_toEnumFinset_val_map", 1)
    if args is not None:
        try:
            rhs = OVar("m")
            results.append((rhs, "Mathlib: Multiset_map_toEnumFinset_fst"))
        except Exception:
            pass
    return results


def _r0087_image_toEnumFinset_fst(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.image_toEnumFinset_fst
    # m.toEnumFinset.image Prod.fst = m.toFinset
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m_toEnumFinset_image", 1)
    if args is not None:
        try:
            rhs = OVar("m_toFinset")
            results.append((rhs, "Mathlib: Multiset_image_toEnumFinset_fst"))
        except Exception:
            pass
    return results


def _r0088_coe_fold_l(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.coe_fold_l
    # fold op b l = l.foldl op b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fold", 3)
    if args is not None:
        try:
            rhs = OOp("l_foldl", (args[0], args[1],))
            results.append((rhs, "Mathlib: Multiset_coe_fold_l"))
        except Exception:
            pass
    return results


def _r0089_fold_cons_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.fold_cons_left
    # ∀ (b a : α) (s : Multiset α), (a ::ₘ s).fold op b = a * s.fold op b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_colon_colon_s_fold", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("a"), OOp("s_fold", (args[0], args[1],))))
            results.append((rhs, "Mathlib: Multiset_fold_cons_left"))
        except Exception:
            pass
    return results


def _r0090_fold_cons_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.fold_cons_right
    # (a ::ₘ s).fold op b = s.fold op b * a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_colon_colon_s_fold", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("s_fold", (args[0], args[1],)), OVar("a")))
            results.append((rhs, "Mathlib: Multiset_fold_cons_right"))
        except Exception:
            pass
    return results


def _r0091_bind_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.bind_def
    # (· >>= ·) = @bind α β
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 2)
    if args is not None:
        try:
            rhs = OOp("at_bind", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Multiset_bind_def"))
        except Exception:
            pass
    return results


def _r0092_sup_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.sup_zero
    # (0 : Multiset α).sup = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_Multiset_a_sup")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Multiset_sup_zero"))
    except Exception:
        pass
    return results


def _r0093_sup_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.sup_cons
    # (a ::ₘ s).sup = a ⊔ s.sup
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_colon_colon_s_sup")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("a", (OVar("_unknown"), OVar("s_sup"),))
            results.append((rhs, "Mathlib: Multiset_sup_cons"))
    except Exception:
        pass
    return results


def _r0094_sup_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.sup_singleton
    # ({a} : Multiset α).sup = a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_colon_Multiset_a_sup")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Multiset_sup_singleton"))
    except Exception:
        pass
    return results


def _r0095_sup_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.sup_add
    # (s₁ + s₂).sup = s₁.sup ⊔ s₂.sup
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_1_plus_s_2_sup")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("s_1_sup", (OVar("_unknown"), OVar("s_2_sup"),))
            results.append((rhs, "Mathlib: Multiset_sup_add"))
    except Exception:
        pass
    return results


def _r0096_sup_ndunion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.sup_ndunion
    # (ndunion s₁ s₂).sup = s₁.sup ⊔ s₂.sup
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ndunion_s_1_s_2_sup")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("s_1_sup", (OVar("_unknown"), OVar("s_2_sup"),))
            results.append((rhs, "Mathlib: Multiset_sup_ndunion"))
    except Exception:
        pass
    return results


def _r0097_sup_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.sup_union
    # (s₁ ∪ s₂).sup = s₁.sup ⊔ s₂.sup
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_1_union_s_2_sup")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("s_1_sup", (OVar("_unknown"), OVar("s_2_sup"),))
            results.append((rhs, "Mathlib: Multiset_sup_union"))
    except Exception:
        pass
    return results


def _r0098_sup_ndinsert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.sup_ndinsert
    # (ndinsert a s).sup = a ⊔ s.sup
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ndinsert_a_s_sup")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("a", (OVar("_unknown"), OVar("s_sup"),))
            results.append((rhs, "Mathlib: Multiset_sup_ndinsert"))
    except Exception:
        pass
    return results


def _r0099_map_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_zero
    # map f 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Multiset_map_zero"))
        except Exception:
            pass
    return results


def _r0100_map_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_cons
    # map f (a ::ₘ s) = f a ::ₘ map f s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("a"), OVar("colon_colon"), OVar("map"), args[0], OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_map_cons"))
        except Exception:
            pass
    return results


def _r0101_map_comp_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_comp_cons
    # map f ∘ cons t = cons (f t) ∘ map f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("comp", (OOp("cons", (OOp("f", (OVar("t"),)),)), OOp("map", (OVar("f"),))))
            results.append((rhs, "Mathlib: Multiset_map_comp_cons"))
        except Exception:
            pass
    return results


def _r0102_map_replicate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_replicate
    # (replicate k a).map f = replicate k (f a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "replicate_k_a_map", 1)
    if args is not None:
        try:
            rhs = OOp("replicate", (OVar("k"), OOp("f", (OVar("a"),)),))
            results.append((rhs, "Mathlib: Multiset_map_replicate"))
        except Exception:
            pass
    return results


def _r0103_map_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_add
    # map f (s + t) = map f s + map f t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("map", (args[0], OVar("s"),)), OOp("map", (args[0], OVar("t"),))))
            results.append((rhs, "Mathlib: Multiset_map_add"))
        except Exception:
            pass
    return results


def _r0104_card_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.card_map
    # card (map f s) = card s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("len", (OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_card_map"))
        except Exception:
            pass
    return results


def _r0105_map_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_eq_zero
    # s.map f = 0 ↔ s = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_map", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("s"))), OLit(0)))
            results.append((rhs, "Mathlib: Multiset_map_eq_zero"))
        except Exception:
            pass
    return results


def _r0106_zero_eq_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.zero_eq_map
    # 0 = s.map f ↔ s = 0
    results: List[Tuple[OTerm, str]] = []
    if _is_lit(term, 0):
        try:
            rhs = OOp("==", (OOp("iff", (OOp("s_map", (OVar("f"),)), OVar("s"))), OLit(0)))
            results.append((rhs, "Mathlib: Multiset_zero_eq_map"))
        except Exception:
            pass
    return results


def _r0107_map_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_id
    # map id s = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Multiset_map_id"))
        except Exception:
            pass
    return results


def _r0108_eq_of_mem_map_const(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.eq_of_mem_map_const
    # b₁ = b₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("b_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("b_2")
            results.append((rhs, "Mathlib: Multiset_eq_of_mem_map_const"))
    except Exception:
        pass
    return results


def _r0109_foldl_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.foldl_cons
    # foldl f b (a ::ₘ s) = foldl f (f b a) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "foldl", 3)
    if args is not None:
        try:
            rhs = OOp("foldl", (args[0], OOp("f", (args[1], OVar("a"),)), OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_foldl_cons"))
        except Exception:
            pass
    return results


def _r0110_foldl_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.foldl_add
    # foldl f b (s + t) = foldl f (foldl f b s) t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "foldl", 3)
    if args is not None:
        try:
            rhs = OOp("foldl", (args[0], OOp("foldl", (args[0], args[1], OVar("s"),)), OVar("t"),))
            results.append((rhs, "Mathlib: Multiset_foldl_add"))
        except Exception:
            pass
    return results


def _r0111_antidiagonal_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.Nat.antidiagonal_succ
    # antidiagonal (n + 1) = (0, n + 1) ::ₘ (antidiagonal n).map (Prod.map Nat.succ id)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "antidiagonal", 1)
    if args is not None:
        try:
            rhs = OOp("_0_n_plus_1", (OVar("colon_colon"), OVar("antidiagonal_n_map"), OOp("Prod_map", (OVar("Nat_succ"), OVar("id"),)),))
            results.append((rhs, "Mathlib: Multiset_Nat_antidiagonal_succ"))
        except Exception:
            pass
    return results


def _r0112_pi_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.pi_cons
    # pi (a ::ₘ m) t = (t a).bind fun b => (pi m t).map <| Pi.cons m a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pi", 2)
    if args is not None:
        try:
            rhs = OOp("t_a_bind", (OVar("fun"), OVar("b"), OVar("eq_gt"), OVar("pi_m_t_map"), OVar("lt_pipe"), OVar("Pi_cons"), OVar("m"), OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Multiset_pi_cons"))
        except Exception:
            pass
    return results


def _r0113_powerset_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.powerset_zero
    # @powerset α 0 = {0}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_powerset", 2)
    if args is not None:
        try:
            rhs = OVar("_0")
            results.append((rhs, "Mathlib: Multiset_powerset_zero"))
        except Exception:
            pass
    return results


def _r0114_powerset_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.powerset_cons
    # powerset (a ::ₘ s) = powerset s + map (cons a) (powerset s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "powerset", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("powerset", (OVar("s"),)), OOp("map", (OOp("cons", (OVar("a"),)), OOp("powerset", (OVar("s"),)),))))
            results.append((rhs, "Mathlib: Multiset_powerset_cons"))
        except Exception:
            pass
    return results


def _r0115_powerset_eq_singleton_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.powerset_eq_singleton_zero_iff
    # powerset s = {0} ↔ s = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "powerset", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("_0"), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: Multiset_powerset_eq_singleton_zero_iff"))
        except Exception:
            pass
    return results


def _r0116_powersetCardAux_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.powersetCardAux_nil
    # powersetCardAux (n + 1) (@nil α) = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "powersetCardAux", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: Multiset_powersetCardAux_nil"))
        except Exception:
            pass
    return results


def _r0117_powersetCardAux_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.powersetCardAux_cons
    # powersetCardAux (n + 1) (a :: l) =       powersetCardAux (n + 1) l ++ List.map (cons a) (powersetCardAux n l)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "powersetCardAux", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("powersetCardAux", (OOp("+", (OVar("n"), OLit(1))), OVar("l"),)), OOp("map", (OOp("cons", (OVar("a"),)), OOp("powersetCardAux", (OVar("n"), OVar("l"),)),))))
            results.append((rhs, "Mathlib: Multiset_powersetCardAux_cons"))
        except Exception:
            pass
    return results


def _r0118_powersetCard_zero_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.powersetCard_zero_right
    # @powersetCard α (n + 1) 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_powersetCard", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Multiset_powersetCard_zero_right"))
        except Exception:
            pass
    return results


def _r0119_card_powersetCard(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.card_powersetCard
    # card (powersetCard n s) = Nat.choose (card s) n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("Nat_choose", (OOp("len", (OVar("s"),)), OVar("n"),))
            results.append((rhs, "Mathlib: Multiset_card_powersetCard"))
        except Exception:
            pass
    return results


def _r0120_range_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.range_succ
    # range (succ n) = n ::ₘ range n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("colon_colon"), OVar("range"), OVar("n"),))
            results.append((rhs, "Mathlib: Multiset_range_succ"))
        except Exception:
            pass
    return results


def _r0121_card_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.card_range
    # card (range n) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Multiset_card_range"))
        except Exception:
            pass
    return results


def _r0122_replicate_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.replicate_succ
    # replicate (n + 1) a = a ::ₘ replicate n a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "replicate", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("colon_colon"), OVar("replicate"), OVar("n"), args[1],))
            results.append((rhs, "Mathlib: Multiset_replicate_succ"))
        except Exception:
            pass
    return results


def _r0123_replicate_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.replicate_add
    # replicate (m + n) a = replicate m a + replicate n a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "replicate", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("replicate", (OVar("m"), args[1],)), OOp("replicate", (OVar("n"), args[1],))))
            results.append((rhs, "Mathlib: Multiset_replicate_add"))
        except Exception:
            pass
    return results


def _r0124_mem_replicate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.mem_replicate
    # b ∈ replicate n a ↔ n ≠ 0 ∧ b = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Multiset_mem_replicate"))
        except Exception:
            pass
    return results


def _r0125_sections_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.sections_cons
    # Sections (m ::ₘ s) = m.bind fun a => (Sections s).map (Multiset.cons a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sections", 1)
    if args is not None:
        try:
            rhs = OOp("m_bind", (OVar("fun"), OVar("a"), OVar("eq_gt"), OVar("Sections_s_map"), OOp("Multiset_cons", (OVar("a"),)),))
            results.append((rhs, "Mathlib: Multiset_sections_cons"))
        except Exception:
            pass
    return results


def _r0126_sort_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.sort_zero
    # sort 0 r = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sort", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: Multiset_sort_zero"))
        except Exception:
            pass
    return results


def _r0127_sort_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.sort_singleton
    # sort {a} r = [a]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sort", 2)
    if args is not None:
        try:
            rhs = OSeq((args[0],))
            results.append((rhs, "Mathlib: Multiset_sort_singleton"))
        except Exception:
            pass
    return results


def _r0128_map_sort(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_sort
    # (s.sort r).map f = (s.map f).sort r'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_sort_r_map", 1)
    if args is not None:
        try:
            rhs = OOp("s_map_f_sort", (OVar("r_prime"),))
            results.append((rhs, "Mathlib: Multiset_map_sort"))
        except Exception:
            pass
    return results


def _r0129_disjSum_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.disjSum_zero
    # s.disjSum (0 : Multiset β) = s.map inl
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_disjSum", 1)
    if args is not None:
        try:
            rhs = OOp("s_map", (OVar("inl"),))
            results.append((rhs, "Mathlib: Multiset_disjSum_zero"))
        except Exception:
            pass
    return results


def _r0130_card_disjSum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.card_disjSum
    # Multiset.card (s.disjSum t) = Multiset.card s + Multiset.card t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("len", (OVar("s"),)), OOp("len", (OVar("t"),))))
            results.append((rhs, "Mathlib: Multiset_card_disjSum"))
        except Exception:
            pass
    return results


def _r0131_sym2_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.sym2_eq_zero_iff
    # m.sym2 = 0 ↔ m = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_sym2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("m"))), OLit(0)))
            results.append((rhs, "Mathlib: Multiset_sym2_eq_zero_iff"))
    except Exception:
        pass
    return results


def _r0132_sym2_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.sym2_zero
    # (0 : Multiset α).sym2 = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_Multiset_a_sym2")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Multiset_sym2_zero"))
    except Exception:
        pass
    return results


def _r0133_sym2_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.sym2_cons
    # (m.cons a).sym2 = ((m.cons a).map <| fun b => s(a, b)) + m.sym2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_cons_a_sym2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OOp("m_cons_a_map", (OVar("lt_pipe"), OVar("fun"), OVar("b"), OVar("eq_gt"), OVar("s_a_b"),)), OVar("m_sym2")))
            results.append((rhs, "Mathlib: Multiset_sym2_cons"))
    except Exception:
        pass
    return results


def _r0134_union_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.union_zero
    # s ∪ 0 = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Multiset_union_zero"))
        except Exception:
            pass
    return results


def _r0135_count_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.count_union
    # count a (s ∪ t) = max (count a s) (count a t)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "count", 2)
    if args is not None:
        try:
            rhs = OOp("max", (OOp("count", (args[0], OVar("s"),)), OOp("count", (args[0], OVar("t"),)),))
            results.append((rhs, "Mathlib: Multiset_count_union"))
        except Exception:
            pass
    return results


def _r0136_filter_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_union
    # filter p (s ∪ t) = filter p s ∪ filter p t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter", 2)
    if args is not None:
        try:
            rhs = OOp("union", (OOp("filter", (args[0], OVar("s"),)), OOp("filter", (args[0], OVar("t"),))))
            results.append((rhs, "Mathlib: Multiset_filter_union"))
        except Exception:
            pass
    return results


def _r0137_zero_inter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.zero_inter
    # 0 ∩ s = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Multiset_zero_inter"))
        except Exception:
            pass
    return results


def _r0138_cons_inter_of_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.cons_inter_of_pos
    # a ∈ t → (a ::ₘ s) ∩ t = a ::ₘ s ∩ t.erase a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OOp("inter", (OOp("a", (OVar("colon_colon"), OVar("s"),)), OOp("t_erase", (OVar("a"),))))
            results.append((rhs, "Mathlib: Multiset_cons_inter_of_pos"))
        except Exception:
            pass
    return results


def _r0139_cons_inter_of_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.cons_inter_of_neg
    # a ∉ t → (a ::ₘ s) ∩ t = s ∩ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OOp("inter", (OVar("s"), args[1]))
            results.append((rhs, "Mathlib: Multiset_cons_inter_of_neg"))
        except Exception:
            pass
    return results


def _r0140_inf_eq_inter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.inf_eq_inter
    # s ⊓ t = s ∩ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OOp("inter", (OVar("s"), args[1]))
            results.append((rhs, "Mathlib: Multiset_inf_eq_inter"))
        except Exception:
            pass
    return results


def _r0141_union_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.union_comm
    # s ∪ t = t ∪ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = OOp("union", (args[1], args[0]))
            results.append((rhs, "Mathlib: Multiset_union_comm"))
        except Exception:
            pass
    return results


def _r0142_inter_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.inter_comm
    # s ∩ t = t ∩ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OOp("inter", (args[1], args[0]))
            results.append((rhs, "Mathlib: Multiset_inter_comm"))
        except Exception:
            pass
    return results


def _r0143_empty_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.empty_eq_zero
    # (∅ : Multiset α) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "empty", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Multiset_empty_eq_zero"))
        except Exception:
            pass
    return results


def _r0144_coe_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.coe_eq_zero
    # (l : Multiset α) = 0 ↔ l = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("l"))), OSeq(())))
            results.append((rhs, "Mathlib: Multiset_coe_eq_zero"))
        except Exception:
            pass
    return results


def _r0145_coe_eq_zero_iff_isEmpty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.coe_eq_zero_iff_isEmpty
    # (l : Multiset α) = 0 ↔ l.isEmpty
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l", 3)
    if args is not None:
        try:
            rhs = OOp("iff", (OLit(0), OVar("l_isEmpty")))
            results.append((rhs, "Mathlib: Multiset_coe_eq_zero_iff_isEmpty"))
        except Exception:
            pass
    return results


def _r0146_cons_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.cons_coe
    # (a ::ₘ l : Multiset α) = (a :: l : List α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 5)
    if args is not None:
        try:
            rhs = OOp("a", (args[0], args[1], args[2], OVar("List"), args[4],))
            results.append((rhs, "Mathlib: Multiset_cons_coe"))
        except Exception:
            pass
    return results


def _r0147_cons_inj_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.cons_inj_left
    # a ::ₘ s = b ::ₘ s ↔ a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("b", (args[0], args[1],)), OVar("a"))), OVar("b")))
            results.append((rhs, "Mathlib: Multiset_cons_inj_left"))
        except Exception:
            pass
    return results


def _r0148_recOn_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.recOn_cons
    # (a ::ₘ m).recOn C_0 C_cons C_cons_heq = C_cons a m (m.recOn C_0 C_cons C_cons_heq)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_colon_colon_m_recOn", 3)
    if args is not None:
        try:
            rhs = OOp("C_cons", (OVar("a"), OVar("m"), OOp("m_recOn", (args[0], args[1], args[2],)),))
            results.append((rhs, "Mathlib: Multiset_recOn_cons"))
        except Exception:
            pass
    return results


def _r0149_multinomial_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.multinomial_singleton
    # Multiset.multinomial {n} = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Multiset_multinomial", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Multiset_multinomial_singleton"))
        except Exception:
            pass
    return results


def _r0150_finite_toSet_toFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.finite_toSet_toFinset
    # s.finite_toSet.toFinset = s.toFinset
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_finite_toSet_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_toFinset")
            results.append((rhs, "Mathlib: Multiset_finite_toSet_toFinset"))
    except Exception:
        pass
    return results


def _r0151_esymm_pair_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.esymm_pair_two
    # esymm (x ::ₘ {y}) 2 = x * y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "esymm", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("x"), OVar("y")))
            results.append((rhs, "Mathlib: Multiset_esymm_pair_two"))
        except Exception:
            pass
    return results


def _r0152_disjoint_list_sum_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.disjoint_list_sum_left
    # Disjoint l.sum a ↔ ∀ b ∈ l, Disjoint b a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Disjoint", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("forall", (OVar("b"),)), OOp("l", (OVar("Disjoint"), OVar("b"), args[1],))))
            results.append((rhs, "Mathlib: Multiset_disjoint_list_sum_left"))
        except Exception:
            pass
    return results


def _r0153_lcm_dvd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.lcm_dvd
    # s.lcm ∣ a ↔ ∀ b ∈ s, b ∣ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_lcm", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("forall", (OVar("b"),)), OOp("s", (OVar("b"), args[0], args[1],))))
            results.append((rhs, "Mathlib: Multiset_lcm_dvd"))
        except Exception:
            pass
    return results


def _r0154_toDFinsupp_le_toDFinsupp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toDFinsupp_le_toDFinsupp
    # toDFinsupp s ≤ toDFinsupp t ↔ s ≤ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("s"), OVar("t")))
            results.append((rhs, "Mathlib: Multiset_toDFinsupp_le_toDFinsupp"))
        except Exception:
            pass
    return results


def _r0155_toDFinsupp_lt_toDFinsupp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toDFinsupp_lt_toDFinsupp
    # toDFinsupp s < toDFinsupp t ↔ s < t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("s"), OVar("t")))
            results.append((rhs, "Mathlib: Multiset_toDFinsupp_lt_toDFinsupp"))
        except Exception:
            pass
    return results


def _r0156_nodup_keys(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.nodup_keys
    # m.keys.Nodup ↔ m.NodupKeys
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_keys_Nodup")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("m_NodupKeys")
            results.append((rhs, "Mathlib: Multiset_nodup_keys"))
    except Exception:
        pass
    return results


def _r0157_toFinset_nonempty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_nonempty
    # s.toFinset.Nonempty ↔ s ≠ 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_toFinset_Nonempty")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("!=", (OVar("s"), OLit(0)))
            results.append((rhs, "Mathlib: Multiset_toFinset_nonempty"))
    except Exception:
        pass
    return results


def _r0158_toFinset_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_subset
    # s.toFinset ⊆ t.toFinset ↔ s ⊆ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "subset", 2)
    if args is not None:
        try:
            rhs = OOp("subset", (OVar("s"), OVar("t")))
            results.append((rhs, "Mathlib: Multiset_toFinset_subset"))
        except Exception:
            pass
    return results


def _r0159_toFinset_ssubset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_ssubset
    # s.toFinset ⊂ t.toFinset ↔ s ⊂ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "strict_subset", 2)
    if args is not None:
        try:
            rhs = OOp("strict_subset", (OVar("s"), OVar("t")))
            results.append((rhs, "Mathlib: Multiset_toFinset_ssubset"))
        except Exception:
            pass
    return results


def _r0160_add_le_add_iff_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.add_le_add_iff_left
    # s + t ≤ s + u ↔ t ≤ u
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("t"), OVar("u")))
            results.append((rhs, "Mathlib: Multiset_add_le_add_iff_left"))
        except Exception:
            pass
    return results


def _r0161_mem_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.mem_add
    # a ∈ s + t ↔ a ∈ s ∨ a ∈ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("or", (OOp("in", (OVar("a"), OVar("s"))), OOp("in", (OVar("a"), args[1]))))
            results.append((rhs, "Mathlib: Multiset_mem_add"))
        except Exception:
            pass
    return results


def _r0162_mem_toList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.mem_toList
    # a ∈ s.toList ↔ a ∈ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[0], OVar("s")))
            results.append((rhs, "Mathlib: Multiset_mem_toList"))
        except Exception:
            pass
    return results


def _r0163_mem_join(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.mem_join
    # a ∈ @join α S ↔ ∃ s ∈ S, a ∈ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("exists", (OVar("s"),)), OOp("in", (OOp("S", (args[0],)), OVar("s")))))
            results.append((rhs, "Mathlib: Multiset_mem_join"))
        except Exception:
            pass
    return results


def _r0164_mem_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.mem_bind
    # b ∈ bind s f ↔ ∃ a ∈ s, b ∈ f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("exists", (OVar("a"),)), OOp("in", (OOp("s", (args[0],)), OOp("f", (OVar("a"),))))))
            results.append((rhs, "Mathlib: Multiset_mem_bind"))
        except Exception:
            pass
    return results


def _r0165_mem_dedup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.mem_dedup
    # a ∈ dedup s ↔ a ∈ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[0], OVar("s")))
            results.append((rhs, "Mathlib: Multiset_mem_dedup"))
        except Exception:
            pass
    return results


def _r0166_le_dedup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.le_dedup
    # s ≤ dedup t ↔ s ≤ t ∧ Nodup s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (args[0], OOp("and", (OVar("t"), OOp("nodup", (args[0],))))))
            results.append((rhs, "Mathlib: Multiset_le_dedup"))
        except Exception:
            pass
    return results


def _r0167_mem_filter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.mem_filter
    # a ∈ filter p s ↔ a ∈ s ∧ p a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("in", (args[0], OVar("s"))), OOp("p", (args[0],))))
            results.append((rhs, "Mathlib: Multiset_mem_filter"))
        except Exception:
            pass
    return results


def _r0168_le_filter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.le_filter
    # s ≤ filter p t ↔ s ≤ t ∧ ∀ a ∈ s, p a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (args[0], OOp("and", (OVar("t"), OOp("in", (OOp("forall", (OVar("a"),)), OOp("s", (OVar("p"), OVar("a"),))))))))
            results.append((rhs, "Mathlib: Multiset_le_filter"))
        except Exception:
            pass
    return results


def _r0169_mem_ndunion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.mem_ndunion
    # a ∈ ndunion s t ↔ a ∈ s ∨ a ∈ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("or", (OOp("in", (args[0], OVar("s"))), OOp("in", (args[0], OVar("t")))))
            results.append((rhs, "Mathlib: Multiset_mem_ndunion"))
        except Exception:
            pass
    return results


def _r0170_mem_ndinter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.mem_ndinter
    # a ∈ ndinter s t ↔ a ∈ s ∧ a ∈ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("in", (args[0], OVar("s"))), OOp("in", (args[0], OVar("t")))))
            results.append((rhs, "Mathlib: Multiset_mem_ndinter"))
        except Exception:
            pass
    return results


def _r0171_forall_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.forall_coe
    # (∀ x : m, p x) ↔ ∀ (x : α) (i : Fin (m.count x)), p ⟨x, i⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "forall", 5)
    if args is not None:
        try:
            rhs = OOp("forall", (OOp("x", (args[1], OVar("a"),)), OVar("i_colon_Fin_m_count_x"), args[3], OVar("x_i"),))
            results.append((rhs, "Mathlib: Multiset_forall_coe"))
        except Exception:
            pass
    return results


def _r0172_sup_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.sup_le
    # s.sup ≤ a ↔ ∀ b ∈ s, b ≤ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("in", (OOp("forall", (OVar("b"),)), OOp("s", (OVar("b"),)))), args[1]))
            results.append((rhs, "Mathlib: Multiset_sup_le"))
        except Exception:
            pass
    return results


def _r0173_nodup_sup_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.nodup_sup_iff
    # m.sup.Nodup ↔ ∀ a : Multiset α, a ∈ m → a.Nodup
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_sup_Nodup")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("implies", (OOp("in", (OOp("forall", (OVar("a"), OVar("colon"), OVar("Multiset"), OVar("a"), OVar("a"),)), OVar("m"))), OVar("a_Nodup")))
            results.append((rhs, "Mathlib: Multiset_nodup_sup_iff"))
    except Exception:
        pass
    return results


def _r0174_mem_powerset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.mem_powerset
    # s ∈ powerset t ↔ s ≤ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (args[0], OVar("t")))
            results.append((rhs, "Mathlib: Multiset_mem_powerset"))
        except Exception:
            pass
    return results


def _r0175_range_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.range_subset
    # range m ⊆ range n ↔ m ≤ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "subset", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("m"), OVar("n")))
            results.append((rhs, "Mathlib: Multiset_range_subset"))
        except Exception:
            pass
    return results


def _r0176_le_inter_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.le_inter_iff
    # s ≤ t ∩ u ↔ s ≤ t ∧ s ≤ u
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (args[0], OOp("<=", (OOp("and", (OVar("t"), args[0])), OVar("u")))))
            results.append((rhs, "Mathlib: Multiset_le_inter_iff"))
        except Exception:
            pass
    return results


def _r0177_union_le_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.union_le_iff
    # s ∪ t ≤ u ↔ s ≤ u ∧ t ≤ u
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("s"), OOp("<=", (OOp("and", (args[1], OVar("t"))), args[1]))))
            results.append((rhs, "Mathlib: Multiset_union_le_iff"))
        except Exception:
            pass
    return results


def _r0178_mem_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.mem_Ico
    # x ∈ Ico a b ↔ a ≤ x ∧ x < b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("a"), OOp("<", (OOp("and", (args[0], args[0])), OVar("b")))))
            results.append((rhs, "Mathlib: Multiset_mem_Ico"))
        except Exception:
            pass
    return results


def _r0179_mem_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.mem_Ioc
    # x ∈ Ioc a b ↔ a < x ∧ x ≤ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("<", (OVar("a"), OOp("and", (args[0], args[0])))), OVar("b")))
            results.append((rhs, "Mathlib: Multiset_mem_Ioc"))
        except Exception:
            pass
    return results


def _r0180_mem_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.mem_Ioo
    # x ∈ Ioo a b ↔ a < x ∧ x < b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("a"), OOp("<", (OOp("and", (args[0], args[0])), OVar("b")))))
            results.append((rhs, "Mathlib: Multiset_mem_Ioo"))
        except Exception:
            pass
    return results


def _r0181_sum_map_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.sum_map_div
    # (s.map (fun x ↦ f x / a)).sum = (s.map f).sum / a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_map_fun_x_f_x_slash_a_sum")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("//", (OVar("s_map_f_sum"), OVar("a")))
            results.append((rhs, "Mathlib: Multiset_sum_map_div"))
    except Exception:
        pass
    return results


def _r0182_prod_map_eq_finprod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_map_eq_finprod
    # (s.map f).prod = ∏ᶠ a, f a ^ s.count a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_map_f_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OOp("_unknown", (OVar("a"), OVar("f"), OVar("a"),)), OOp("s_count", (OVar("a"),))))
            results.append((rhs, "Mathlib: Multiset_prod_map_eq_finprod"))
    except Exception:
        pass
    return results


def _r0183_card_finsuppSum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.card_finsuppSum
    # card (f.sum g) = f.sum fun i m ↦ card (g i m)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("f_sum", (OVar("fun"), OVar("i"), OVar("m"), OVar("_unknown"), OVar("card"), OOp("g", (OVar("i"), OVar("m"),)),))
            results.append((rhs, "Mathlib: Multiset_card_finsuppSum"))
        except Exception:
            pass
    return results


def _r0184_prod_map_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_map_prod
    # (m.map fun i ↦ ∏ a ∈ s, f i a).prod = ∏ a ∈ s, (m.map fun i ↦ f i a).prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_map_fun_i_a_in_s_f_i_a_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("a"),)), OOp("s", (OVar("m_map_fun_i_f_i_a_prod"),))))
            results.append((rhs, "Mathlib: Multiset_prod_map_prod"))
    except Exception:
        pass
    return results


def _r0185_toFinset_sum_count_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_sum_count_eq
    # ∑ a ∈ s.toFinset, s.count a = card s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("len", (OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_toFinset_sum_count_eq"))
        except Exception:
            pass
    return results


def _r0186_sum_count_eq_card(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.sum_count_eq_card
    # ∑ a ∈ s, m.count a = card m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("len", (OVar("m"),))
            results.append((rhs, "Mathlib: Multiset_sum_count_eq_card"))
        except Exception:
            pass
    return results


def _r0187_toFinset_sum_count_nsmul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_sum_count_nsmul_eq
    # ∑ a ∈ s.toFinset, s.count a • {a} = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Multiset_toFinset_sum_count_nsmul_eq"))
        except Exception:
            pass
    return results


def _r0188_exists_smul_of_dvd_count(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.exists_smul_of_dvd_count
    # ∃ u : Multiset ι, s = k • u
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 5)
    if args is not None:
        try:
            rhs = OOp("k", (OVar("_unknown"), args[0],))
            results.append((rhs, "Mathlib: Multiset_exists_smul_of_dvd_count"))
        except Exception:
            pass
    return results


def _r0189_prod_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_sum
    # (∑ x ∈ s, f x).prod = ∏ x ∈ s, (f x).prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_in_s_f_x_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("s", (OVar("f_x_prod"),))))
            results.append((rhs, "Mathlib: Multiset_prod_sum"))
    except Exception:
        pass
    return results


def _r0190_card_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.card_sum
    # card (∑ i ∈ s, f i) = ∑ i ∈ s, card (f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("card"), OOp("f", (OVar("i"),)),))))
            results.append((rhs, "Mathlib: Multiset_card_sum"))
        except Exception:
            pass
    return results


def _r0191_prod_erase(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_erase
    # a * (s.erase a).prod = s.prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("s_prod")
            results.append((rhs, "Mathlib: Multiset_prod_erase"))
        except Exception:
            pass
    return results


def _r0192_prod_map_erase(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_map_erase
    # f a * ((m.erase a).map f).prod = (m.map f).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("m_map_f_prod")
            results.append((rhs, "Mathlib: Multiset_prod_map_erase"))
        except Exception:
            pass
    return results


def _r0193_prod_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_add
    # prod (s + t) = prod s * prod t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prod", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("prod", (OVar("s"),)), OOp("prod", (OVar("t"),))))
            results.append((rhs, "Mathlib: Multiset_prod_add"))
        except Exception:
            pass
    return results


def _r0194_prod_filter_mul_prod_filter_not(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_filter_mul_prod_filter_not
    # (s.filter p).prod * (s.filter (fun a ↦ ¬ p a)).prod = s.prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("s_prod")
            results.append((rhs, "Mathlib: Multiset_prod_filter_mul_prod_filter_not"))
        except Exception:
            pass
    return results


def _r0195_prod_map_eq_pow_single(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_map_eq_pow_single
    # (m.map f).prod = f i ^ m.count i
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_map_f_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OOp("f", (OVar("i"),)), OOp("m_count", (OVar("i"),))))
            results.append((rhs, "Mathlib: Multiset_prod_map_eq_pow_single"))
    except Exception:
        pass
    return results


def _r0196_prod_eq_pow_single(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_eq_pow_single
    # s.prod = a ^ s.count a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OVar("a"), OOp("s_count", (OVar("a"),))))
            results.append((rhs, "Mathlib: Multiset_prod_eq_pow_single"))
    except Exception:
        pass
    return results


def _r0197_prod_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_eq_one
    # s.prod = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Multiset_prod_eq_one"))
    except Exception:
        pass
    return results


def _r0198_prod_hom_ne_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_hom_ne_zero
    # (s.map f).prod = f s.prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_map_f_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f", (OVar("s_prod"),))
            results.append((rhs, "Mathlib: Multiset_prod_hom_ne_zero"))
    except Exception:
        pass
    return results


def _r0199_prod_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_hom
    # (s.map f).prod = f s.prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_map_f_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f", (OVar("s_prod"),))
            results.append((rhs, "Mathlib: Multiset_prod_hom"))
    except Exception:
        pass
    return results


def _r0200_prod_hom_2_ne_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_hom₂_ne_zero
    # (s.map fun i => f (f₁ i) (f₂ i)).prod = f (s.map f₁).prod (s.map f₂).prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_map_fun_i_eq_gt_f_f_1_i_f_2_i_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f", (OVar("s_map_f_1_prod"), OVar("s_map_f_2_prod"),))
            results.append((rhs, "Mathlib: Multiset_prod_hom_2_ne_zero"))
    except Exception:
        pass
    return results


def _r0201_prod_hom_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_hom₂
    # (s.map fun i => f (f₁ i) (f₂ i)).prod = f (s.map f₁).prod (s.map f₂).prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_map_fun_i_eq_gt_f_f_1_i_f_2_i_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f", (OVar("s_map_f_1_prod"), OVar("s_map_f_2_prod"),))
            results.append((rhs, "Mathlib: Multiset_prod_hom_2"))
    except Exception:
        pass
    return results


def _r0202_prod_map_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_map_mul
    # (m.map fun i => f i * g i).prod = (m.map f).prod * (m.map g).prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_map_fun_i_eq_gt_f_i_star_g_i_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("m_map_f_prod"), OVar("m_map_g_prod")))
            results.append((rhs, "Mathlib: Multiset_prod_map_mul"))
    except Exception:
        pass
    return results


def _r0203_prod_map_prod_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_map_prod_map
    # prod (m.map fun a => prod <| n.map fun b => f a b) =       prod (n.map fun b => prod <| m.map fun a => f a b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prod", 1)
    if args is not None:
        try:
            rhs = OOp("prod", (OOp("n_map", (OVar("fun"), OVar("b"), OVar("eq_gt"), OVar("prod"), OVar("lt_pipe"), OVar("m_map"), OVar("fun"), OVar("a"), OVar("eq_gt"), OVar("f"), OVar("a"), OVar("b"),)),))
            results.append((rhs, "Mathlib: Multiset_prod_map_prod_map"))
        except Exception:
            pass
    return results


def _r0204_map_multiset_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: map_multiset_prod
    # f s.prod = (s.map f).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OVar("s_map_f_prod")
            results.append((rhs, "Mathlib: map_multiset_prod"))
        except Exception:
            pass
    return results


def _r0205_map_multiset_ne_zero_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: map_multiset_ne_zero_prod
    # f s.prod = (s.map f).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OVar("s_map_f_prod")
            results.append((rhs, "Mathlib: map_multiset_ne_zero_prod"))
        except Exception:
            pass
    return results


def _r0206_map_multiset_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.map_multiset_prod
    # f s.prod = (s.map f).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OVar("s_map_f_prod")
            results.append((rhs, "Mathlib: MonoidHom_map_multiset_prod"))
        except Exception:
            pass
    return results


def _r0207_map_multiset_ne_zero_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulHom.map_multiset_ne_zero_prod
    # f s.prod = (s.map f).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OVar("s_map_f_prod")
            results.append((rhs, "Mathlib: MulHom_map_multiset_ne_zero_prod"))
        except Exception:
            pass
    return results


def _r0208_fst_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.fst_prod
    # s.prod.1 = (s.map Prod.fst).prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_prod_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_map_Prod_fst_prod")
            results.append((rhs, "Mathlib: Multiset_fst_prod"))
    except Exception:
        pass
    return results


def _r0209_snd_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.snd_prod
    # s.prod.2 = (s.map Prod.snd).prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_prod_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_map_Prod_snd_prod")
            results.append((rhs, "Mathlib: Multiset_snd_prod"))
    except Exception:
        pass
    return results


def _r0210_prod_eq_foldr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_eq_foldr
    # prod s = foldr (· * ·) 1 s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prod", 1)
    if args is not None:
        try:
            rhs = OOp("foldr", (OOp("*", (OVar("_unknown"), OVar("_unknown"))), OLit(1), args[0],))
            results.append((rhs, "Mathlib: Multiset_prod_eq_foldr"))
        except Exception:
            pass
    return results


def _r0211_prod_eq_foldl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_eq_foldl
    # prod s = foldl (· * ·) 1 s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prod", 1)
    if args is not None:
        try:
            rhs = OOp("foldl", (OOp("*", (OVar("_unknown"), OVar("_unknown"))), OLit(1), args[0],))
            results.append((rhs, "Mathlib: Multiset_prod_eq_foldl"))
        except Exception:
            pass
    return results


def _r0212_prod_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_coe
    # prod ↑l = l.prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prod", 1)
    if args is not None:
        try:
            rhs = OVar("l_prod")
            results.append((rhs, "Mathlib: Multiset_prod_coe"))
        except Exception:
            pass
    return results


def _r0213_prod_map_toList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_map_toList
    # (s.toList.map f).prod = (s.map f).prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_toList_map_f_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_map_f_prod")
            results.append((rhs, "Mathlib: Multiset_prod_map_toList"))
    except Exception:
        pass
    return results


def _r0214_prod_replicate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_replicate
    # (replicate n a).prod = a ^ n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("replicate_n_a_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OVar("a"), OVar("n")))
            results.append((rhs, "Mathlib: Multiset_prod_replicate"))
    except Exception:
        pass
    return results


def _r0215_prod_map_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_map_one
    # prod (m.map fun _ => (1 : M)) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prod", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Multiset_prod_map_one"))
        except Exception:
            pass
    return results


def _r0216_smul_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.smul_sum
    # r • s.sum = (s.map (r • ·)).sum
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "r", 2)
    if args is not None:
        try:
            rhs = OVar("s_map_r_sum")
            results.append((rhs, "Mathlib: Multiset_smul_sum"))
        except Exception:
            pass
    return results


def _r0217_smul_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.smul_prod
    # b ^ card s • s.prod = (s.map (b • ·)).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("s_map_b_prod")
            results.append((rhs, "Mathlib: Multiset_smul_prod"))
        except Exception:
            pass
    return results


def _r0218_prod_map_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_map_neg
    # (s.map Neg.neg).prod = (-1) ^ card s * s.prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_map_Neg_neg_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OOp("**", (OVar("minus_1"), OOp("len", (OVar("s"),)))), OVar("s_prod")))
            results.append((rhs, "Mathlib: Multiset_prod_map_neg"))
    except Exception:
        pass
    return results


def _r0219_lcm_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.lcm_zero
    # (0 : Multiset α).lcm = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_Multiset_a_lcm")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Multiset_lcm_zero"))
    except Exception:
        pass
    return results


def _r0220_normalize_lcm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.normalize_lcm
    # normalize s.lcm = s.lcm
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "normalize", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Multiset_normalize_lcm"))
        except Exception:
            pass
    return results


def _r0221_lcm_dedup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.lcm_dedup
    # (dedup s).lcm = s.lcm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("dedup_s_lcm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_lcm")
            results.append((rhs, "Mathlib: Multiset_lcm_dedup"))
    except Exception:
        pass
    return results


def _r0222_lcm_ndunion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.lcm_ndunion
    # (ndunion s₁ s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ndunion_s_1_s_2_lcm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("GCDMonoid_lcm", (OVar("s_1_lcm"), OVar("s_2_lcm"),))
            results.append((rhs, "Mathlib: Multiset_lcm_ndunion"))
    except Exception:
        pass
    return results


def _r0223_lcm_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.lcm_union
    # (s₁ ∪ s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_1_union_s_2_lcm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("GCDMonoid_lcm", (OVar("s_1_lcm"), OVar("s_2_lcm"),))
            results.append((rhs, "Mathlib: Multiset_lcm_union"))
    except Exception:
        pass
    return results


def _r0224_lcm_ndinsert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.lcm_ndinsert
    # (ndinsert a s).lcm = GCDMonoid.lcm a s.lcm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ndinsert_a_s_lcm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("GCDMonoid_lcm", (OVar("a"), OVar("s_lcm"),))
            results.append((rhs, "Mathlib: Multiset_lcm_ndinsert"))
    except Exception:
        pass
    return results


def _r0225_sum_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.sum_smul
    # l.sum • x = (l.map fun r ↦ r • x).sum
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_sum", 2)
    if args is not None:
        try:
            rhs = OVar("l_map_fun_r_r_x_sum")
            results.append((rhs, "Mathlib: Multiset_sum_smul"))
        except Exception:
            pass
    return results


def _r0226_sum_smul_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.sum_smul_sum
    # s.sum • t.sum = ((s ×ˢ t).map fun p : R × M ↦ p.fst • p.snd).sum
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_sum", 2)
    if args is not None:
        try:
            rhs = OVar("s_times_t_map_fun_p_colon_R_times_M_p_fst_p_snd_sum")
            results.append((rhs, "Mathlib: Multiset_sum_smul_sum"))
        except Exception:
            pass
    return results


def _r0227_finset_sum_eq_sup_iff_disjoint(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.finset_sum_eq_sup_iff_disjoint
    # i.sum f = i.sup f ↔ ∀ x ∈ i, ∀ y ∈ i, x ≠ y → Disjoint (f x) (f y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_sum", 1)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("iff", (OOp("i_sup", (args[0],)), OOp("in", (OOp("forall", (OVar("x"),)), OOp("in", (OOp("i", (OVar("forall"), OVar("y"),)), OOp("i", (OVar("x"),)))))))), OOp("implies", (OVar("y"), OOp("Disjoint", (OOp("f", (OVar("x"),)), OOp("f", (OVar("y"),)),))))))
            results.append((rhs, "Mathlib: Multiset_finset_sum_eq_sup_iff_disjoint"))
        except Exception:
            pass
    return results


def _r0228_sup_powerset_len(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.sup_powerset_len
    # (Finset.sup (Finset.range (card x + 1)) fun k => x.powersetCard k) = x.powerset
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Finset_sup", 6)
    if args is not None:
        try:
            rhs = OVar("x_powerset")
            results.append((rhs, "Mathlib: Multiset_sup_powerset_len"))
        except Exception:
            pass
    return results


def _r0229_card_le_card_toFinset_add_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.card_le_card_toFinset_add_one_iff
    # m.card ≤ m.toFinset.card + 1 ↔       ∀ x y, 1 < m.count x → 1 < m.count y → x = y ∧ m.count x = 2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("and", (OVar("y"), OOp("m_count", (OVar("x"),)))), OLit(2)))
            results.append((rhs, "Mathlib: Multiset_card_le_card_toFinset_add_one_iff"))
    except Exception:
        pass
    return results


def _r0230_all_one_of_le_one_le_of_prod_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.all_one_of_le_one_le_of_prod_eq_one
    # (∀ x ∈ s, (1 : α) ≤ x) → s.prod = 1 → ∀ x ∈ s, x = (1 : α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("colon"), OVar("a"),))
            results.append((rhs, "Mathlib: Multiset_all_one_of_le_one_le_of_prod_eq_one"))
        except Exception:
            pass
    return results


def _r0231_toFinset_nsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_nsmul
    # ∀ n ≠ 0, (n • s).toFinset = s.toFinset   | 0, h =>
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_s_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("s_toFinset", (OVar("pipe"), OVar("_0"), OVar("h"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: Multiset_toFinset_nsmul"))
    except Exception:
        pass
    return results


def _r0232_toFinset_eq_singleton_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_eq_singleton_iff
    # s.toFinset = {a} ↔ card s ≠ 0 ∧ s = card s • {a}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("!=", (OOp("iff", (OVar("a"), OOp("len", (OVar("s"),)))), OOp("and", (OLit(0), OVar("s"))))), OOp("len", (OVar("s"), OVar("_unknown"), OVar("a"),))))
            results.append((rhs, "Mathlib: Multiset_toFinset_eq_singleton_iff"))
    except Exception:
        pass
    return results


def _r0233_toFinset_card_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_card_eq_one_iff
    # #s.toFinset = 1 ↔ Multiset.card s ≠ 0 ∧ ∃ a : α, s = Multiset.card s • {a}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_s_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("!=", (OOp("iff", (OLit(1), OOp("len", (OVar("s"),)))), OOp("and", (OLit(0), OOp("exists", (OVar("a"), OVar("colon"), OVar("a"), OVar("s"),)))))), OOp("len", (OVar("s"), OVar("_unknown"), OVar("a"),))))
            results.append((rhs, "Mathlib: Multiset_toFinset_card_eq_one_iff"))
    except Exception:
        pass
    return results


def _r0234_nsmul_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.nsmul_cons
    # n • (a ::ₘ s) = n • ({a} : Multiset α) + n • s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("n", (args[0], OOp("a", (OVar("colon"), OVar("Multiset"), OVar("a"),)),)), OOp("n", (args[0], OVar("s"),))))
            results.append((rhs, "Mathlib: Multiset_nsmul_cons"))
        except Exception:
            pass
    return results


def _r0235_card_nsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.card_nsmul
    # card (n • s) = n * card s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("n"), OOp("len", (OVar("s"),))))
            results.append((rhs, "Mathlib: Multiset_card_nsmul"))
        except Exception:
            pass
    return results


def _r0236_nsmul_replicate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.nsmul_replicate
    # n • replicate m a = replicate (n * m) a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n", 4)
    if args is not None:
        try:
            rhs = OOp("replicate", (OOp("*", (OVar("n"), args[2])), args[3],))
            results.append((rhs, "Mathlib: Multiset_nsmul_replicate"))
        except Exception:
            pass
    return results


def _r0237_nsmul_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.nsmul_singleton
    # n • ({a} : Multiset α) = replicate n a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n", 2)
    if args is not None:
        try:
            rhs = OOp("replicate", (OVar("n"), OVar("a"),))
            results.append((rhs, "Mathlib: Multiset_nsmul_singleton"))
        except Exception:
            pass
    return results


def _r0238_map_add_left_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_add_left_Icc
    # (Icc a b).map (c + ·) = Icc (c + a) (c + b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Icc_a_b_map", 1)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("+", (OVar("c"), OVar("a"))), OOp("+", (OVar("c"), OVar("b"))),))
            results.append((rhs, "Mathlib: Multiset_map_add_left_Icc"))
        except Exception:
            pass
    return results


def _r0239_map_add_left_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_add_left_Ico
    # (Ico a b).map (c + ·) = Ico (c + a) (c + b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico_a_b_map", 1)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("+", (OVar("c"), OVar("a"))), OOp("+", (OVar("c"), OVar("b"))),))
            results.append((rhs, "Mathlib: Multiset_map_add_left_Ico"))
        except Exception:
            pass
    return results


def _r0240_map_add_left_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_add_left_Ioc
    # (Ioc a b).map (c + ·) = Ioc (c + a) (c + b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioc_a_b_map", 1)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("+", (OVar("c"), OVar("a"))), OOp("+", (OVar("c"), OVar("b"))),))
            results.append((rhs, "Mathlib: Multiset_map_add_left_Ioc"))
        except Exception:
            pass
    return results


def _r0241_map_add_left_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_add_left_Ioo
    # (Ioo a b).map (c + ·) = Ioo (c + a) (c + b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioo_a_b_map", 1)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OOp("+", (OVar("c"), OVar("a"))), OOp("+", (OVar("c"), OVar("b"))),))
            results.append((rhs, "Mathlib: Multiset_map_add_left_Ioo"))
        except Exception:
            pass
    return results


def _r0242_map_add_right_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_add_right_Icc
    # ((Icc a b).map fun x => x + c) = Icc (a + c) (b + c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("+", (OVar("a"), args[1])), OOp("+", (OVar("b"), args[1])),))
            results.append((rhs, "Mathlib: Multiset_map_add_right_Icc"))
        except Exception:
            pass
    return results


def _r0243_map_add_right_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_add_right_Ico
    # ((Ico a b).map fun x => x + c) = Ico (a + c) (b + c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("+", (OVar("a"), args[1])), OOp("+", (OVar("b"), args[1])),))
            results.append((rhs, "Mathlib: Multiset_map_add_right_Ico"))
        except Exception:
            pass
    return results


def _r0244_map_add_right_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_add_right_Ioc
    # ((Ioc a b).map fun x => x + c) = Ioc (a + c) (b + c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("+", (OVar("a"), args[1])), OOp("+", (OVar("b"), args[1])),))
            results.append((rhs, "Mathlib: Multiset_map_add_right_Ioc"))
        except Exception:
            pass
    return results


def _r0245_map_add_right_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_add_right_Ioo
    # ((Ioo a b).map fun x => x + c) = Ioo (a + c) (b + c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OOp("+", (OVar("a"), args[1])), OOp("+", (OVar("b"), args[1])),))
            results.append((rhs, "Mathlib: Multiset_map_add_right_Ioo"))
        except Exception:
            pass
    return results


def _r0246_trop_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.trop_sum
    # trop s.sum = Multiset.prod (s.map trop)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "trop", 1)
    if args is not None:
        try:
            rhs = OOp("Multiset_prod", (OOp("s_map", (OVar("trop"),)),))
            results.append((rhs, "Mathlib: Multiset_trop_sum"))
        except Exception:
            pass
    return results


def _r0247_untrop_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.untrop_prod
    # untrop s.prod = Multiset.sum (s.map untrop)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "untrop", 1)
    if args is not None:
        try:
            rhs = OOp("sum", (OOp("s_map", (OVar("untrop"),)),))
            results.append((rhs, "Mathlib: Multiset_untrop_prod"))
        except Exception:
            pass
    return results


def _r0248_trop_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.trop_inf
    # trop s.inf = Multiset.sum (s.map trop)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "trop", 1)
    if args is not None:
        try:
            rhs = OOp("sum", (OOp("s_map", (OVar("trop"),)),))
            results.append((rhs, "Mathlib: Multiset_trop_inf"))
        except Exception:
            pass
    return results


def _r0249_untrop_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.untrop_sum
    # untrop s.sum = Multiset.inf (s.map untrop)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "untrop", 1)
    if args is not None:
        try:
            rhs = OOp("Multiset_inf", (OOp("s_map", (OVar("untrop"),)),))
            results.append((rhs, "Mathlib: Multiset_untrop_sum"))
        except Exception:
            pass
    return results


def _r0250_bell_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.bell_zero
    # bell 0 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bell", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Multiset_bell_zero"))
        except Exception:
            pass
    return results


def _r0251_bell_mul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.bell_mul_eq
    # m.bell * (m.map (fun j ↦ j !)).prod * ∏ j ∈ (m.toFinset.erase 0), (m.count j)!       = m.sum !
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("m_sum", (OOp("not", (OVar("_"),)),))
            results.append((rhs, "Mathlib: Multiset_bell_mul_eq"))
        except Exception:
            pass
    return results


def _r0252_bell_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.bell_eq
    # m.bell = m.sum ! / ((m.map (fun j ↦ j !)).prod *       ∏ j ∈ (m.toFinset.erase 0), (m.count j)!)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_bell")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("//", (OOp("m_sum", (OOp("not", (OVar("_"),)),)), OOp("*", (OVar("m_map_fun_j_j_bang_prod"), OOp("in", (OOp("_unknown", (OVar("j"),)), OOp("m_toFinset_erase_0", (OVar("m_count_j_bang"),))))))))
            results.append((rhs, "Mathlib: Multiset_bell_eq"))
    except Exception:
        pass
    return results


def _r0253_toDFinsupp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toDFinsupp_apply
    # Multiset.toDFinsupp s a = s.count a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Multiset_toDFinsupp", 2)
    if args is not None:
        try:
            rhs = OOp("s_count", (args[1],))
            results.append((rhs, "Mathlib: Multiset_toDFinsupp_apply"))
        except Exception:
            pass
    return results


def _r0254_toDFinsupp_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toDFinsupp_singleton
    # toDFinsupp {a} = DFinsupp.single a 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toDFinsupp", 1)
    if args is not None:
        try:
            rhs = OOp("DFinsupp_single", (args[0], OLit(1),))
            results.append((rhs, "Mathlib: Multiset_toDFinsupp_singleton"))
        except Exception:
            pass
    return results


def _r0255_toDFinsupp_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toDFinsupp_inj
    # toDFinsupp s = toDFinsupp t ↔ s = t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toDFinsupp", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("toDFinsupp", (OVar("t"),)), args[0])), OVar("t")))
            results.append((rhs, "Mathlib: Multiset_toDFinsupp_inj"))
        except Exception:
            pass
    return results


def _r0256_antidiagonalTuple_zero_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.Nat.antidiagonalTuple_zero_zero
    # antidiagonalTuple 0 0 = {![]}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "antidiagonalTuple", 2)
    if args is not None:
        try:
            rhs = OVar("bang")
            results.append((rhs, "Mathlib: Multiset_Nat_antidiagonalTuple_zero_zero"))
        except Exception:
            pass
    return results


def _r0257_antidiagonalTuple_zero_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.Nat.antidiagonalTuple_zero_right
    # antidiagonalTuple k 0 = {0}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "antidiagonalTuple", 2)
    if args is not None:
        try:
            rhs = OVar("_0")
            results.append((rhs, "Mathlib: Multiset_Nat_antidiagonalTuple_zero_right"))
        except Exception:
            pass
    return results


def _r0258_antidiagonalTuple_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.Nat.antidiagonalTuple_one
    # antidiagonalTuple 1 n = {![n]}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "antidiagonalTuple", 2)
    if args is not None:
        try:
            rhs = OVar("bang_n")
            results.append((rhs, "Mathlib: Multiset_Nat_antidiagonalTuple_one"))
        except Exception:
            pass
    return results


def _r0259_coe_keys(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.coe_keys
    # keys (l : Multiset (Sigma β)) = (l.keys : Multiset α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "keys", 1)
    if args is not None:
        try:
            rhs = OOp("l_keys", (OVar("colon"), OVar("Multiset"), OVar("a"),))
            results.append((rhs, "Mathlib: Multiset_coe_keys"))
        except Exception:
            pass
    return results


def _r0260_keys_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.keys_singleton
    # keys ({⟨a, b⟩} : Multiset (Sigma β)) = {a}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "keys", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Multiset_keys_singleton"))
        except Exception:
            pass
    return results


def _r0261_toFinset_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_add
    # (s + t).toFinset = s.toFinset ∪ t.toFinset
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_plus_t_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("union", (OVar("s_toFinset"), OVar("t_toFinset")))
            results.append((rhs, "Mathlib: Multiset_toFinset_add"))
    except Exception:
        pass
    return results


def _r0262_toFinset_filter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_filter
    # (s.filter p).toFinset = s.toFinset.filter p
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_filter_p_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("filter", (OVar("p"),))
            results.append((rhs, "Mathlib: Multiset_toFinset_filter"))
    except Exception:
        pass
    return results


def _r0263_toFinset_replicate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_replicate
    # (replicate n a).toFinset = if n = 0 then ∅ else {a}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("replicate_n_a_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("if", (OVar("n"),)), OOp("_0", (OVar("then"), OVar("empty"), OVar("else"), OVar("a"),))))
            results.append((rhs, "Mathlib: Multiset_toFinset_replicate"))
    except Exception:
        pass
    return results


def _r0264_card_toFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.card_toFinset
    # #m.toFinset = Multiset.card m.dedup
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_m_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("len", (OVar("m_dedup"),))
            results.append((rhs, "Mathlib: Multiset_card_toFinset"))
    except Exception:
        pass
    return results


def _r0265_toFinset_card_of_nodup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_card_of_nodup
    # #m.toFinset = Multiset.card m
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_m_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("len", (OVar("m"),))
            results.append((rhs, "Mathlib: Multiset_toFinset_card_of_nodup"))
    except Exception:
        pass
    return results


def _r0266_dedup_card_eq_card_iff_nodup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.dedup_card_eq_card_iff_nodup
    # card m.dedup = card m ↔ m.Nodup
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OOp("len", (OVar("m"),)), OVar("m_Nodup")))
            results.append((rhs, "Mathlib: Multiset_dedup_card_eq_card_iff_nodup"))
        except Exception:
            pass
    return results


def _r0267_toFinset_card_eq_card_iff_nodup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_card_eq_card_iff_nodup
    # #m.toFinset = card m ↔ m.Nodup
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_m_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OOp("len", (OVar("m"),)), OVar("m_Nodup")))
            results.append((rhs, "Mathlib: Multiset_toFinset_card_eq_card_iff_nodup"))
    except Exception:
        pass
    return results


def _r0268_toFinset_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_val
    # s.toFinset.1 = s.dedup
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_toFinset_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_dedup")
            results.append((rhs, "Mathlib: Multiset_toFinset_val"))
    except Exception:
        pass
    return results


def _r0269_toFinset_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.Nodup.toFinset_inj
    # l = l'
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_prime")
            results.append((rhs, "Mathlib: Multiset_Nodup_toFinset_inj"))
    except Exception:
        pass
    return results


def _r0270_toFinset_dedup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_dedup
    # m.dedup.toFinset = m.toFinset
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_dedup_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("m_toFinset")
            results.append((rhs, "Mathlib: Multiset_toFinset_dedup"))
    except Exception:
        pass
    return results


def _r0271_covBy_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.covBy_iff
    # s ⋖ t ↔ ∃ a, a ::ₘ s = t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("t")
            results.append((rhs, "Mathlib: Multiset_covBy_iff"))
        except Exception:
            pass
    return results


def _r0272_isAtom_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.isAtom_iff
    # IsAtom s ↔ ∃ a, s = {a}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Multiset_isAtom_iff"))
        except Exception:
            pass
    return results


def _r0273_grade_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.grade_eq
    # grade ℕ m = card m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "grade", 2)
    if args is not None:
        try:
            rhs = OOp("len", (args[1],))
            results.append((rhs, "Mathlib: Multiset_grade_eq"))
        except Exception:
            pass
    return results


def _r0274_toFinset_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_map
    # (m.map f).toFinset = m.toFinset.image f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_map_f_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("m_toFinset_image", (OVar("f"),))
            results.append((rhs, "Mathlib: Multiset_toFinset_map"))
    except Exception:
        pass
    return results


def _r0275_toFinset_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinset_zero
    # toFinset (0 : Multiset α) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFinset", 1)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Multiset_toFinset_zero"))
        except Exception:
            pass
    return results


def _r0276_map_finset_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_finset_sup
    # map g (s.sup f) = s.sup (map g ∘ f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("s_sup", (OOp("comp", (OOp("map", (args[0],)), OVar("f"))),))
            results.append((rhs, "Mathlib: Multiset_map_finset_sup"))
        except Exception:
            pass
    return results


def _r0277_count_finset_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.count_finset_sup
    # count b (s.sup f) = s.sup fun a => count b (f a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "count", 2)
    if args is not None:
        try:
            rhs = OOp("s_sup", (OVar("fun"), OVar("a"), OVar("eq_gt"), OVar("count"), args[0], OOp("f", (OVar("a"),)),))
            results.append((rhs, "Mathlib: Multiset_count_finset_sup"))
        except Exception:
            pass
    return results


def _r0278_nat_divisors_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.nat_divisors_prod
    # divisors s.prod = (s.map divisors).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "divisors", 1)
    if args is not None:
        try:
            rhs = OVar("s_map_divisors_prod")
            results.append((rhs, "Mathlib: Multiset_nat_divisors_prod"))
        except Exception:
            pass
    return results


def _r0279_noncommFoldr_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.noncommFoldr_coe
    # noncommFoldr f (l : Multiset α) comm b = l.foldr f b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "noncommFoldr", 4)
    if args is not None:
        try:
            rhs = OOp("l_foldr", (args[0], args[3],))
            results.append((rhs, "Mathlib: Multiset_noncommFoldr_coe"))
        except Exception:
            pass
    return results


def _r0280_noncommFoldr_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.noncommFoldr_empty
    # noncommFoldr f (0 : Multiset α) h b = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "noncommFoldr", 4)
    if args is not None:
        try:
            rhs = args[3]
            results.append((rhs, "Mathlib: Multiset_noncommFoldr_empty"))
        except Exception:
            pass
    return results


def _r0281_noncommFoldr_eq_foldr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.noncommFoldr_eq_foldr
    # noncommFoldr f s (fun x _ y _ _ => h.left_comm x y) b = foldr f b s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "noncommFoldr", 4)
    if args is not None:
        try:
            rhs = OOp("foldr", (args[0], args[3], args[1],))
            results.append((rhs, "Mathlib: Multiset_noncommFoldr_eq_foldr"))
        except Exception:
            pass
    return results


def _r0282_noncommFold_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.noncommFold_coe
    # noncommFold op (l : Multiset α) comm a = l.foldr op a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "noncommFold", 4)
    if args is not None:
        try:
            rhs = OOp("l_foldr", (args[0], args[3],))
            results.append((rhs, "Mathlib: Multiset_noncommFold_coe"))
        except Exception:
            pass
    return results


def _r0283_noncommFold_eq_fold(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.noncommFold_eq_fold
    # noncommFold op s (fun x _ y _ _ => Std.Commutative.comm x y) a = fold op a s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "noncommFold", 4)
    if args is not None:
        try:
            rhs = OOp("fold", (args[0], args[3], args[1],))
            results.append((rhs, "Mathlib: Multiset_noncommFold_eq_fold"))
        except Exception:
            pass
    return results


def _r0284_support_sum_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.support_sum_eq
    # s.sum.support = (s.map Finsupp.support).sup
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_sum_support")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_map_Finsupp_support_sup")
            results.append((rhs, "Mathlib: Multiset_support_sum_eq"))
    except Exception:
        pass
    return results


def _r0285_toFinsupp_support(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinsupp_support
    # s.toFinsupp.support = s.toFinset
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_toFinsupp_support")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_toFinset")
            results.append((rhs, "Mathlib: Multiset_toFinsupp_support"))
    except Exception:
        pass
    return results


def _r0286_toFinsupp_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinsupp_add
    # toFinsupp (s + t) = toFinsupp s + toFinsupp t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFinsupp", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("toFinsupp", (OVar("s"),)), OOp("toFinsupp", (OVar("t"),))))
            results.append((rhs, "Mathlib: Multiset_toFinsupp_add"))
        except Exception:
            pass
    return results


def _r0287_toFinsupp_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinsupp_singleton
    # toFinsupp ({a} : Multiset α) = Finsupp.single a 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFinsupp", 1)
    if args is not None:
        try:
            rhs = OOp("Finsupp_single", (OVar("a"), OLit(1),))
            results.append((rhs, "Mathlib: Multiset_toFinsupp_singleton"))
        except Exception:
            pass
    return results


def _r0288_toFinsupp_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinsupp_union
    # toFinsupp (s ∪ t) = toFinsupp s ⊔ toFinsupp t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFinsupp", 1)
    if args is not None:
        try:
            rhs = OOp("toFinsupp", (OVar("s"), OVar("_unknown"), OVar("toFinsupp"), OVar("t"),))
            results.append((rhs, "Mathlib: Multiset_toFinsupp_union"))
        except Exception:
            pass
    return results


def _r0289_toFinsupp_inter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinsupp_inter
    # toFinsupp (s ∩ t) = toFinsupp s ⊓ toFinsupp t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFinsupp", 1)
    if args is not None:
        try:
            rhs = OOp("toFinsupp", (OVar("s"), OVar("_unknown"), OVar("toFinsupp"), OVar("t"),))
            results.append((rhs, "Mathlib: Multiset_toFinsupp_inter"))
        except Exception:
            pass
    return results


def _r0290_toFinsupp_sum_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toFinsupp_sum_eq
    # s.toFinsupp.sum (fun _ ↦ id) = Multiset.card s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_toFinsupp_sum", 1)
    if args is not None:
        try:
            rhs = OOp("len", (OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_toFinsupp_sum_eq"))
        except Exception:
            pass
    return results


def _r0291_count_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.count_univ
    # count a Finset.univ.val = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "count", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Multiset_count_univ"))
        except Exception:
            pass
    return results


def _r0292_bijective_iff_map_univ_eq_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.bijective_iff_map_univ_eq_univ
    # f.Bijective ↔ map f (Finset.univ : Finset α).val = univ.val
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("univ_val")
            results.append((rhs, "Mathlib: Multiset_bijective_iff_map_univ_eq_univ"))
        except Exception:
            pass
    return results


def _r0293_lists_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.lists_coe
    # lists (l : Multiset α) = l.permutations
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lists", 1)
    if args is not None:
        try:
            rhs = OVar("l_permutations")
            results.append((rhs, "Mathlib: Multiset_lists_coe"))
        except Exception:
            pass
    return results


def _r0294_mem_lists_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.mem_lists_iff
    # l ∈ lists s ↔ s = ⟦l⟧
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("l")
            results.append((rhs, "Mathlib: Multiset_mem_lists_iff"))
        except Exception:
            pass
    return results


def _r0295_coe_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.coe_add
    # (s + t : Multiset α) = (s ++ t : List α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (args[0], OOp("t", (OVar("colon"), OVar("List"), OVar("a"),))))
            results.append((rhs, "Mathlib: Multiset_coe_add"))
        except Exception:
            pass
    return results


def _r0296_add_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.add_comm
    # s + t = t + s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[1], args[0]))
            results.append((rhs, "Mathlib: Multiset_add_comm"))
        except Exception:
            pass
    return results


def _r0297_add_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.add_assoc
    # s + t + u = s + (t + u)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], OOp("+", (OVar("t"), OVar("u")))))
            results.append((rhs, "Mathlib: Multiset_add_assoc"))
        except Exception:
            pass
    return results


def _r0298_zero_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.zero_add
    # 0 + s = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Multiset_zero_add"))
        except Exception:
            pass
    return results


def _r0299_le_iff_exists_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.le_iff_exists_add
    # s ≤ t ↔ ∃ u, t = s + u
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], OVar("u")))
            results.append((rhs, "Mathlib: Multiset_le_iff_exists_add"))
        except Exception:
            pass
    return results


def _r0300_cons_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.cons_add
    # a ::ₘ s + t = a ::ₘ (s + t)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("colon_colon"), OOp("+", (OVar("s"), args[1])),))
            results.append((rhs, "Mathlib: Multiset_cons_add"))
        except Exception:
            pass
    return results


def _r0301_countP_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.countP_add
    # countP p (s + t) = countP p s + countP p t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "countP", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("countP", (args[0], OVar("s"),)), OOp("countP", (args[0], OVar("t"),))))
            results.append((rhs, "Mathlib: Multiset_countP_add"))
        except Exception:
            pass
    return results


def _r0302_count_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.count_add
    # ∀ s t, count a (s + t) = count a s + count a t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "count", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("count", (args[0], OVar("s"),)), OOp("count", (args[0], OVar("t"),))))
            results.append((rhs, "Mathlib: Multiset_count_add"))
        except Exception:
            pass
    return results


def _r0303_add_right_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.add_right_inj
    # s + t = s + u ↔ t = u
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("+", (args[0], OVar("u"))), args[1])), OVar("u")))
            results.append((rhs, "Mathlib: Multiset_add_right_inj"))
        except Exception:
            pass
    return results


def _r0304_card_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.card_add
    # card (s + t) = card s + card t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("len", (OVar("s"),)), OOp("len", (OVar("t"),))))
            results.append((rhs, "Mathlib: Multiset_card_add"))
        except Exception:
            pass
    return results


def _r0305_antidiagonal_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.antidiagonal_coe
    # @antidiagonal α l = revzip (powersetAux l)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_antidiagonal", 2)
    if args is not None:
        try:
            rhs = OOp("revzip", (OOp("powersetAux", (args[1],)),))
            results.append((rhs, "Mathlib: Multiset_antidiagonal_coe"))
        except Exception:
            pass
    return results


def _r0306_mem_antidiagonal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.mem_antidiagonal
    # x ∈ antidiagonal s ↔ x.1 + x.2 = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Multiset_mem_antidiagonal"))
        except Exception:
            pass
    return results


def _r0307_antidiagonal_map_fst(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.antidiagonal_map_fst
    # (antidiagonal s).map Prod.fst = powerset s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "antidiagonal_s_map", 1)
    if args is not None:
        try:
            rhs = OOp("powerset", (OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_antidiagonal_map_fst"))
        except Exception:
            pass
    return results


def _r0308_antidiagonal_eq_map_powerset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.antidiagonal_eq_map_powerset
    # s.antidiagonal = s.powerset.map fun t ↦ (s - t, t)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_antidiagonal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("s_powerset_map", (OVar("fun"), OVar("t"), OVar("_unknown"), OOp("-", (OVar("s"), OOp("t", (OVar("t"),)))),))
            results.append((rhs, "Mathlib: Multiset_antidiagonal_eq_map_powerset"))
    except Exception:
        pass
    return results


def _r0309_card_antidiagonal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.card_antidiagonal
    # card (antidiagonal s) = 2 ^ card s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OLit(2), OOp("len", (OVar("s"),))))
            results.append((rhs, "Mathlib: Multiset_card_antidiagonal"))
        except Exception:
            pass
    return results


def _r0310_coe_toList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.coe_toList
    # (s.toList : Multiset α) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_toList", 3)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Multiset_coe_toList"))
        except Exception:
            pass
    return results


def _r0311_toList_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.toList_zero
    # (Multiset.toList 0 : List α) = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Multiset_toList", 4)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: Multiset_toList_zero"))
        except Exception:
            pass
    return results


def _r0312_join_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.join_zero
    # @join α 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_join", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Multiset_join_zero"))
        except Exception:
            pass
    return results


def _r0313_card_join(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.card_join
    # card (@join α S) = sum (map card S)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("sum", (OOp("map", (OVar("card"), OVar("S"),)),))
            results.append((rhs, "Mathlib: Multiset_card_join"))
        except Exception:
            pass
    return results


def _r0314_prod_join(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_join
    # prod (join S) = prod (map prod S)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prod", 1)
    if args is not None:
        try:
            rhs = OOp("prod", (OOp("map", (OVar("prod"), OVar("S"),)),))
            results.append((rhs, "Mathlib: Multiset_prod_join"))
        except Exception:
            pass
    return results


def _r0315_filter_join(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_join
    # filter p (join S) = join (map (filter p) S)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter", 2)
    if args is not None:
        try:
            rhs = OOp("flatten", (OOp("map", (OOp("filter", (args[0],)), OVar("S"),)),))
            results.append((rhs, "Mathlib: Multiset_filter_join"))
        except Exception:
            pass
    return results


def _r0316_filterMap_join(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filterMap_join
    # filterMap f (join S) = join (map (filterMap f) S)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter_map", 2)
    if args is not None:
        try:
            rhs = OOp("flatten", (OOp("map", (OOp("filter_map", (args[0],)), OVar("S"),)),))
            results.append((rhs, "Mathlib: Multiset_filterMap_join"))
        except Exception:
            pass
    return results


def _r0317_coe_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.coe_bind
    # (@bind α β l fun a => f a) = l.flatMap f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_bind", 8)
    if args is not None:
        try:
            rhs = OOp("l_flatMap", (args[6],))
            results.append((rhs, "Mathlib: Multiset_coe_bind"))
        except Exception:
            pass
    return results


def _r0318_zero_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.zero_bind
    # bind 0 f = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "flat_map", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Multiset_zero_bind"))
        except Exception:
            pass
    return results


def _r0319_bind_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.bind_singleton
    # (s.bind fun x => ({f x} : Multiset β)) = map f s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_bind", 4)
    if args is not None:
        try:
            rhs = OOp("map", (OVar("f"), OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_bind_singleton"))
        except Exception:
            pass
    return results


def _r0320_map_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_bind
    # map f (bind m n) = bind m fun a => map f (n a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("flat_map", (OVar("m"), OVar("fun"), OVar("a"), OVar("eq_gt"), OVar("map"), args[0], OOp("n", (OVar("a"),)),))
            results.append((rhs, "Mathlib: Multiset_map_bind"))
        except Exception:
            pass
    return results


def _r0321_bind_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.bind_map
    # bind (map f m) n = bind m fun a => n (f a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "flat_map", 2)
    if args is not None:
        try:
            rhs = OOp("flat_map", (OVar("m"), OVar("fun"), OVar("a"), OVar("eq_gt"), args[1], OOp("f", (OVar("a"),)),))
            results.append((rhs, "Mathlib: Multiset_bind_map"))
        except Exception:
            pass
    return results


def _r0322_bind_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.bind_assoc
    # (s.bind f).bind g = s.bind fun a => (f a).bind g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_bind_f_bind", 1)
    if args is not None:
        try:
            rhs = OOp("s_bind", (OVar("fun"), OVar("a"), OVar("eq_gt"), OVar("f_a_bind"), args[0],))
            results.append((rhs, "Mathlib: Multiset_bind_assoc"))
        except Exception:
            pass
    return results


def _r0323_bind_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.bind_bind
    # ((bind m) fun a => (bind n) fun b => f a b) = (bind n) fun b => (bind m) fun a => f a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bind_m", 10)
    if args is not None:
        try:
            rhs = OOp("bind_n", (args[4], args[9], args[6], OOp("flat_map", (OVar("m"),)), args[4], args[8], args[6], args[7], args[8], args[9],))
            results.append((rhs, "Mathlib: Multiset_bind_bind"))
        except Exception:
            pass
    return results


def _r0324_bind_map_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.bind_map_comm
    # ((bind m) fun a => n.map fun b => f a b) = (bind n) fun b => m.map fun a => f a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bind_m", 10)
    if args is not None:
        try:
            rhs = OOp("bind_n", (args[4], args[9], args[6], OVar("m_map"), args[4], args[8], args[6], args[7], args[8], args[9],))
            results.append((rhs, "Mathlib: Multiset_bind_map_comm"))
        except Exception:
            pass
    return results


def _r0325_filter_eq_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_eq_bind
    # filter p m = bind m (fun a => if p a then {a} else 0)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter", 2)
    if args is not None:
        try:
            rhs = OOp("flat_map", (args[1], OOp("fun", (OVar("a"), OVar("eq_gt"), OVar("if"), args[0], OVar("a"), OVar("then"), OVar("a"), OVar("else"), OLit(0),)),))
            results.append((rhs, "Mathlib: Multiset_filter_eq_bind"))
        except Exception:
            pass
    return results


def _r0326_bind_filter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.bind_filter
    # bind (filter p m) f = bind m (fun a => if p a then f a else 0)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "flat_map", 2)
    if args is not None:
        try:
            rhs = OOp("flat_map", (OVar("m"), OOp("fun", (OVar("a"), OVar("eq_gt"), OVar("if"), OVar("p"), OVar("a"), OVar("then"), args[1], OVar("a"), OVar("else"), OLit(0),)),))
            results.append((rhs, "Mathlib: Multiset_bind_filter"))
        except Exception:
            pass
    return results


def _r0327_filter_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_bind
    # filter p (bind m f) = bind m (fun a => filter p (f a))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter", 2)
    if args is not None:
        try:
            rhs = OOp("flat_map", (OVar("m"), OOp("fun", (OVar("a"), OVar("eq_gt"), OVar("filter"), args[0], OOp("f", (OVar("a"),)),)),))
            results.append((rhs, "Mathlib: Multiset_filter_bind"))
        except Exception:
            pass
    return results


def _r0328_filterMap_eq_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filterMap_eq_bind
    # filterMap f m = bind m (fun a => ((f a).map singleton).getD 0)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter_map", 2)
    if args is not None:
        try:
            rhs = OOp("flat_map", (args[1], OOp("fun", (OVar("a"), OVar("eq_gt"), OVar("f_a_map_singleton_getD"), OLit(0),)),))
            results.append((rhs, "Mathlib: Multiset_filterMap_eq_bind"))
        except Exception:
            pass
    return results


def _r0329_bind_filterMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.bind_filterMap
    # bind (filterMap f m) g = bind m (fun a => ((f a).map g).getD 0)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "flat_map", 2)
    if args is not None:
        try:
            rhs = OOp("flat_map", (OVar("m"), OOp("fun", (OVar("a"), OVar("eq_gt"), OVar("f_a_map_g_getD"), OLit(0),)),))
            results.append((rhs, "Mathlib: Multiset_bind_filterMap"))
        except Exception:
            pass
    return results


def _r0330_filterMap_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filterMap_bind
    # filterMap g (bind m f) = bind m (fun a => filterMap g (f a))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter_map", 2)
    if args is not None:
        try:
            rhs = OOp("flat_map", (OVar("m"), OOp("fun", (OVar("a"), OVar("eq_gt"), OVar("filterMap"), args[0], OOp("f", (OVar("a"),)),)),))
            results.append((rhs, "Mathlib: Multiset_filterMap_bind"))
        except Exception:
            pass
    return results


def _r0331_prod_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.prod_bind
    # (s.bind t).prod = (s.map fun a => (t a).prod).prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_bind_t_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_map_fun_a_eq_gt_t_a_prod_prod")
            results.append((rhs, "Mathlib: Multiset_prod_bind"))
    except Exception:
        pass
    return results


def _r0332_count_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.count_sum
    # count a (map f m).sum = sum (m.map fun b => count a <| f b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "count", 2)
    if args is not None:
        try:
            rhs = OOp("sum", (OOp("m_map", (OVar("fun"), OVar("b"), OVar("eq_gt"), OVar("count"), args[0], OVar("lt_pipe"), OVar("f"), OVar("b"),)),))
            results.append((rhs, "Mathlib: Multiset_count_sum"))
        except Exception:
            pass
    return results


def _r0333_count_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.count_bind
    # count a (bind m f) = sum (m.map fun b => count a <| f b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "count", 2)
    if args is not None:
        try:
            rhs = OOp("sum", (OOp("m_map", (OVar("fun"), OVar("b"), OVar("eq_gt"), OVar("count"), args[0], OVar("lt_pipe"), OVar("f"), OVar("b"),)),))
            results.append((rhs, "Mathlib: Multiset_count_bind"))
        except Exception:
            pass
    return results


def _r0334_attach_bind_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.attach_bind_coe
    # (s.attach.bind fun i => f i) = s.bind f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_attach_bind", 5)
    if args is not None:
        try:
            rhs = OOp("s_bind", (args[3],))
            results.append((rhs, "Mathlib: Multiset_attach_bind_coe"))
        except Exception:
            pass
    return results


def _r0335_dedup_bind_dedup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.dedup_bind_dedup
    # (s.dedup.bind f).dedup = (s.bind f).dedup
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_dedup_bind_f_dedup")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_bind_f_dedup")
            results.append((rhs, "Mathlib: Multiset_dedup_bind_dedup"))
    except Exception:
        pass
    return results


def _r0336_fold_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.fold_bind
    # (s.bind t).fold op ((s.map b).fold op b₀) =     (s.map fun i => (t i).fold op (b i)).fold op b₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_bind_t_fold", 2)
    if args is not None:
        try:
            rhs = OOp("s_map_fun_i_eq_gt_t_i_fold_op_b_i_fold", (args[0], OVar("b_0"),))
            results.append((rhs, "Mathlib: Multiset_fold_bind"))
        except Exception:
            pass
    return results


def _r0337_coe_countP(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.coe_countP
    # countP p l = l.countP p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "countP", 2)
    if args is not None:
        try:
            rhs = OOp("l_countP", (args[0],))
            results.append((rhs, "Mathlib: Multiset_coe_countP"))
        except Exception:
            pass
    return results


def _r0338_countP_cons_of_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.countP_cons_of_pos
    # p a → countP p (a ::ₘ s) = countP p s + 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "countP", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("countP", (args[0], OVar("s"),)), OLit(1)))
            results.append((rhs, "Mathlib: Multiset_countP_cons_of_pos"))
        except Exception:
            pass
    return results


def _r0339_countP_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.countP_cons
    # countP p (b ::ₘ s) = countP p s + if p b then 1 else 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "countP", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("countP", (args[0], OVar("s"),)), OOp("if", (args[0], OVar("b"), OVar("then"), OLit(1), OVar("else"), OLit(0),))))
            results.append((rhs, "Mathlib: Multiset_countP_cons"))
        except Exception:
            pass
    return results


def _r0340_card_eq_countP_add_countP(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.card_eq_countP_add_countP
    # card s = countP p s + countP (fun x => ¬p x) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("countP", (OVar("p"), args[0],)), OOp("countP", (OOp("fun", (OVar("x"), OVar("eq_gt"), OOp("not", (OVar("p"),)), OVar("x"),)), args[0],))))
            results.append((rhs, "Mathlib: Multiset_card_eq_countP_add_countP"))
        except Exception:
            pass
    return results


def _r0341_countP_True(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.countP_True
    # countP (fun _ => True) s = card s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "countP", 2)
    if args is not None:
        try:
            rhs = OOp("len", (args[1],))
            results.append((rhs, "Mathlib: Multiset_countP_True"))
        except Exception:
            pass
    return results


def _r0342_countP_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.countP_eq_zero
    # countP p s = 0 ↔ ∀ a ∈ s, ¬p a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "countP", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (OLit(0), OOp("in", (OOp("forall", (OVar("a"),)), OOp("s", (OOp("not", (args[0],)), OVar("a"),))))))
            results.append((rhs, "Mathlib: Multiset_countP_eq_zero"))
        except Exception:
            pass
    return results


def _r0343_countP_eq_card(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.countP_eq_card
    # countP p s = card s ↔ ∀ a ∈ s, p a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "countP", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (OOp("len", (args[1],)), OOp("in", (OOp("forall", (OVar("a"),)), OOp("s", (args[0], OVar("a"),))))))
            results.append((rhs, "Mathlib: Multiset_countP_eq_card"))
        except Exception:
            pass
    return results


def _r0344_countP_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.countP_congr
    # s.countP p = s'.countP p'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_countP", 1)
    if args is not None:
        try:
            rhs = OOp("s_prime_countP", (OVar("p_prime"),))
            results.append((rhs, "Mathlib: Multiset_countP_congr"))
        except Exception:
            pass
    return results


def _r0345_coe_dedup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.coe_dedup
    # @dedup α _ l = l.dedup
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_dedup", 3)
    if args is not None:
        try:
            rhs = OVar("l_dedup")
            results.append((rhs, "Mathlib: Multiset_coe_dedup"))
        except Exception:
            pass
    return results


def _r0346_count_dedup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.count_dedup
    # m.dedup.count a = if a ∈ m then 1 else 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m_dedup_count", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("if", (args[0],)), OOp("m", (OVar("then"), OLit(1), OVar("else"), OLit(0),))))
            results.append((rhs, "Mathlib: Multiset_count_dedup"))
        except Exception:
            pass
    return results


def _r0347_dedup_idem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.dedup_idem
    # m.dedup.dedup = m.dedup
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_dedup_dedup")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("m_dedup")
            results.append((rhs, "Mathlib: Multiset_dedup_idem"))
    except Exception:
        pass
    return results


def _r0348_dedup_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.dedup_singleton
    # dedup ({a} : Multiset α) = {a}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Multiset_dedup_singleton"))
        except Exception:
            pass
    return results


def _r0349_dedup_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.dedup_ext
    # dedup s = dedup t ↔ ∀ a, a ∈ s ↔ a ∈ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OOp("dedup", (OVar("t"),)), OOp("iff", (OOp("in", (OOp("forall", (OVar("a"), OVar("a"),)), args[0])), OOp("in", (OVar("a"), OVar("t")))))))
            results.append((rhs, "Mathlib: Multiset_dedup_ext"))
        except Exception:
            pass
    return results


def _r0350_dedup_map_of_injective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.dedup_map_of_injective
    # (s.map f).dedup = s.dedup.map f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_map_f_dedup")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("s_dedup_map", (OVar("f"),))
            results.append((rhs, "Mathlib: Multiset_dedup_map_of_injective"))
    except Exception:
        pass
    return results


def _r0351_dedup_map_dedup_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.dedup_map_dedup_eq
    # dedup (map f (dedup s)) = dedup (map f s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OOp("dedup", (OOp("map", (OVar("f"), OVar("s"),)),))
            results.append((rhs, "Mathlib: Multiset_dedup_map_dedup_eq"))
        except Exception:
            pass
    return results


def _r0352_dedup_add_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.Subset.dedup_add_right
    # dedup (s + t) = dedup t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OOp("dedup", (OVar("t"),))
            results.append((rhs, "Mathlib: Multiset_Subset_dedup_add_right"))
        except Exception:
            pass
    return results


def _r0353_dedup_add_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.Subset.dedup_add_left
    # dedup (s + t) = dedup s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OOp("dedup", (OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_Subset_dedup_add_left"))
        except Exception:
            pass
    return results


def _r0354_dedup_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.Disjoint.dedup_add
    # dedup (s + t) = dedup s + dedup t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("dedup", (OVar("s"),)), OOp("dedup", (OVar("t"),))))
            results.append((rhs, "Mathlib: Multiset_Disjoint_dedup_add"))
        except Exception:
            pass
    return results


def _r0355_coe_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.coe_eq_coe
    # (l₁ : Multiset α) = l₂ ↔ l₁ ~ l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_1", 3)
    if args is not None:
        try:
            rhs = OOp("iff", (OVar("l_2"), OOp("l_1", (OVar("tilde"), OVar("l_2"),))))
            results.append((rhs, "Mathlib: Multiset_coe_eq_coe"))
        except Exception:
            pass
    return results


def _r0356_isDershowitzMannaLT_singleton_insert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.isDershowitzMannaLT_singleton_insert
    # ∃ M', N = a ::ₘ M' ∧ OneStep M' M ∨ N = M + M' ∧ ∀ x ∈ M', x < a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("and", (OOp("a", (OVar("colon_colon"), args[0],)), OOp("or", (OOp("OneStep", (args[0], OVar("M"),)), args[1])))), OOp("<", (OOp("and", (OOp("+", (OVar("M"), args[0])), OOp("in", (OOp("forall", (OVar("x"),)), OOp("M_prime", (OVar("x"),)))))), OVar("a")))))
            results.append((rhs, "Mathlib: Multiset_isDershowitzMannaLT_singleton_insert"))
        except Exception:
            pass
    return results


def _r0357_filter_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_coe
    # filter p l = l.filter p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter", 2)
    if args is not None:
        try:
            rhs = OOp("l_filter", (args[0],))
            results.append((rhs, "Mathlib: Multiset_filter_coe"))
        except Exception:
            pass
    return results


def _r0358_filter_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_add
    # filter p (s + t) = filter p s + filter p t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("filter", (args[0], OVar("s"),)), OOp("filter", (args[0], OVar("t"),))))
            results.append((rhs, "Mathlib: Multiset_filter_add"))
        except Exception:
            pass
    return results


def _r0359_filter_cons_of_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_cons_of_pos
    # p a → filter p (a ::ₘ s) = a ::ₘ filter p s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("colon_colon"), OVar("filter"), args[0], OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_filter_cons_of_pos"))
        except Exception:
            pass
    return results


def _r0360_filter_eq_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_eq_self
    # filter p s = s ↔ ∀ a ∈ s, p a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (args[1], OOp("in", (OOp("forall", (OVar("a"),)), OOp("s", (args[0], OVar("a"),))))))
            results.append((rhs, "Mathlib: Multiset_filter_eq_self"))
        except Exception:
            pass
    return results


def _r0361_filter_eq_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_eq_nil
    # filter p s = 0 ↔ ∀ a ∈ s, ¬p a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (OLit(0), OOp("in", (OOp("forall", (OVar("a"),)), OOp("s", (OOp("not", (args[0],)), OVar("a"),))))))
            results.append((rhs, "Mathlib: Multiset_filter_eq_nil"))
        except Exception:
            pass
    return results


def _r0362_filter_true(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_true
    # s.filter (fun _ ↦ True) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_filter", 1)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Multiset_filter_true"))
        except Exception:
            pass
    return results


def _r0363_filter_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_cons
    # filter p (a ::ₘ s) = (if p a then {a} else 0) + filter p s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("if", (args[0], OVar("a"), OVar("then"), OVar("a"), OVar("else"), OLit(0),)), OOp("filter", (args[0], OVar("s"),))))
            results.append((rhs, "Mathlib: Multiset_filter_cons"))
        except Exception:
            pass
    return results


def _r0364_filter_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_singleton
    # filter p {a} = if p a then {a} else ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter", 2)
    if args is not None:
        try:
            rhs = OOp("if", (args[0], args[1], OVar("then"), args[1], OVar("else"), OVar("empty"),))
            results.append((rhs, "Mathlib: Multiset_filter_singleton"))
        except Exception:
            pass
    return results


def _r0365_filter_filter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_filter
    # filter p (filter q s) = filter (fun a => p a ∧ q a) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter", 2)
    if args is not None:
        try:
            rhs = OOp("filter", (OOp("and", (OOp("fun", (OVar("a"), OVar("eq_gt"), args[0], OVar("a"),)), OOp("q", (OVar("a"),)))), OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_filter_filter"))
        except Exception:
            pass
    return results


def _r0366_filter_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_comm
    # filter p (filter q s) = filter q (filter p s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter", 2)
    if args is not None:
        try:
            rhs = OOp("filter", (OVar("q"), OOp("filter", (args[0], OVar("s"),)),))
            results.append((rhs, "Mathlib: Multiset_filter_comm"))
        except Exception:
            pass
    return results


def _r0367_filter_add_filter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_add_filter
    # filter p s + filter q s = filter (fun a => p a ∨ q a) s + filter (fun a => p a ∧ q a) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("filter", (OOp("or", (OOp("fun", (OVar("a"), OVar("eq_gt"), OVar("p"), OVar("a"),)), OOp("q", (OVar("a"),)))), OVar("s"),)), OOp("filter", (OOp("and", (OOp("fun", (OVar("a"), OVar("eq_gt"), OVar("p"), OVar("a"),)), OOp("q", (OVar("a"),)))), OVar("s"),))))
            results.append((rhs, "Mathlib: Multiset_filter_add_filter"))
        except Exception:
            pass
    return results


def _r0368_filter_add_not(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_add_not
    # filter p s + filter (fun a => ¬p a) s = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Multiset_filter_add_not"))
        except Exception:
            pass
    return results


def _r0369_filter_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_map
    # filter p (map f s) = map f (filter (p ∘ f) s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter", 2)
    if args is not None:
        try:
            rhs = OOp("map", (OVar("f"), OOp("filter", (OOp("comp", (args[0], OVar("f"))), OVar("s"),)),))
            results.append((rhs, "Mathlib: Multiset_filter_map"))
        except Exception:
            pass
    return results


def _r0370_filterMap_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filterMap_coe
    # filterMap f l = l.filterMap f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter_map", 2)
    if args is not None:
        try:
            rhs = OOp("l_filterMap", (args[0],))
            results.append((rhs, "Mathlib: Multiset_filterMap_coe"))
        except Exception:
            pass
    return results


def _r0371_filterMap_cons_some(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filterMap_cons_some
    # filterMap f (a ::ₘ s) = b ::ₘ filterMap f s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter_map", 2)
    if args is not None:
        try:
            rhs = OOp("b", (OVar("colon_colon"), OVar("filterMap"), args[0], OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_filterMap_cons_some"))
        except Exception:
            pass
    return results


def _r0372_filterMap_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filterMap_cons
    # filterMap f (a ::ₘ s) = ((f a).map singleton).getD 0 + filterMap f s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter_map", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("f_a_map_singleton_getD", (OLit(0),)), OOp("filter_map", (args[0], OVar("s"),))))
            results.append((rhs, "Mathlib: Multiset_filterMap_cons"))
        except Exception:
            pass
    return results


def _r0373_filterMap_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filterMap_add
    # filterMap f (s + t) = filterMap f s + filterMap f t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter_map", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("filter_map", (args[0], OVar("s"),)), OOp("filter_map", (args[0], OVar("t"),))))
            results.append((rhs, "Mathlib: Multiset_filterMap_add"))
        except Exception:
            pass
    return results


def _r0374_filterMap_eq_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filterMap_eq_map
    # filterMap (some ∘ f) = map f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter_map", 1)
    if args is not None:
        try:
            rhs = OOp("map", (OVar("f"),))
            results.append((rhs, "Mathlib: Multiset_filterMap_eq_map"))
        except Exception:
            pass
    return results


def _r0375_filterMap_eq_filter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filterMap_eq_filter
    # filterMap (Option.guard p) = filter p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter_map", 1)
    if args is not None:
        try:
            rhs = OOp("filter", (OVar("p"),))
            results.append((rhs, "Mathlib: Multiset_filterMap_eq_filter"))
        except Exception:
            pass
    return results


def _r0376_filterMap_filterMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filterMap_filterMap
    # filterMap g (filterMap f s) = filterMap (fun x => (f x).bind g) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter_map", 2)
    if args is not None:
        try:
            rhs = OOp("filter_map", (OOp("fun", (OVar("x"), OVar("eq_gt"), OVar("f_x_bind"), args[0],)), OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_filterMap_filterMap"))
        except Exception:
            pass
    return results


def _r0377_map_filterMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_filterMap
    # map g (filterMap f s) = filterMap (fun x => (f x).map g) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("filter_map", (OOp("fun", (OVar("x"), OVar("eq_gt"), OVar("f_x_map"), args[0],)), OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_map_filterMap"))
        except Exception:
            pass
    return results


def _r0378_filterMap_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filterMap_map
    # filterMap g (map f s) = filterMap (g ∘ f) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter_map", 2)
    if args is not None:
        try:
            rhs = OOp("filter_map", (OOp("comp", (args[0], OVar("f"))), OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_filterMap_map"))
        except Exception:
            pass
    return results


def _r0379_filter_filterMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_filterMap
    # filter p (filterMap f s) = filterMap (fun x => (f x).filter p) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter", 2)
    if args is not None:
        try:
            rhs = OOp("filter_map", (OOp("fun", (OVar("x"), OVar("eq_gt"), OVar("f_x_filter"), args[0],)), OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_filter_filterMap"))
        except Exception:
            pass
    return results


def _r0380_filterMap_filter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filterMap_filter
    # filterMap f (filter p s) = filterMap (fun x => if p x then f x else none) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter_map", 2)
    if args is not None:
        try:
            rhs = OOp("filter_map", (OOp("fun", (OVar("x"), OVar("eq_gt"), OVar("if"), OVar("p"), OVar("x"), OVar("then"), args[0], OVar("x"), OVar("else"), OVar("none"),)), OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_filterMap_filter"))
        except Exception:
            pass
    return results


def _r0381_filterMap_some(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filterMap_some
    # filterMap some s = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "filter_map", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Multiset_filterMap_some"))
        except Exception:
            pass
    return results


def _r0382_map_filterMap_of_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_filterMap_of_inv
    # map g (filterMap f s) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Multiset_map_filterMap_of_inv"))
        except Exception:
            pass
    return results


def _r0383_map_filter_eq_filterMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.map_filter_eq_filterMap
    # map f (filter p s) = filterMap (fun a => if p a then .some (f a) else .none) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("filter_map", (OOp("fun", (OVar("a"), OVar("eq_gt"), OVar("if"), OVar("p"), OVar("a"), OVar("then"), OVar("some"), OOp("f", (OVar("a"),)), OVar("else"), OVar("none"),)), OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_map_filter_eq_filterMap"))
        except Exception:
            pass
    return results


def _r0384_countP_eq_card_filter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.countP_eq_card_filter
    # countP p s = card (filter p s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "countP", 2)
    if args is not None:
        try:
            rhs = OOp("len", (OOp("filter", (args[0], args[1],)),))
            results.append((rhs, "Mathlib: Multiset_countP_eq_card_filter"))
        except Exception:
            pass
    return results


def _r0385_countP_filter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.countP_filter
    # countP p (filter q s) = countP (fun a => p a ∧ q a) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "countP", 2)
    if args is not None:
        try:
            rhs = OOp("countP", (OOp("and", (OOp("fun", (OVar("a"), OVar("eq_gt"), args[0], OVar("a"),)), OOp("q", (OVar("a"),)))), OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_countP_filter"))
        except Exception:
            pass
    return results


def _r0386_countP_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.countP_map
    # countP p (map f s) = card (s.filter fun a => p (f a))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "countP", 2)
    if args is not None:
        try:
            rhs = OOp("len", (OOp("s_filter", (OVar("fun"), OVar("a"), OVar("eq_gt"), args[0], OOp("f", (OVar("a"),)),)),))
            results.append((rhs, "Mathlib: Multiset_countP_map"))
        except Exception:
            pass
    return results


def _r0387_filter_attach(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.filter_attach
    # (s.attach.filter fun a : {a // a ∈ s} ↦ p ↑a) =       (s.filter p).attach.map (Subtype.map id fun _ ↦ Multiset.mem_of_me
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_attach_filter", 7)
    if args is not None:
        try:
            rhs = OOp("s_filter_p_attach_map", (OOp("Subtype_map", (OVar("id"), args[0], args[4], args[4], OVar("Multiset_mem_of_mem_filter"),)),))
            results.append((rhs, "Mathlib: Multiset_filter_attach"))
        except Exception:
            pass
    return results


def _r0388_coe_ndinsert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.coe_ndinsert
    # ndinsert a l = (insert a l : List α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ndinsert", 2)
    if args is not None:
        try:
            rhs = OOp("insert", (args[0], args[1], OVar("colon"), OVar("List"), args[0],))
            results.append((rhs, "Mathlib: Multiset_coe_ndinsert"))
        except Exception:
            pass
    return results


def _r0389_length_ndinsert_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.length_ndinsert_of_mem
    # card (ndinsert a s) = card s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("len", (OVar("s"),))
            results.append((rhs, "Mathlib: Multiset_length_ndinsert_of_mem"))
        except Exception:
            pass
    return results


def _r0390_length_ndinsert_of_notMem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.length_ndinsert_of_notMem
    # card (ndinsert a s) = card s + 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("len", (OVar("s"),)), OLit(1)))
            results.append((rhs, "Mathlib: Multiset_length_ndinsert_of_notMem"))
        except Exception:
            pass
    return results


def _r0391_dedup_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.dedup_cons
    # dedup (a ::ₘ s) = ndinsert a (dedup s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OOp("ndinsert", (OVar("a"), OOp("dedup", (OVar("s"),)),))
            results.append((rhs, "Mathlib: Multiset_dedup_cons"))
        except Exception:
            pass
    return results


def _r0392_attach_ndinsert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.attach_ndinsert
    # (s.ndinsert a).attach =       ndinsert ⟨a, mem_ndinsert_self a s⟩ (s.attach.map fun p => ⟨p.1, mem_ndinsert_of_mem p.2⟩)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_ndinsert_a_attach")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("ndinsert", (OVar("a_mem_ndinsert_self_a_s"), OOp("s_attach_map", (OVar("fun"), OVar("p"), OVar("eq_gt"), OVar("p_1_mem_ndinsert_of_mem_p_2"),)),))
            results.append((rhs, "Mathlib: Multiset_attach_ndinsert"))
    except Exception:
        pass
    return results


def _r0393_coe_ndunion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.coe_ndunion
    # @ndunion α _ l₁ l₂ = (l₁ ∪ l₂ : List α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_ndunion", 4)
    if args is not None:
        try:
            rhs = OOp("union", (args[2], OOp("l_2", (OVar("colon"), OVar("List"), args[0],))))
            results.append((rhs, "Mathlib: Multiset_coe_ndunion"))
        except Exception:
            pass
    return results


def _r0394_zero_ndunion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.zero_ndunion
    # ndunion 0 s = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ndunion", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Multiset_zero_ndunion"))
        except Exception:
            pass
    return results


def _r0395_cons_ndunion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.cons_ndunion
    # ndunion (a ::ₘ s) t = ndinsert a (ndunion s t)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ndunion", 2)
    if args is not None:
        try:
            rhs = OOp("ndinsert", (OVar("a"), OOp("ndunion", (OVar("s"), args[1],)),))
            results.append((rhs, "Mathlib: Multiset_cons_ndunion"))
        except Exception:
            pass
    return results


def _r0396_ndunion_eq_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.ndunion_eq_union
    # ndunion s t = s ∪ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ndunion", 2)
    if args is not None:
        try:
            rhs = OOp("union", (args[0], args[1]))
            results.append((rhs, "Mathlib: Multiset_ndunion_eq_union"))
        except Exception:
            pass
    return results


def _r0397_ndunion_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.Disjoint.ndunion_eq
    # s.ndunion t = s.dedup + t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_ndunion", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("s_dedup"), args[0]))
            results.append((rhs, "Mathlib: Multiset_Disjoint_ndunion_eq"))
        except Exception:
            pass
    return results


def _r0398_ndunion_eq_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.Subset.ndunion_eq_right
    # s.ndunion t = t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_ndunion", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Multiset_Subset_ndunion_eq_right"))
        except Exception:
            pass
    return results


def _r0399_coe_ndinter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.coe_ndinter
    # @ndinter α _ l₁ l₂ = (l₁ ∩ l₂ : List α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_ndinter", 4)
    if args is not None:
        try:
            rhs = OOp("inter", (args[2], OOp("l_2", (OVar("colon"), OVar("List"), args[0],))))
            results.append((rhs, "Mathlib: Multiset_coe_ndinter"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_multiset rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("!=", "*", "**", "+", "-", "<", "<=", "DFinsupp_toMultiset", "Disjoint", "Finset_mk", "Finset_sup", "Finsupp_toMultiset", "Icc_a_b_map", "Ico", "Ico_a_b_map", "Ioc", "Ioc_a_b_map", "Ioo", "Ioo_a_b_map", "IsAtom", "Multiset", "Multiset_multinomial", "Multiset_replicate", "Multiset_toDFinsupp", "Multiset_toList", "Option_guard", "Quotient_lift", "Sections", "Sigma", "_0", "_1", "_unknown", "a", "a_b", "a_colon_colon_m_recOn", "a_colon_colon_s_bind", "a_colon_colon_s_fold", "and", "antidiagonal", "antidiagonalTuple", "antidiagonal_s_map", "at_antidiagonal", "at_bind", "at_dedup", "at_join", "at_ndinter", "at_ndunion", "at_nil", "at_powerset", "at_powersetCard",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_multiset axioms."""
    if recognizes(term):
        return 0.6
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_multiset rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_prod_nsmul(term, ctx))
    results.extend(_r0001_prod_map_pow(term, ctx))
    results.extend(_r0002_prod_toList(term, ctx))
    results.extend(_r0003_prod_zero(term, ctx))
    results.extend(_r0004_prod_cons(term, ctx))
    results.extend(_r0005_prod_singleton(term, ctx))
    results.extend(_r0006_prod_pair(term, ctx))
    results.extend(_r0007_pow_count(term, ctx))
    results.extend(_r0008_lcm_cons(term, ctx))
    results.extend(_r0009_lcm_singleton(term, ctx))
    results.extend(_r0010_lcm_add(term, ctx))
    results.extend(_r0011_map_nsmul(term, ctx))
    results.extend(_r0012_bell_mul_eq_lemma(term, ctx))
    results.extend(_r0013_toDFinsupp_support(term, ctx))
    results.extend(_r0014_toDFinsupp_replicate(term, ctx))
    results.extend(_r0015_toDFinsupp_toMultiset(term, ctx))
    results.extend(_r0016_toDFinsupp_inter(term, ctx))
    results.extend(_r0017_toDFinsupp_union(term, ctx))
    results.extend(_r0018_antidiagonalTuple_zero_succ(term, ctx))
    results.extend(_r0019_mem_antidiagonalTuple(term, ctx))
    results.extend(_r0020_antidiagonalTuple_two(term, ctx))
    results.extend(_r0021_keys_zero(term, ctx))
    results.extend(_r0022_keys_cons(term, ctx))
    results.extend(_r0023_toFinset_inter(term, ctx))
    results.extend(_r0024_toFinset_union(term, ctx))
    results.extend(_r0025_toFinset_eq_empty(term, ctx))
    results.extend(_r0026_toFinset_eq(term, ctx))
    results.extend(_r0027_exists_multiset_cons(term, ctx))
    results.extend(_r0028_toFinset_cons(term, ctx))
    results.extend(_r0029_toFinset_singleton(term, ctx))
    results.extend(_r0030_noncommFoldr_cons(term, ctx))
    results.extend(_r0031_noncommFold_empty(term, ctx))
    results.extend(_r0032_noncommFold_cons(term, ctx))
    results.extend(_r0033_toFinsupp_apply(term, ctx))
    results.extend(_r0034_toFinsupp_zero(term, ctx))
    results.extend(_r0035_toFinsupp_toMultiset(term, ctx))
    results.extend(_r0036_toFinsupp_eq_iff(term, ctx))
    results.extend(_r0037_map_univ_val_equiv(term, ctx))
    results.extend(_r0038_singleton_add(term, ctx))
    results.extend(_r0039_add_zero(term, ctx))
    results.extend(_r0040_add_cons(term, ctx))
    results.extend(_r0041_add_left_inj(term, ctx))
    results.extend(_r0042_antidiagonal_map_snd(term, ctx))
    results.extend(_r0043_antidiagonal_zero(term, ctx))
    results.extend(_r0044_antidiagonal_cons(term, ctx))
    results.extend(_r0045_toList_eq_nil(term, ctx))
    results.extend(_r0046_empty_toList(term, ctx))
    results.extend(_r0047_toList_eq_singleton_iff(term, ctx))
    results.extend(_r0048_toList_singleton(term, ctx))
    results.extend(_r0049_length_toList(term, ctx))
    results.extend(_r0050_join_cons(term, ctx))
    results.extend(_r0051_join_add(term, ctx))
    results.extend(_r0052_singleton_join(term, ctx))
    results.extend(_r0053_map_join(term, ctx))
    results.extend(_r0054_cons_bind(term, ctx))
    results.extend(_r0055_singleton_bind(term, ctx))
    results.extend(_r0056_add_bind(term, ctx))
    results.extend(_r0057_bind_add(term, ctx))
    results.extend(_r0058_bind_cons(term, ctx))
    results.extend(_r0059_card_bind(term, ctx))
    results.extend(_r0060_bind_congr(term, ctx))
    results.extend(_r0061_countP_zero(term, ctx))
    results.extend(_r0062_countP_cons_of_neg(term, ctx))
    results.extend(_r0063_countP_False(term, ctx))
    results.extend(_r0064_countP_attach(term, ctx))
    results.extend(_r0065_dedup_zero(term, ctx))
    results.extend(_r0066_dedup_cons_of_mem(term, ctx))
    results.extend(_r0067_dedup_cons_of_notMem(term, ctx))
    results.extend(_r0068_dedup_eq_self(term, ctx))
    results.extend(_r0069_dedup_eq_zero(term, ctx))
    results.extend(_r0070_lift_coe(term, ctx))
    results.extend(_r0071_filter_zero(term, ctx))
    results.extend(_r0072_filter_congr(term, ctx))
    results.extend(_r0073_filter_cons_of_neg(term, ctx))
    results.extend(_r0074_filter_false(term, ctx))
    results.extend(_r0075_filterMap_zero(term, ctx))
    results.extend(_r0076_filterMap_cons_none(term, ctx))
    results.extend(_r0077_mem_filterMap(term, ctx))
    results.extend(_r0078_countP_eq_countP_filter_add(term, ctx))
    results.extend(_r0079_ndinsert_zero(term, ctx))
    results.extend(_r0080_ndinsert_of_mem(term, ctx))
    results.extend(_r0081_ndinsert_of_notMem(term, ctx))
    results.extend(_r0082_mem_ndinsert(term, ctx))
    results.extend(_r0083_dedup_add(term, ctx))
    results.extend(_r0084_cons_ndinter_of_mem(term, ctx))
    results.extend(_r0085_ndinter_cons_of_notMem(term, ctx))
    results.extend(_r0086_map_toEnumFinset_fst(term, ctx))
    results.extend(_r0087_image_toEnumFinset_fst(term, ctx))
    results.extend(_r0088_coe_fold_l(term, ctx))
    results.extend(_r0089_fold_cons_left(term, ctx))
    results.extend(_r0090_fold_cons_right(term, ctx))
    results.extend(_r0091_bind_def(term, ctx))
    results.extend(_r0092_sup_zero(term, ctx))
    results.extend(_r0093_sup_cons(term, ctx))
    results.extend(_r0094_sup_singleton(term, ctx))
    results.extend(_r0095_sup_add(term, ctx))
    results.extend(_r0096_sup_ndunion(term, ctx))
    results.extend(_r0097_sup_union(term, ctx))
    results.extend(_r0098_sup_ndinsert(term, ctx))
    results.extend(_r0099_map_zero(term, ctx))
    results.extend(_r0100_map_cons(term, ctx))
    results.extend(_r0101_map_comp_cons(term, ctx))
    results.extend(_r0102_map_replicate(term, ctx))
    results.extend(_r0103_map_add(term, ctx))
    results.extend(_r0104_card_map(term, ctx))
    results.extend(_r0105_map_eq_zero(term, ctx))
    results.extend(_r0106_zero_eq_map(term, ctx))
    results.extend(_r0107_map_id(term, ctx))
    results.extend(_r0108_eq_of_mem_map_const(term, ctx))
    results.extend(_r0109_foldl_cons(term, ctx))
    results.extend(_r0110_foldl_add(term, ctx))
    results.extend(_r0111_antidiagonal_succ(term, ctx))
    results.extend(_r0112_pi_cons(term, ctx))
    results.extend(_r0113_powerset_zero(term, ctx))
    results.extend(_r0114_powerset_cons(term, ctx))
    results.extend(_r0115_powerset_eq_singleton_zero_iff(term, ctx))
    results.extend(_r0116_powersetCardAux_nil(term, ctx))
    results.extend(_r0117_powersetCardAux_cons(term, ctx))
    results.extend(_r0118_powersetCard_zero_right(term, ctx))
    results.extend(_r0119_card_powersetCard(term, ctx))
    results.extend(_r0120_range_succ(term, ctx))
    results.extend(_r0121_card_range(term, ctx))
    results.extend(_r0122_replicate_succ(term, ctx))
    results.extend(_r0123_replicate_add(term, ctx))
    results.extend(_r0124_mem_replicate(term, ctx))
    results.extend(_r0125_sections_cons(term, ctx))
    results.extend(_r0126_sort_zero(term, ctx))
    results.extend(_r0127_sort_singleton(term, ctx))
    results.extend(_r0128_map_sort(term, ctx))
    results.extend(_r0129_disjSum_zero(term, ctx))
    results.extend(_r0130_card_disjSum(term, ctx))
    results.extend(_r0131_sym2_eq_zero_iff(term, ctx))
    results.extend(_r0132_sym2_zero(term, ctx))
    results.extend(_r0133_sym2_cons(term, ctx))
    results.extend(_r0134_union_zero(term, ctx))
    results.extend(_r0135_count_union(term, ctx))
    results.extend(_r0136_filter_union(term, ctx))
    results.extend(_r0137_zero_inter(term, ctx))
    results.extend(_r0138_cons_inter_of_pos(term, ctx))
    results.extend(_r0139_cons_inter_of_neg(term, ctx))
    results.extend(_r0140_inf_eq_inter(term, ctx))
    results.extend(_r0141_union_comm(term, ctx))
    results.extend(_r0142_inter_comm(term, ctx))
    results.extend(_r0143_empty_eq_zero(term, ctx))
    results.extend(_r0144_coe_eq_zero(term, ctx))
    results.extend(_r0145_coe_eq_zero_iff_isEmpty(term, ctx))
    results.extend(_r0146_cons_coe(term, ctx))
    results.extend(_r0147_cons_inj_left(term, ctx))
    results.extend(_r0148_recOn_cons(term, ctx))
    results.extend(_r0149_multinomial_singleton(term, ctx))
    results.extend(_r0150_finite_toSet_toFinset(term, ctx))
    results.extend(_r0151_esymm_pair_two(term, ctx))
    results.extend(_r0152_disjoint_list_sum_left(term, ctx))
    results.extend(_r0153_lcm_dvd(term, ctx))
    results.extend(_r0154_toDFinsupp_le_toDFinsupp(term, ctx))
    results.extend(_r0155_toDFinsupp_lt_toDFinsupp(term, ctx))
    results.extend(_r0156_nodup_keys(term, ctx))
    results.extend(_r0157_toFinset_nonempty(term, ctx))
    results.extend(_r0158_toFinset_subset(term, ctx))
    results.extend(_r0159_toFinset_ssubset(term, ctx))
    results.extend(_r0160_add_le_add_iff_left(term, ctx))
    results.extend(_r0161_mem_add(term, ctx))
    results.extend(_r0162_mem_toList(term, ctx))
    results.extend(_r0163_mem_join(term, ctx))
    results.extend(_r0164_mem_bind(term, ctx))
    results.extend(_r0165_mem_dedup(term, ctx))
    results.extend(_r0166_le_dedup(term, ctx))
    results.extend(_r0167_mem_filter(term, ctx))
    results.extend(_r0168_le_filter(term, ctx))
    results.extend(_r0169_mem_ndunion(term, ctx))
    results.extend(_r0170_mem_ndinter(term, ctx))
    results.extend(_r0171_forall_coe(term, ctx))
    results.extend(_r0172_sup_le(term, ctx))
    results.extend(_r0173_nodup_sup_iff(term, ctx))
    results.extend(_r0174_mem_powerset(term, ctx))
    results.extend(_r0175_range_subset(term, ctx))
    results.extend(_r0176_le_inter_iff(term, ctx))
    results.extend(_r0177_union_le_iff(term, ctx))
    results.extend(_r0178_mem_Ico(term, ctx))
    results.extend(_r0179_mem_Ioc(term, ctx))
    results.extend(_r0180_mem_Ioo(term, ctx))
    results.extend(_r0181_sum_map_div(term, ctx))
    results.extend(_r0182_prod_map_eq_finprod(term, ctx))
    results.extend(_r0183_card_finsuppSum(term, ctx))
    results.extend(_r0184_prod_map_prod(term, ctx))
    results.extend(_r0185_toFinset_sum_count_eq(term, ctx))
    results.extend(_r0186_sum_count_eq_card(term, ctx))
    results.extend(_r0187_toFinset_sum_count_nsmul_eq(term, ctx))
    results.extend(_r0188_exists_smul_of_dvd_count(term, ctx))
    results.extend(_r0189_prod_sum(term, ctx))
    results.extend(_r0190_card_sum(term, ctx))
    results.extend(_r0191_prod_erase(term, ctx))
    results.extend(_r0192_prod_map_erase(term, ctx))
    results.extend(_r0193_prod_add(term, ctx))
    results.extend(_r0194_prod_filter_mul_prod_filter_not(term, ctx))
    results.extend(_r0195_prod_map_eq_pow_single(term, ctx))
    results.extend(_r0196_prod_eq_pow_single(term, ctx))
    results.extend(_r0197_prod_eq_one(term, ctx))
    results.extend(_r0198_prod_hom_ne_zero(term, ctx))
    results.extend(_r0199_prod_hom(term, ctx))
    results.extend(_r0200_prod_hom_2_ne_zero(term, ctx))
    results.extend(_r0201_prod_hom_2(term, ctx))
    results.extend(_r0202_prod_map_mul(term, ctx))
    results.extend(_r0203_prod_map_prod_map(term, ctx))
    results.extend(_r0204_map_multiset_prod(term, ctx))
    results.extend(_r0205_map_multiset_ne_zero_prod(term, ctx))
    results.extend(_r0206_map_multiset_prod(term, ctx))
    results.extend(_r0207_map_multiset_ne_zero_prod(term, ctx))
    results.extend(_r0208_fst_prod(term, ctx))
    results.extend(_r0209_snd_prod(term, ctx))
    results.extend(_r0210_prod_eq_foldr(term, ctx))
    results.extend(_r0211_prod_eq_foldl(term, ctx))
    results.extend(_r0212_prod_coe(term, ctx))
    results.extend(_r0213_prod_map_toList(term, ctx))
    results.extend(_r0214_prod_replicate(term, ctx))
    results.extend(_r0215_prod_map_one(term, ctx))
    results.extend(_r0216_smul_sum(term, ctx))
    results.extend(_r0217_smul_prod(term, ctx))
    results.extend(_r0218_prod_map_neg(term, ctx))
    results.extend(_r0219_lcm_zero(term, ctx))
    results.extend(_r0220_normalize_lcm(term, ctx))
    results.extend(_r0221_lcm_dedup(term, ctx))
    results.extend(_r0222_lcm_ndunion(term, ctx))
    results.extend(_r0223_lcm_union(term, ctx))
    results.extend(_r0224_lcm_ndinsert(term, ctx))
    results.extend(_r0225_sum_smul(term, ctx))
    results.extend(_r0226_sum_smul_sum(term, ctx))
    results.extend(_r0227_finset_sum_eq_sup_iff_disjoint(term, ctx))
    results.extend(_r0228_sup_powerset_len(term, ctx))
    results.extend(_r0229_card_le_card_toFinset_add_one_iff(term, ctx))
    results.extend(_r0230_all_one_of_le_one_le_of_prod_eq_one(term, ctx))
    results.extend(_r0231_toFinset_nsmul(term, ctx))
    results.extend(_r0232_toFinset_eq_singleton_iff(term, ctx))
    results.extend(_r0233_toFinset_card_eq_one_iff(term, ctx))
    results.extend(_r0234_nsmul_cons(term, ctx))
    results.extend(_r0235_card_nsmul(term, ctx))
    results.extend(_r0236_nsmul_replicate(term, ctx))
    results.extend(_r0237_nsmul_singleton(term, ctx))
    results.extend(_r0238_map_add_left_Icc(term, ctx))
    results.extend(_r0239_map_add_left_Ico(term, ctx))
    results.extend(_r0240_map_add_left_Ioc(term, ctx))
    results.extend(_r0241_map_add_left_Ioo(term, ctx))
    results.extend(_r0242_map_add_right_Icc(term, ctx))
    results.extend(_r0243_map_add_right_Ico(term, ctx))
    results.extend(_r0244_map_add_right_Ioc(term, ctx))
    results.extend(_r0245_map_add_right_Ioo(term, ctx))
    results.extend(_r0246_trop_sum(term, ctx))
    results.extend(_r0247_untrop_prod(term, ctx))
    results.extend(_r0248_trop_inf(term, ctx))
    results.extend(_r0249_untrop_sum(term, ctx))
    results.extend(_r0250_bell_zero(term, ctx))
    results.extend(_r0251_bell_mul_eq(term, ctx))
    results.extend(_r0252_bell_eq(term, ctx))
    results.extend(_r0253_toDFinsupp_apply(term, ctx))
    results.extend(_r0254_toDFinsupp_singleton(term, ctx))
    results.extend(_r0255_toDFinsupp_inj(term, ctx))
    results.extend(_r0256_antidiagonalTuple_zero_zero(term, ctx))
    results.extend(_r0257_antidiagonalTuple_zero_right(term, ctx))
    results.extend(_r0258_antidiagonalTuple_one(term, ctx))
    results.extend(_r0259_coe_keys(term, ctx))
    results.extend(_r0260_keys_singleton(term, ctx))
    results.extend(_r0261_toFinset_add(term, ctx))
    results.extend(_r0262_toFinset_filter(term, ctx))
    results.extend(_r0263_toFinset_replicate(term, ctx))
    results.extend(_r0264_card_toFinset(term, ctx))
    results.extend(_r0265_toFinset_card_of_nodup(term, ctx))
    results.extend(_r0266_dedup_card_eq_card_iff_nodup(term, ctx))
    results.extend(_r0267_toFinset_card_eq_card_iff_nodup(term, ctx))
    results.extend(_r0268_toFinset_val(term, ctx))
    results.extend(_r0269_toFinset_inj(term, ctx))
    results.extend(_r0270_toFinset_dedup(term, ctx))
    results.extend(_r0271_covBy_iff(term, ctx))
    results.extend(_r0272_isAtom_iff(term, ctx))
    results.extend(_r0273_grade_eq(term, ctx))
    results.extend(_r0274_toFinset_map(term, ctx))
    results.extend(_r0275_toFinset_zero(term, ctx))
    results.extend(_r0276_map_finset_sup(term, ctx))
    results.extend(_r0277_count_finset_sup(term, ctx))
    results.extend(_r0278_nat_divisors_prod(term, ctx))
    results.extend(_r0279_noncommFoldr_coe(term, ctx))
    results.extend(_r0280_noncommFoldr_empty(term, ctx))
    results.extend(_r0281_noncommFoldr_eq_foldr(term, ctx))
    results.extend(_r0282_noncommFold_coe(term, ctx))
    results.extend(_r0283_noncommFold_eq_fold(term, ctx))
    results.extend(_r0284_support_sum_eq(term, ctx))
    results.extend(_r0285_toFinsupp_support(term, ctx))
    results.extend(_r0286_toFinsupp_add(term, ctx))
    results.extend(_r0287_toFinsupp_singleton(term, ctx))
    results.extend(_r0288_toFinsupp_union(term, ctx))
    results.extend(_r0289_toFinsupp_inter(term, ctx))
    results.extend(_r0290_toFinsupp_sum_eq(term, ctx))
    results.extend(_r0291_count_univ(term, ctx))
    results.extend(_r0292_bijective_iff_map_univ_eq_univ(term, ctx))
    results.extend(_r0293_lists_coe(term, ctx))
    results.extend(_r0294_mem_lists_iff(term, ctx))
    results.extend(_r0295_coe_add(term, ctx))
    results.extend(_r0296_add_comm(term, ctx))
    results.extend(_r0297_add_assoc(term, ctx))
    results.extend(_r0298_zero_add(term, ctx))
    results.extend(_r0299_le_iff_exists_add(term, ctx))
    results.extend(_r0300_cons_add(term, ctx))
    results.extend(_r0301_countP_add(term, ctx))
    results.extend(_r0302_count_add(term, ctx))
    results.extend(_r0303_add_right_inj(term, ctx))
    results.extend(_r0304_card_add(term, ctx))
    results.extend(_r0305_antidiagonal_coe(term, ctx))
    results.extend(_r0306_mem_antidiagonal(term, ctx))
    results.extend(_r0307_antidiagonal_map_fst(term, ctx))
    results.extend(_r0308_antidiagonal_eq_map_powerset(term, ctx))
    results.extend(_r0309_card_antidiagonal(term, ctx))
    results.extend(_r0310_coe_toList(term, ctx))
    results.extend(_r0311_toList_zero(term, ctx))
    results.extend(_r0312_join_zero(term, ctx))
    results.extend(_r0313_card_join(term, ctx))
    results.extend(_r0314_prod_join(term, ctx))
    results.extend(_r0315_filter_join(term, ctx))
    results.extend(_r0316_filterMap_join(term, ctx))
    results.extend(_r0317_coe_bind(term, ctx))
    results.extend(_r0318_zero_bind(term, ctx))
    results.extend(_r0319_bind_singleton(term, ctx))
    results.extend(_r0320_map_bind(term, ctx))
    results.extend(_r0321_bind_map(term, ctx))
    results.extend(_r0322_bind_assoc(term, ctx))
    results.extend(_r0323_bind_bind(term, ctx))
    results.extend(_r0324_bind_map_comm(term, ctx))
    results.extend(_r0325_filter_eq_bind(term, ctx))
    results.extend(_r0326_bind_filter(term, ctx))
    results.extend(_r0327_filter_bind(term, ctx))
    results.extend(_r0328_filterMap_eq_bind(term, ctx))
    results.extend(_r0329_bind_filterMap(term, ctx))
    results.extend(_r0330_filterMap_bind(term, ctx))
    results.extend(_r0331_prod_bind(term, ctx))
    results.extend(_r0332_count_sum(term, ctx))
    results.extend(_r0333_count_bind(term, ctx))
    results.extend(_r0334_attach_bind_coe(term, ctx))
    results.extend(_r0335_dedup_bind_dedup(term, ctx))
    results.extend(_r0336_fold_bind(term, ctx))
    results.extend(_r0337_coe_countP(term, ctx))
    results.extend(_r0338_countP_cons_of_pos(term, ctx))
    results.extend(_r0339_countP_cons(term, ctx))
    results.extend(_r0340_card_eq_countP_add_countP(term, ctx))
    results.extend(_r0341_countP_True(term, ctx))
    results.extend(_r0342_countP_eq_zero(term, ctx))
    results.extend(_r0343_countP_eq_card(term, ctx))
    results.extend(_r0344_countP_congr(term, ctx))
    results.extend(_r0345_coe_dedup(term, ctx))
    results.extend(_r0346_count_dedup(term, ctx))
    results.extend(_r0347_dedup_idem(term, ctx))
    results.extend(_r0348_dedup_singleton(term, ctx))
    results.extend(_r0349_dedup_ext(term, ctx))
    results.extend(_r0350_dedup_map_of_injective(term, ctx))
    results.extend(_r0351_dedup_map_dedup_eq(term, ctx))
    results.extend(_r0352_dedup_add_right(term, ctx))
    results.extend(_r0353_dedup_add_left(term, ctx))
    results.extend(_r0354_dedup_add(term, ctx))
    results.extend(_r0355_coe_eq_coe(term, ctx))
    results.extend(_r0356_isDershowitzMannaLT_singleton_insert(term, ctx))
    results.extend(_r0357_filter_coe(term, ctx))
    results.extend(_r0358_filter_add(term, ctx))
    results.extend(_r0359_filter_cons_of_pos(term, ctx))
    results.extend(_r0360_filter_eq_self(term, ctx))
    results.extend(_r0361_filter_eq_nil(term, ctx))
    results.extend(_r0362_filter_true(term, ctx))
    results.extend(_r0363_filter_cons(term, ctx))
    results.extend(_r0364_filter_singleton(term, ctx))
    results.extend(_r0365_filter_filter(term, ctx))
    results.extend(_r0366_filter_comm(term, ctx))
    results.extend(_r0367_filter_add_filter(term, ctx))
    results.extend(_r0368_filter_add_not(term, ctx))
    results.extend(_r0369_filter_map(term, ctx))
    results.extend(_r0370_filterMap_coe(term, ctx))
    results.extend(_r0371_filterMap_cons_some(term, ctx))
    results.extend(_r0372_filterMap_cons(term, ctx))
    results.extend(_r0373_filterMap_add(term, ctx))
    results.extend(_r0374_filterMap_eq_map(term, ctx))
    results.extend(_r0375_filterMap_eq_filter(term, ctx))
    results.extend(_r0376_filterMap_filterMap(term, ctx))
    results.extend(_r0377_map_filterMap(term, ctx))
    results.extend(_r0378_filterMap_map(term, ctx))
    results.extend(_r0379_filter_filterMap(term, ctx))
    results.extend(_r0380_filterMap_filter(term, ctx))
    results.extend(_r0381_filterMap_some(term, ctx))
    results.extend(_r0382_map_filterMap_of_inv(term, ctx))
    results.extend(_r0383_map_filter_eq_filterMap(term, ctx))
    results.extend(_r0384_countP_eq_card_filter(term, ctx))
    results.extend(_r0385_countP_filter(term, ctx))
    results.extend(_r0386_countP_map(term, ctx))
    results.extend(_r0387_filter_attach(term, ctx))
    results.extend(_r0388_coe_ndinsert(term, ctx))
    results.extend(_r0389_length_ndinsert_of_mem(term, ctx))
    results.extend(_r0390_length_ndinsert_of_notMem(term, ctx))
    results.extend(_r0391_dedup_cons(term, ctx))
    results.extend(_r0392_attach_ndinsert(term, ctx))
    results.extend(_r0393_coe_ndunion(term, ctx))
    results.extend(_r0394_zero_ndunion(term, ctx))
    results.extend(_r0395_cons_ndunion(term, ctx))
    results.extend(_r0396_ndunion_eq_union(term, ctx))
    results.extend(_r0397_ndunion_eq(term, ctx))
    results.extend(_r0398_ndunion_eq_right(term, ctx))
    results.extend(_r0399_coe_ndinter(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_multiset rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("Multiset_prod_primes_dvd", "s_prod_n", "Not an equality or iff proposition"),
    ("Multiset_prod_ne_zero_of_prime", "s_prod_ne_0", "Not an equality or iff proposition"),
    ("Multiset_mulSupport_fun_pow_count_subset", "fun_a_f_a_pow_count_a_s_mulSupport_sub_s_toFinset", "Not an equality or iff proposition"),
    ("Multiset_hasFiniteMulSupport_fun_pow_count", "fun_a_f_a_pow_s_count_a_HasFiniteMulSupport", "Not an equality or iff proposition"),
    ("Multiset_count_sum", "_unknown", "Empty proposition"),
    ("Multiset_toFinset_prod_dvd_prod", "S_toFinset_prod_id_S_prod", "Not an equality or iff proposition"),
    ("Multiset_prod_hom", "_unknown", "Empty proposition"),
    ("Multiset_prod_dvd_prod_of_le", "s_prod_t_prod", "Not an equality or iff proposition"),
    ("Multiset_dvd_prod", "a_in_s_to_a_s_prod", "Not an equality or iff proposition"),
    ("Multiset_prod_hom_rel", "r_s_map_f_prod_s_map_g_prod", "Not an equality or iff proposition"),
    ("Multiset_prod_induction", "p_s_prod", "Not an equality or iff proposition"),
    ("Multiset_prod_induction_nonempty", "p_s_prod", "Not an equality or iff proposition"),
    ("Multiset_smul_prod", "_unknown", "Empty proposition"),
    ("Multiset_dvd_lcm", "a_s_lcm", "Not an equality or iff proposition"),
    ("Multiset_lcm_mono", "s_1_lcm_s_2_lcm", "Not an equality or iff proposition"),
    ("Multiset_one_le_prod_of_one_le", "forall_x_in_s_1_colon_a_le_x_to_1_le_s_prod", "Not an equality or iff proposition"),
    ("Multiset_single_le_prod", "forall_x_in_s_1_colon_a_le_x_to_forall_x_in_s_x_le_s_prod", "Not an equality or iff proposition"),
    ("Multiset_prod_le_pow_card", "s_prod_le_n_pow_card_s", "Not an equality or iff proposition"),
    ("Multiset_prod_le_prod_of_rel_le", "s_prod_le_t_prod", "Not an equality or iff proposition"),
    ("Multiset_prod_map_le_prod_map", "s_map_f_prod_le_s_map_g_prod", "Not an equality or iff proposition"),
    ("Multiset_prod_map_le_prod", "s_map_f_prod_le_s_prod", "Not an equality or iff proposition"),
    ("Multiset_prod_le_prod_map", "s_prod_le_s_map_f_prod", "Not an equality or iff proposition"),
    ("Multiset_pow_card_le_prod", "a_pow_card_s_le_s_prod", "Not an equality or iff proposition"),
    ("Multiset_prod_nonneg", "_0_le_s_prod", "Not an equality or iff proposition"),
    ("Multiset_one_le_prod", "_1_le_s_prod", "Not an equality or iff proposition"),
    ("Multiset_prod_map_le_prod_map_0", "map_f_s_prod_le_map_g_s_prod", "Not an equality or iff proposition"),
    ("Multiset_prod_map_le_pow_card", "map_f_t_prod_le_r_pow_card_t", "Not an equality or iff proposition"),
    ("Multiset_prod_map_nonneg", "_0_le_s_map_f_prod", "Not an equality or iff proposition"),
    ("Multiset_one_le_prod_map", "_1_le_s_map_f_prod", "Not an equality or iff proposition"),
    ("Multiset_prod_pos", "_0_lt_s_prod", "Not an equality or iff proposition"),
    ("Multiset_prod_map_lt_prod_map", "map_f_s_prod_lt_map_g_s_prod", "Not an equality or iff proposition"),
    ("Multiset_le_prod_of_submultiplicative_on_pred_of_nonneg", "f_s_prod_le_s_map_f_prod", "Not an equality or iff proposition"),
    ("Multiset_le_prod_of_submultiplicative_of_nonneg", "f_s_prod_le_s_map_f_prod", "Not an equality or iff proposition"),
    ("Multiset_mem_le_prod_of_one_le", "f_a_le_s_map_f_prod", "Not an equality or iff proposition"),
    ("Multiset_mem_of_mem_nsmul", "a_in_s", "Not an equality or iff proposition"),
    ("Multiset_coe_mapAddMonoidHom", "mapAddMonoidHom_f_colon_Multiset_a_to_Multiset_b_eq_map_f", "Not an equality or iff proposition"),
    ("Multiset_toDFinsupp_injective", "Injective_toDFinsupp_colon_Multiset_a_to_Pi_0_a", "Not an equality or iff proposition"),
    ("Multiset_Nat_nodup_antidiagonalTuple", "antidiagonalTuple_k_n_Nodup", "Not an equality or iff proposition"),
    ("Multiset_NodupKeys_nodup", "m_Nodup", "Not an equality or iff proposition"),
    ("Multiset_toFinset_card_le", "hash_m_toFinset_le_Multiset_card_m", "Not an equality or iff proposition"),
    ("Multiset_covBy_cons", "s_a_colon_colon_s", "Not an equality or iff proposition"),
    ("CovBy_card_multiset", "card_s_card_t", "Not an equality or iff proposition"),
    ("Multiset_isAtom_singleton", "IsAtom_a_colon_Multiset_a", "Not an equality or iff proposition"),
    ("Multiset_exists_max_image", "exists_y_in_s_forall_z_in_s_f_z_le_f_y", "Not an equality or iff proposition"),
    ("Multiset_exists_min_image", "exists_y_in_s_forall_z_in_s_f_y_le_f_z", "Not an equality or iff proposition"),
    ("Multiset_support_sum_subset", "s_sum_support_sub_s_map_Finsupp_support_sup", "Not an equality or iff proposition"),
    ("Multiset_toFinsupp_strictMono", "StrictMono_at_Multiset_toFinsupp_i", "Not an equality or iff proposition"),
    ("Multiset_lists_nodup_finset", "lists_l_val_Nodup", "Not an equality or iff proposition"),
    ("Multiset_le_add_right", "s_le_s_plus_t", "Not an equality or iff proposition"),
    ("Multiset_le_add_left", "s_le_t_plus_s", "Not an equality or iff proposition"),
    ("Multiset_subset_add_left", "s_sub_s_plus_t", "Not an equality or iff proposition"),
    ("Multiset_subset_add_right", "s_sub_t_plus_s", "Not an equality or iff proposition"),
    ("Multiset_antidiagonal_coe", "_unknown", "Empty proposition"),
    ("Multiset_coe_join", "forall_L_colon_List_List_a_join_L_map_colon_List_a_to_Multiset_a_colon_Multiset_Mul", "Not an equality or iff proposition"),
    ("Multiset_rel_join", "Rel_r_s_join_t_join", "Not an equality or iff proposition"),
    ("Multiset_bind_zero", "s_bind_fun_eq_gt_0_colon_a_to_Multiset_b_eq_0", "Not an equality or iff proposition"),
    ("Multiset_bind_hcongr", "bind_m_f_bind_m_f_prime", "Not an equality or iff proposition"),
    ("Multiset_rel_bind", "Rel_p_s_bind_f_t_bind_g", "Not an equality or iff proposition"),
    ("Multiset_le_bind", "f_x_le_S_bind_f", "Not an equality or iff proposition"),
    ("Multiset_countP_le_card", "countP_p_s_le_card_s", "Not an equality or iff proposition"),
    ("Multiset_countP_le_of_le", "countP_p_s_le_countP_p_t", "Not an equality or iff proposition"),
    ("Multiset_countP_pos_of_mem", "_0_lt_countP_p_s", "Not an equality or iff proposition"),
    ("Multiset_dedup_le", "dedup_s_le_s", "Not an equality or iff proposition"),
    ("Multiset_dedup_subset", "dedup_s_sub_s", "Not an equality or iff proposition"),
    ("Multiset_subset_dedup", "s_sub_dedup_s", "Not an equality or iff proposition"),
    ("Multiset_dedup_subset", "_unknown", "Empty proposition"),
    ("Multiset_subset_dedup", "_unknown", "Empty proposition"),
    ("Multiset_nodup_dedup", "Nodup_dedup_s", "Not an equality or iff proposition"),
    ("List_Subset_dedup_append_left", "List_dedup_s_plus_plus_t_tilde_List_dedup_s", "Not an equality or iff proposition"),
    ("Multiset_quot_mk_to_coe", "at_Eq_Multiset_a_l_l", "Not an equality or iff proposition"),
    ("Multiset_quot_mk_to_coe", "_unknown", "Empty proposition"),
    ("Multiset_quot_mk_to_coe", "_unknown", "Empty proposition"),
    ("Multiset_IsDershowitzMannaLT_trans", "IsDershowitzMannaLT_M_N_to_IsDershowitzMannaLT_N_P_to_IsDershowitzMannaLT_M_P", "Not an equality or iff proposition"),
    ("Multiset_isDershowitzMannaLT_of_oneStep", "OneStep_M_N_to_IsDershowitzMannaLT_M_N", "Not an equality or iff proposition"),
    ("Multiset_acc_oneStep_cons_of_acc_lt", "forall_M_Acc_OneStep_M_to_Acc_OneStep_a_colon_colon_M", "Not an equality or iff proposition"),
    ("Multiset_acc_oneStep_of_acc_lt", "Acc_OneStep_M", "Not an equality or iff proposition"),
    ("Multiset_isDershowitzMannaLT_singleton_wf", "WellFounded_OneStep_colon_Multiset_a_to_Multiset_a_to_Prop", "Not an equality or iff proposition"),
    ("Multiset_transGen_oneStep_of_isDershowitzMannaLT", "IsDershowitzMannaLT_M_N_to_TransGen_OneStep_M_N", "Not an equality or iff proposition"),
    ("Multiset_isDershowitzMannaLT_of_transGen_oneStep", "IsDershowitzMannaLT_M_N", "Not an equality or iff proposition"),
    ("Multiset_transGen_oneStep_eq_isDershowitzMannaLT", "TransGen_OneStep_colon_Multiset_a_to_Multiset_a_to_Prop_eq_IsDershowitzMannaLT", "Not an equality or iff proposition"),
    ("Multiset_wellFounded_isDershowitzMannaLT", "WellFounded_IsDershowitzMannaLT_colon_Multiset_a_to_Multiset_a_to_Prop", "Not an equality or iff proposition"),
    ("Multiset_filter_le", "filter_p_s_le_s", "Not an equality or iff proposition"),
    ("Multiset_filter_subset", "filter_p_s_sub_s", "Not an equality or iff proposition"),
    ("Multiset_filter_le_filter", "filter_p_s_le_filter_p_t", "Not an equality or iff proposition"),
    ("Multiset_monotone_filter_left", "Monotone_filter_p", "Not an equality or iff proposition"),
    ("Multiset_monotone_filter_right", "_unknown", "Empty proposition"),
    ("Multiset_of_mem_filter", "p_a", "Not an equality or iff proposition"),
    ("Multiset_mem_of_mem_filter", "a_in_s", "Not an equality or iff proposition"),
    ("Multiset_mem_filter_of_mem", "a_in_filter_p_l", "Not an equality or iff proposition"),
    ("Multiset_map_filter", "_unknown", "Empty proposition"),
    ("Multiset_filterMap_le_filterMap", "filterMap_f_s_le_filterMap_f_t", "Not an equality or iff proposition"),
    ("Multiset_le_ndinsert_self", "s_le_ndinsert_a_s", "Not an equality or iff proposition"),
    ("Multiset_mem_ndinsert_self", "a_in_ndinsert_a_s", "Not an equality or iff proposition"),
    ("Multiset_mem_ndinsert_of_mem", "a_in_ndinsert_b_s", "Not an equality or iff proposition"),
    ("Multiset_Nodup_ndinsert", "Nodup_s_to_Nodup_ndinsert_a_s", "Not an equality or iff proposition"),
    ("Multiset_le_ndunion_right", "t_le_ndunion_s_t", "Not an equality or iff proposition"),
    ("Multiset_subset_ndunion_right", "t_sub_ndunion_s_t", "Not an equality or iff proposition"),
    ("Multiset_ndunion_le_add", "ndunion_s_t_le_s_plus_t", "Not an equality or iff proposition"),
    ("Multiset_subset_ndunion_left", "s_sub_ndunion_s_t", "Not an equality or iff proposition"),
    ("Multiset_le_ndunion_left", "s_le_ndunion_s_t", "Not an equality or iff proposition"),
    ("Multiset_ndunion_le_union", "ndunion_s_t_le_s_union_t", "Not an equality or iff proposition"),
    ("Multiset_Nodup_ndunion", "Nodup_t_to_Nodup_ndunion_s_t", "Not an equality or iff proposition"),
    ("Multiset_Nodup_ndinter", "Nodup_s_to_Nodup_ndinter_s_t", "Not an equality or iff proposition"),
    ("Multiset_ndinter_le_left", "ndinter_s_t_le_s", "Not an equality or iff proposition"),
    ("Multiset_ndinter_subset_left", "ndinter_s_t_sub_s", "Not an equality or iff proposition"),
    ("Multiset_ndinter_subset_right", "ndinter_s_t_sub_t", "Not an equality or iff proposition"),
    ("Multiset_ndinter_le_right", "ndinter_s_t_le_t", "Not an equality or iff proposition"),
    ("Multiset_inter_le_ndinter", "s_inter_t_le_ndinter_s_t", "Not an equality or iff proposition"),
    ("Multiset_Nodup_inter", "Nodup_s_inter_t", "Not an equality or iff proposition"),
    ("Multiset_coe_mem", "x_in_m", "Not an equality or iff proposition"),
    ("Multiset_mem_of_mem_toEnumFinset", "p_1_in_m", "Not an equality or iff proposition"),
    ("Multiset_map_fst_le_of_subset_toEnumFinset", "s_1_map_Prod_fst_le_m", "Not an equality or iff proposition"),
    ("Multiset_toEnumFinset_mono", "m_1_toEnumFinset_sub_m_2_toEnumFinset", "Not an equality or iff proposition"),
    ("Multiset_fold_cons", "_unknown", "Empty proposition"),
    ("Multiset_fold_cons", "_unknown", "Empty proposition"),
    ("Multiset_pure_def", "pure_colon_a_to_Multiset_a_eq_singleton", "Not an equality or iff proposition"),
    ("Multiset_id_traverse", "traverse_pure_colon_a_to_Id_a_x_eq_pure_x", "Not an equality or iff proposition"),
    ("Multiset_le_sup", "a_le_s_sup", "Not an equality or iff proposition"),
    ("Multiset_sup_mono", "s_1_sup_le_s_2_sup", "Not an equality or iff proposition"),
    ("Multiset_map_hcongr", "map_f_m_map_f_prime_m", "Not an equality or iff proposition"),
    ("Multiset_mem_map_of_mem", "f_a_in_map_f_s", "Not an equality or iff proposition"),
    ("Multiset_map_id", "_unknown", "Empty proposition"),
    ("Multiset_map_const", "_unknown", "Empty proposition"),
    ("Multiset_map_le_map", "map_f_s_le_map_f_t", "Not an equality or iff proposition"),
    ("Multiset_map_lt_map", "s_map_f_lt_t_map_f", "Not an equality or iff proposition"),
    ("Multiset_map_mono", "Monotone_map_f", "Not an equality or iff proposition"),
    ("Multiset_map_strictMono", "StrictMono_map_f", "Not an equality or iff proposition"),
    ("Multiset_map_subset_map", "map_f_s_sub_map_f_t", "Not an equality or iff proposition"),
    ("Multiset_map_surjective_of_surjective", "Function_Surjective_map_f", "Not an equality or iff proposition"),
    ("Multiset_Nat_nodup_antidiagonal", "Nodup_antidiagonal_n", "Not an equality or iff proposition"),
    ("Multiset_Nat_antidiagonal_succ", "_unknown", "Empty proposition"),
    ("Multiset_Nat_antidiagonal_succ_succ", "_unknown", "Empty proposition"),
    ("Multiset_Pairwise_forall", "forall_a_a_in_s_to_forall_b_b_in_s_to_a_ne_b_to_r_a_b", "Not an equality or iff proposition"),
    ("Multiset_Pi_cons_swap", "Pi_cons_a_prime_colon_colon_m_a_b_Pi_cons_m_a_prime_b_prime_f_Pi_cons_a_colon_colon_m_a_prime_b_prime_Pi_c", "Not an equality or iff proposition"),
    ("Multiset_Pi_forall_rel_cons_ext", "forall_a_ha_r_cons_b_1_f_1_a_ha_cons_b_2_f_2_a_ha", "Not an equality or iff proposition"),
    ("Multiset_Pi_cons_injective", "Function_Injective_Pi_cons_s_a_b", "Not an equality or iff proposition"),
    ("Multiset_Nodup_pi", "Nodup_s_to_forall_a_in_s_Nodup_t_a_to_Nodup_pi_s_t", "Not an equality or iff proposition"),
    ("Multiset_powersetAux_perm_powersetAux", "_unknown", "Empty proposition"),
    ("Multiset_powersetAux", "_unknown", "Empty proposition"),
    ("Multiset_powersetAux", "_unknown", "Empty proposition"),
    ("Multiset_powerset_aux", "_unknown", "Empty proposition"),
    ("Multiset_powersetAux_perm", "powersetAux_l_1_tilde_powersetAux_l_2", "Not an equality or iff proposition"),
    ("Multiset_powerset_coe", "_unknown", "Empty proposition"),
    ("Multiset_map_single_le_powerset", "s_map_singleton_le_powerset_s", "Not an equality or iff proposition"),
    ("Multiset_zero_mem_powerset", "_0_in_s_powerset", "Not an equality or iff proposition"),
    ("Multiset_self_mem_powerset", "s_in_s_powerset", "Not an equality or iff proposition"),
    ("Multiset_revzip_powersetAux", "_unknown", "Empty proposition"),
    ("Multiset_revzip_powersetAux", "_unknown", "Empty proposition"),
    ("Multiset_revzip_powersetAux_perm_aux", "_unknown", "Empty proposition"),
    ("Multiset_revzip_powersetAux_perm", "revzip_powersetAux_l_1_tilde_revzip_powersetAux_l_2", "Not an equality or iff proposition"),
    ("Multiset_powerset_injective", "Function_Injective_at_Multiset_powerset_a", "Not an equality or iff proposition"),
    ("Multiset_powerset_strictMono", "StrictMono_at_Multiset_powerset_a", "Not an equality or iff proposition"),
    ("Multiset_powerset_mono", "Monotone_at_Multiset_powerset_a", "Not an equality or iff proposition"),
    ("Multiset_powersetCardAux_perm", "powersetCardAux_n_l_1_tilde_powersetCardAux_n_l_2", "Not an equality or iff proposition"),
    ("Multiset_powersetCard_coe", "_unknown", "Empty proposition"),
    ("Multiset_powersetCard_le_powerset", "powersetCard_n_s_le_powerset_s", "Not an equality or iff proposition"),
    ("Multiset_powersetCard_mono", "powersetCard_n_s_le_powersetCard_n_t", "Not an equality or iff proposition"),
    ("Multiset_Nodup_powersetCard", "Nodup_powersetCard_n_s", "Not an equality or iff proposition"),
    ("Multiset_notMem_range_self", "n_notin_range_n", "Not an equality or iff proposition"),
    ("Multiset_self_mem_range_succ", "n_in_range_n_plus_1", "Not an equality or iff proposition"),
    ("Multiset_range_disjoint_map_add", "Disjoint_range_a_m_map_a_plus", "Not an equality or iff proposition"),
    ("Multiset_nodup_range", "Nodup_range_n", "Not an equality or iff proposition"),
    ("Multiset_replicate_right_injective", "Injective_at_replicate_a_n", "Not an equality or iff proposition"),
    ("Multiset_replicate_left_injective", "Injective_replicate_a", "Not an equality or iff proposition"),
    ("Multiset_replicate_subset_singleton", "replicate_n_a_sub_a", "Not an equality or iff proposition"),
    ("Multiset_replicate_mono", "replicate_k_a_le_replicate_n_a", "Not an equality or iff proposition"),
    ("Multiset_pairwise_sort", "sort_s_r_Pairwise_r", "Not an equality or iff proposition"),
    ("Multiset_disjSum_mono", "s_1_disjSum_t_1_le_s_2_disjSum_t_2", "Not an equality or iff proposition"),
    ("Multiset_disjSum_mono_right", "Monotone_s_disjSum_colon_Multiset_b_to_Multiset_a_b", "Not an equality or iff proposition"),
    ("Multiset_disjSum_lt_disjSum_of_lt_of_le", "s_1_disjSum_t_1_lt_s_2_disjSum_t_2", "Not an equality or iff proposition"),
    ("Multiset_disjSum_lt_disjSum_of_le_of_lt", "s_1_disjSum_t_1_lt_s_2_disjSum_t_2", "Not an equality or iff proposition"),
    ("Multiset_disjSum_strictMono_right", "StrictMono_s_disjSum_colon_Multiset_b_to_Multiset_a_b", "Not an equality or iff proposition"),
    ("Multiset_Nodup_disjSum", "s_disjSum_t_Nodup", "Not an equality or iff proposition"),
    ("Multiset_Nodup_sym2", "m_sym2_Nodup", "Not an equality or iff proposition"),
    ("Multiset_sym2_mono", "m_sym2_le_m_prime_sym2", "Not an equality or iff proposition"),
    ("Multiset_monotone_sym2", "Monotone_Multiset_sym2_colon_Multiset_a_to", "Not an equality or iff proposition"),
    ("Multiset_le_union_left", "s_le_s_union_t", "Not an equality or iff proposition"),
    ("Multiset_le_union_right", "t_le_s_union_t", "Not an equality or iff proposition"),
    ("Multiset_union_le_union_right", "s_union_u_le_t_union_u", "Not an equality or iff proposition"),
    ("Multiset_union_le", "s_union_t_le_u", "Not an equality or iff proposition"),
    ("Multiset_inter_le_left", "s_inter_t_le_s", "Not an equality or iff proposition"),
    ("Multiset_inter_le_right", "s_inter_t_le_t", "Not an equality or iff proposition"),
    ("Multiset_le_inter", "s_le_t_inter_u", "Not an equality or iff proposition"),
    ("Multiset_union_le_union_left", "u_union_s_le_u_union_t", "Not an equality or iff proposition"),
    ("Multiset_union_le_add", "s_union_t_le_s_plus_t", "Not an equality or iff proposition"),
    ("Multiset_induction", "forall_s_p_s", "Not an equality or iff proposition"),
    ("Multiset_induction_on", "p_s", "Not an equality or iff proposition"),
    ("Multiset_finite_toSet", "x_pipe_x_in_s_Finite", "Not an equality or iff proposition"),
    ("Multiset_aestronglyMeasurable_prod", "AEStronglyMeasurable_l_prod_mu", "Not an equality or iff proposition"),
    ("Multiset_stronglyMeasurable_prod", "StronglyMeasurable_l_prod", "Not an equality or iff proposition"),
    ("Multiset_measurable_prod", "Measurable_l_prod", "Not an equality or iff proposition"),
    ("Multiset_aemeasurable_prod", "AEMeasurable_l_prod_mu", "Not an equality or iff proposition"),
    ("Multiset_iSup_mem_map_of_exists_sSup_empty_le", "x_in_s_f_x_in_s_map_f", "Not an equality or iff proposition"),
    ("Multiset_iInf_mem_map_of_exists_le_sInf_empty", "x_in_s_f_x_in_s_map_f", "Not an equality or iff proposition"),
    ("Multiset_iSup_mem_map_of_ne_zero", "x_in_s_f_x_in_s_map_f", "Not an equality or iff proposition"),
    ("Multiset_prod_X_add_C_coeff", "_unknown", "Empty proposition"),
    ("Mathlib_Meta_Multiset_range_zero", "_unknown", "Empty proposition"),
    ("Mathlib_Meta_Multiset_range_succ", "_unknown", "Empty proposition"),
]
