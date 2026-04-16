"""Mathlib: Function — auto-generated from Mathlib4.

Contains 400 rewrite rules derived from Mathlib theorems.
Plus 579 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_function"
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

def _r0000_mul_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.End.mul_def
    # (f * g) = f ∘ g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("comp", (args[0], args[1]))
            results.append((rhs, "Mathlib: Function_End_mul_def"))
        except Exception:
            pass
    return results


def _r0001_update_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.update_mul
    # update (f₁ * f₂) i (x₁ * x₂) = update f₁ i x₁ * update f₂ i x₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "update", 3)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("update", (OVar("f_1"), args[1], OVar("x_1"),)), OOp("update", (OVar("f_2"), args[1], OVar("x_2"),))))
            results.append((rhs, "Mathlib: Function_update_mul"))
        except Exception:
            pass
    return results


def _r0002_mulSupport_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.mulSupport_inv
    # mulSupport f⁻¹ = mulSupport f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulSupport", 1)
    if args is not None:
        try:
            rhs = OOp("mulSupport", (OVar("f"),))
            results.append((rhs, "Mathlib: Function_mulSupport_inv"))
        except Exception:
            pass
    return results


def _r0003_mulSupport_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subsingleton.mulSupport_eq
    # mulSupport f = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulSupport", 1)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Subsingleton_mulSupport_eq"))
        except Exception:
            pass
    return results


def _r0004_mulSupport_const(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.mulSupport_const
    # (mulSupport fun _ : ι ↦ c) = Set.univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulSupport", 6)
    if args is not None:
        try:
            rhs = OVar("Set_univ")
            results.append((rhs, "Mathlib: Function_mulSupport_const"))
        except Exception:
            pass
    return results


def _r0005_funext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.funext
    # (fun x => f (x + c)) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun", 4)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: Function_Periodic_funext"))
        except Exception:
            pass
    return results


def _r0006_funext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Antiperiodic.funext
    # (fun x => f (x + c)) = -f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun", 4)
    if args is not None:
        try:
            rhs = OVar("minus_f")
            results.append((rhs, "Mathlib: Function_Antiperiodic_funext"))
        except Exception:
            pass
    return results


def _r0007_uncurry_curry(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.OfArity.uncurry_curry
    # uncurry (curry f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "uncurry", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Function_OfArity_uncurry_curry"))
        except Exception:
            pass
    return results


def _r0008_curry_two_eq_curry(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.OfArity.curry_two_eq_curry
    # curry f = Function.curry (f ∘ (finTwoArrowEquiv α).symm)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "curry", 1)
    if args is not None:
        try:
            rhs = OOp("Function_curry", (OOp("comp", (args[0], OVar("finTwoArrowEquiv_a_symm"))),))
            results.append((rhs, "Mathlib: Function_OfArity_curry_two_eq_curry"))
        except Exception:
            pass
    return results


def _r0009_updateFinset_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.updateFinset_singleton
    # updateFinset x {i} y = Function.update x i (y ⟨i, mem_singleton_self i⟩)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "updateFinset", 3)
    if args is not None:
        try:
            rhs = OOp("Function_update", (args[0], args[1], OOp("y", (OVar("i_mem_singleton_self_i"),)),))
            results.append((rhs, "Mathlib: Function_updateFinset_singleton"))
        except Exception:
            pass
    return results


def _r0010_invFun_restrict(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Injective.invFun_restrict
    # (Set.range f).restrict (invFun f) = hf.invOfMemRange
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_range_f_restrict", 1)
    if args is not None:
        try:
            rhs = OVar("hf_invOfMemRange")
            results.append((rhs, "Mathlib: Function_Injective_invFun_restrict"))
        except Exception:
            pass
    return results


def _r0011_right_inv_of_invOfMemRange(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.right_inv_of_invOfMemRange
    # f.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_invOfMemRange", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Function_Embedding_right_inv_of_invOfMemRange"))
        except Exception:
            pass
    return results


def _r0012_invFun_restrict(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.invFun_restrict
    # (Set.range f).restrict (invFun f) = f.invOfMemRange
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_range_f_restrict", 1)
    if args is not None:
        try:
            rhs = OVar("f_invOfMemRange")
            results.append((rhs, "Mathlib: Function_Embedding_invFun_restrict"))
        except Exception:
            pass
    return results


def _r0013_list_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Injective.list_map
    # Injective (map f)   | [], [], _ => rfl   | x :: xs, y :: ys, hxy =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "injective", 5)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("rfl"), args[1], OVar("x"), OVar("colon_colon"), OVar("xs"), OVar("y"), OVar("colon_colon"), OVar("ys"), OVar("hxy"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: Function_Injective_list_map"))
        except Exception:
            pass
    return results


def _r0014_graph_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.graph_comp
    # graph (f ∘ g) = graph g ○ graph f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "graph", 1)
    if args is not None:
        try:
            rhs = OOp("graph", (OVar("g"), OVar("_unknown"), OVar("graph"), OVar("f"),))
            results.append((rhs, "Mathlib: Function_graph_comp"))
        except Exception:
            pass
    return results


def _r0015_invFunOn_apply_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.invFunOn_apply_eq
    # f (invFunOn f s (f a)) = f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("a"),))
            results.append((rhs, "Mathlib: Function_invFunOn_apply_eq"))
        except Exception:
            pass
    return results


def _r0016_mem_fixedPoints_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.mem_fixedPoints_iff
    # x ∈ fixedPoints f ↔ f x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Function_mem_fixedPoints_iff"))
        except Exception:
            pass
    return results


def _r0017_iterate_add_minimalPeriod_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.iterate_add_minimalPeriod_eq
    # f^[n + minimalPeriod f x] x = f^[n] x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fpow_n_plus_minimalPeriod_f_x", 1)
    if args is not None:
        try:
            rhs = OOp("fpow_n", (args[0],))
            results.append((rhs, "Mathlib: Function_iterate_add_minimalPeriod_eq"))
        except Exception:
            pass
    return results


def _r0018_periodicOrbit_eq_nil_iff_not_periodic_pt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.periodicOrbit_eq_nil_iff_not_periodic_pt
    # periodicOrbit f x = Cycle.nil ↔ x ∉ periodicPts f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "periodicOrbit", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (OVar("Cycle_nil"), OOp("not_in", (args[1], OOp("periodicPts", (args[0],))))))
            results.append((rhs, "Mathlib: Function_periodicOrbit_eq_nil_iff_not_periodic_pt"))
        except Exception:
            pass
    return results


def _r0019_coe_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.coe_smul
    # ⇑(g • f) = g • ⇑f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("g_f")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("g", (OVar("_unknown"), OVar("f"),))
            results.append((rhs, "Mathlib: Function_Embedding_coe_smul"))
    except Exception:
        pass
    return results


def _r0020_mk_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.mk_coe
    # (⟨f, inj⟩ : α ↪ β) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_inj", 4)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Function_Embedding_mk_coe"))
        except Exception:
            pass
    return results


def _r0021_coe_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.coe_refl
    # ⇑(Embedding.refl α) = id
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Embedding_refl_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Function_Embedding_coe_refl"))
    except Exception:
        pass
    return results


def _r0022_coe_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.coe_trans
    # ⇑(f.trans g) = ⇑g ∘ ⇑f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_trans_g")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comp", (OVar("g"), OVar("f")))
            results.append((rhs, "Mathlib: Function_Embedding_coe_trans"))
    except Exception:
        pass
    return results


def _r0023_mk_trans_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.mk_trans_mk
    # (mk f hf).trans (mk g hg) = mk (g ∘ f) (hg.comp hf)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mk_f_hf_trans", 1)
    if args is not None:
        try:
            rhs = OOp("pair", (OOp("comp", (OVar("g"), OVar("f"))), OOp("hg_comp", (OVar("hf"),)),))
            results.append((rhs, "Mathlib: Function_Embedding_mk_trans_mk"))
        except Exception:
            pass
    return results


def _r0024_equiv_toEmbedding_trans_symm_toEmbedding(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.equiv_toEmbedding_trans_symm_toEmbedding
    # e.toEmbedding.trans e.symm.toEmbedding = Embedding.refl _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_toEmbedding_trans", 1)
    if args is not None:
        try:
            rhs = OOp("Embedding_refl", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: Function_Embedding_equiv_toEmbedding_trans_symm_toEmbedding"))
        except Exception:
            pass
    return results


def _r0025_sumSet_preimage_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.sumSet_preimage_inr
    # .inr ⁻¹' (Function.Embedding.sumSet h ⁻¹' r) = r ∩ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inr", 2)
    if args is not None:
        try:
            rhs = OOp("inter", (OVar("r"), OVar("t")))
            results.append((rhs, "Mathlib: Function_Embedding_sumSet_preimage_inr"))
        except Exception:
            pass
    return results


def _r0026_sumSet_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.sumSet_range
    # range (Function.Embedding.sumSet h) = s ∪ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OOp("union", (OVar("s"), OVar("t")))
            results.append((rhs, "Mathlib: Function_Embedding_sumSet_range"))
        except Exception:
            pass
    return results


def _r0027_toPerm_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Involutive.toPerm_symm
    # (h.toPerm f).symm = h.toPerm f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("h_toPerm_f_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("h_toPerm", (OVar("f"),))
            results.append((rhs, "Mathlib: Function_Involutive_toPerm_symm"))
    except Exception:
        pass
    return results


def _r0028_toEquivRange_eq_ofInjective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.toEquivRange_eq_ofInjective
    # f.toEquivRange = Equiv.ofInjective f f.injective
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toEquivRange")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Equiv_ofInjective", (OVar("f"), OVar("f_injective"),))
            results.append((rhs, "Mathlib: Function_Embedding_toEquivRange_eq_ofInjective"))
    except Exception:
        pass
    return results


def _r0029_eval_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.eval_apply
    # eval x f = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eval", 2)
    if args is not None:
        try:
            rhs = OOp("f", (args[0],))
            results.append((rhs, "Mathlib: Function_eval_apply"))
        except Exception:
            pass
    return results


def _r0030_onFun_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.onFun_apply
    # onFun f g a b = f (g a) (g b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "onFun", 4)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("g", (args[2],)), OOp("g", (args[3],)),))
            results.append((rhs, "Mathlib: Function_onFun_apply"))
        except Exception:
            pass
    return results


def _r0031_eq_rec_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.LeftInverse.eq_rec_eq
    # @Eq.rec β (f (g (f a))) (fun x _ ↦ γ x) (C (g (f a))) (f a) (congr_arg f (h a)) = C a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_Eq_rec", 6)
    if args is not None:
        try:
            rhs = OOp("C", (OVar("a"),))
            results.append((rhs, "Mathlib: Function_LeftInverse_eq_rec_eq"))
        except Exception:
            pass
    return results


def _r0032_const_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.FromTypes.const_succ
    # const p t = fun _ => const (vecTail p) t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "const", 2)
    if args is not None:
        try:
            rhs = OOp("fun", (OVar("_unknown"), OVar("eq_gt"), OVar("const"), OOp("vecTail", (args[0],)), args[1],))
            results.append((rhs, "Mathlib: Function_FromTypes_const_succ"))
        except Exception:
            pass
    return results


def _r0033_const_succ_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.FromTypes.const_succ_apply
    # const p t x = const (vecTail p) t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "const", 3)
    if args is not None:
        try:
            rhs = OOp("const", (OOp("vecTail", (args[0],)), args[1],))
            results.append((rhs, "Mathlib: Function_FromTypes_const_succ_apply"))
        except Exception:
            pass
    return results


def _r0034_iterate_zero_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.iterate_zero_apply
    # f^[0] x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fpow_0", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Function_iterate_zero_apply"))
        except Exception:
            pass
    return results


def _r0035_iterate_succ_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.iterate_succ_apply
    # f^[n.succ] x = f^[n] (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fpow_n_succ", 1)
    if args is not None:
        try:
            rhs = OOp("fpow_n", (OOp("f", (args[0],)),))
            results.append((rhs, "Mathlib: Function_iterate_succ_apply"))
        except Exception:
            pass
    return results


def _r0036_iterate_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.iterate_add
    # ∀ n : ℕ, f^[m + n] = f^[m] ∘ f^[n]   | 0 => rfl   | Nat.succ n =>
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("fpow_m_plus_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comp", (OVar("fpow_m"), OOp("fpow_n", (OVar("pipe"), OLit(0), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("Nat_succ"), OVar("n"), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: Function_iterate_add"))
    except Exception:
        pass
    return results


def _r0037_iterate_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.iterate_mul
    # ∀ n, f^[m * n] = f^[m]^[n]   | 0 =>
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("fpow_m_star_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("fpow_m_pow_n", (OVar("pipe"), OLit(0), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: Function_iterate_mul"))
    except Exception:
        pass
    return results


def _r0038_ofArity_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.ofArity_succ
    # OfArity α β n.succ = (α → OfArity α β n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "OfArity", 3)
    if args is not None:
        try:
            rhs = OOp("implies", (args[0], OOp("OfArity", (args[0], args[1], OVar("n"),))))
            results.append((rhs, "Mathlib: Function_ofArity_succ"))
        except Exception:
            pass
    return results


def _r0039_const_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.OfArity.const_succ
    # const α b n.succ = fun _ => const _ b n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "const", 3)
    if args is not None:
        try:
            rhs = OOp("fun", (OVar("_unknown"), OVar("eq_gt"), OVar("const"), OVar("_unknown"), args[1], OVar("n"),))
            results.append((rhs, "Mathlib: Function_OfArity_const_succ"))
        except Exception:
            pass
    return results


def _r0040_coe_injective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Embedding.coe_injective
    # @Function.Injective (M ↪[L] N) (M → N) (↑)   | _, _, h => DFunLike.ext'_iff.mpr h  @[ext] theorem ext ⦃f g : M ↪[L] N⦄ (
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "N_pipe_h_eq_gt_DFunLike_ext_prime_iff_mpr_h_at_ext_theorem_ext_f_g_colon_M_L_N_h", 5)
    if args is not None:
        try:
            rhs = OOp("g", (OVar("x_colon_f_eq_g"),))
            results.append((rhs, "Mathlib: FirstOrder_Language_Embedding_coe_injective"))
        except Exception:
            pass
    return results


def _r0041_comp_toHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Embedding.comp_toHom
    # (hnp.comp hmn).toHom = hnp.toHom.comp hmn.toHom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hnp_comp_hmn_toHom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("hnp_toHom_comp", (OVar("hmn_toHom"),))
            results.append((rhs, "Mathlib: FirstOrder_Language_Embedding_comp_toHom"))
    except Exception:
        pass
    return results


def _r0042_refl_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Embedding.refl_comp
    # (refl L N).comp f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "refl_L_N_comp", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: FirstOrder_Language_Embedding_refl_comp"))
        except Exception:
            pass
    return results


def _r0043_refl_toHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Embedding.refl_toHom
    # (refl L M).toHom = Hom.id L M
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("refl_L_M_toHom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Hom_id", (OVar("L"), OVar("M"),))
            results.append((rhs, "Mathlib: FirstOrder_Language_Embedding_refl_toHom"))
    except Exception:
        pass
    return results


def _r0044_subtype_equivRange(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Embedding.subtype_equivRange
    # (subtype _).comp f.equivRange.toEmbedding = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "subtype_comp", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Embedding_subtype_equivRange"))
        except Exception:
            pass
    return results


def _r0045_X_zpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FunctionField.inftyValuation.X_zpow
    # inftyValuation F (RatFunc.X ^ m) = exp m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inftyValuation", 2)
    if args is not None:
        try:
            rhs = OOp("exp", (OVar("m"),))
            results.append((rhs, "Mathlib: FunctionField_inftyValuation_X_zpow"))
        except Exception:
            pass
    return results


def _r0046_negPart_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.locallyFinsuppWithin.negPart_apply
    # a⁻ x = (a x)⁻
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ainv", 1)
    if args is not None:
        try:
            rhs = OVar("a_x_inv")
            results.append((rhs, "Mathlib: Function_locallyFinsuppWithin_negPart_apply"))
        except Exception:
            pass
    return results


def _r0047_mul_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.SurjectiveOfEpiAuxs.mul_smul
    # (b * b') • x = b • b' • x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "b_star_b_prime", 2)
    if args is not None:
        try:
            rhs = OOp("b", (args[0], OVar("b_prime"), args[0], args[1],))
            results.append((rhs, "Mathlib: GrpCat_SurjectiveOfEpiAuxs_mul_smul"))
        except Exception:
            pass
    return results


def _r0048_one_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.SurjectiveOfEpiAuxs.one_smul
    # (1 : B) • x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_B", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: GrpCat_SurjectiveOfEpiAuxs_one_smul"))
        except Exception:
            pass
    return results


def _r0049_fromCoset_eq_of_mem_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.SurjectiveOfEpiAuxs.fromCoset_eq_of_mem_range
    # fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fromCoset", 1)
    if args is not None:
        try:
            rhs = OOp("fromCoset", (OVar("f_hom_range_1_one_leftCoset"),))
            results.append((rhs, "Mathlib: GrpCat_SurjectiveOfEpiAuxs_fromCoset_eq_of_mem_range"))
        except Exception:
            pass
    return results


def _r0050_tau_apply_infinity(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.SurjectiveOfEpiAuxs.τ_apply_infinity
    # τ ∞ = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tau", 1)
    if args is not None:
        try:
            rhs = OOp("fromCoset", (OVar("f_hom_range_1_one_leftCoset"),))
            results.append((rhs, "Mathlib: GrpCat_SurjectiveOfEpiAuxs_tau_apply_infinity"))
        except Exception:
            pass
    return results


def _r0051_tau_apply_fromCoset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.SurjectiveOfEpiAuxs.τ_apply_fromCoset
    # τ (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) = ∞
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tau", 1)
    if args is not None:
        try:
            rhs = OVar("inf")
            results.append((rhs, "Mathlib: GrpCat_SurjectiveOfEpiAuxs_tau_apply_fromCoset"))
        except Exception:
            pass
    return results


def _r0052_tau_symm_apply_fromCoset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.SurjectiveOfEpiAuxs.τ_symm_apply_fromCoset
    # Equiv.symm τ (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) = ∞
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Equiv_symm", 2)
    if args is not None:
        try:
            rhs = OVar("inf")
            results.append((rhs, "Mathlib: GrpCat_SurjectiveOfEpiAuxs_tau_symm_apply_fromCoset"))
        except Exception:
            pass
    return results


def _r0053_tau_symm_apply_infinity(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.SurjectiveOfEpiAuxs.τ_symm_apply_infinity
    # Equiv.symm τ ∞ = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Equiv_symm", 2)
    if args is not None:
        try:
            rhs = OOp("fromCoset", (OVar("f_hom_range_1_one_leftCoset"),))
            results.append((rhs, "Mathlib: GrpCat_SurjectiveOfEpiAuxs_tau_symm_apply_infinity"))
        except Exception:
            pass
    return results


def _r0054_g_apply_fromCoset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.SurjectiveOfEpiAuxs.g_apply_fromCoset
    # g x (fromCoset y) = fromCoset ⟨x • ↑y,
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g", 2)
    if args is not None:
        try:
            rhs = OOp("fromCoset", (OVar("x_y"),))
            results.append((rhs, "Mathlib: GrpCat_SurjectiveOfEpiAuxs_g_apply_fromCoset"))
        except Exception:
            pass
    return results


def _r0055_g_apply_infinity(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.SurjectiveOfEpiAuxs.g_apply_infinity
    # (g x) ∞ = ∞
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_x", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: GrpCat_SurjectiveOfEpiAuxs_g_apply_infinity"))
        except Exception:
            pass
    return results


def _r0056_h_apply_infinity(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.SurjectiveOfEpiAuxs.h_apply_infinity
    # (h x) ∞ = ∞
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_x", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: GrpCat_SurjectiveOfEpiAuxs_h_apply_infinity"))
        except Exception:
            pass
    return results


def _r0057_h_apply_fromCoset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.SurjectiveOfEpiAuxs.h_apply_fromCoset
    # (h x) (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) =       fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_x", 1)
    if args is not None:
        try:
            rhs = OOp("fromCoset", (OVar("f_hom_range_1_one_leftCoset"),))
            results.append((rhs, "Mathlib: GrpCat_SurjectiveOfEpiAuxs_h_apply_fromCoset"))
        except Exception:
            pass
    return results


def _r0058_h_apply_fromCoset_nin_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.SurjectiveOfEpiAuxs.h_apply_fromCoset_nin_range
    # h x (fromCoset ⟨b • f.hom.range, b, rfl⟩) = fromCoset ⟨(x * b) • ↑f.hom.range, x * b, rfl⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h", 2)
    if args is not None:
        try:
            rhs = OOp("fromCoset", (OVar("x_star_b_f_hom_range_x_star_b_rfl"),))
            results.append((rhs, "Mathlib: GrpCat_SurjectiveOfEpiAuxs_h_apply_fromCoset_nin_range"))
        except Exception:
            pass
    return results


def _r0059_agree(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.SurjectiveOfEpiAuxs.agree
    # f.hom.range = { x | h x = g x }
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_hom_range")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x_pipe_h_x_eq_g_x")
            results.append((rhs, "Mathlib: GrpCat_SurjectiveOfEpiAuxs_agree"))
    except Exception:
        pass
    return results


def _r0060_comp_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.SurjectiveOfEpiAuxs.comp_eq
    # (f ≫ ofHom g) = f ≫ ofHom h
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 3)
    if args is not None:
        try:
            rhs = OOp("f", (args[0], args[1], OVar("h"),))
            results.append((rhs, "Mathlib: GrpCat_SurjectiveOfEpiAuxs_comp_eq"))
        except Exception:
            pass
    return results


def _r0061_apply_apply_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.MulExact.apply_apply_eq_one
    # g (f x) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Function_MulExact_apply_apply_eq_one"))
        except Exception:
            pass
    return results


def _r0062_comp_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.MulExact.comp_eq_one
    # g.comp f = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_comp", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Function_MulExact_comp_eq_one"))
        except Exception:
            pass
    return results


def _r0063_monoidHom_ker_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.MulExact.monoidHom_ker_eq
    # ker g = range f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ker", 1)
    if args is not None:
        try:
            rhs = OOp("range", (OVar("f"),))
            results.append((rhs, "Mathlib: Function_MulExact_monoidHom_ker_eq"))
        except Exception:
            pass
    return results


def _r0064_monoidHom_comp_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.MulExact.monoidHom_comp_eq_zero
    # g.comp f = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_comp", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Function_MulExact_monoidHom_comp_eq_zero"))
        except Exception:
            pass
    return results


def _r0065_linearMap_ker_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Exact.linearMap_ker_eq
    # ker g = range f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ker", 1)
    if args is not None:
        try:
            rhs = OOp("range", (OVar("f"),))
            results.append((rhs, "Mathlib: Function_Exact_linearMap_ker_eq"))
        except Exception:
            pass
    return results


def _r0066_linearMap_comp_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Exact.linearMap_comp_eq_zero
    # g.comp f = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_comp", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Function_Exact_linearMap_comp_eq_zero"))
        except Exception:
            pass
    return results


def _r0067_linearEquivOfSurjective_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Exact.linearEquivOfSurjective_symm_apply
    # (h.linearEquivOfSurjective hg).symm (g x) = Submodule.Quotient.mk x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_linearEquivOfSurjective_hg_symm", 1)
    if args is not None:
        try:
            rhs = OOp("Submodule_Quotient_mk", (OVar("x"),))
            results.append((rhs, "Mathlib: Function_Exact_linearEquivOfSurjective_symm_apply"))
        except Exception:
            pass
    return results


def _r0068_exists_mem_Ico_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.exists_mem_Ico₀
    # ∃ y ∈ Ico 0 c, f x = f y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("y"),))
            results.append((rhs, "Mathlib: Function_Periodic_exists_mem_Ico_0"))
        except Exception:
            pass
    return results


def _r0069_exists_mem_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.exists_mem_Ico
    # ∃ y ∈ Ico a (a + c), f x = f y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("y"),))
            results.append((rhs, "Mathlib: Function_Periodic_exists_mem_Ico"))
        except Exception:
            pass
    return results


def _r0070_exists_mem_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.exists_mem_Ioc
    # ∃ y ∈ Ioc a (a + c), f x = f y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("y"),))
            results.append((rhs, "Mathlib: Function_Periodic_exists_mem_Ioc"))
        except Exception:
            pass
    return results


def _r0071_image_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.image_Ioc
    # f '' Ioc a (a + c) = range f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 4)
    if args is not None:
        try:
            rhs = OOp("range", (OVar("f"),))
            results.append((rhs, "Mathlib: Function_Periodic_image_Ioc"))
        except Exception:
            pass
    return results


def _r0072_image_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.image_Icc
    # f '' Icc a (a + c) = range f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 4)
    if args is not None:
        try:
            rhs = OOp("range", (OVar("f"),))
            results.append((rhs, "Mathlib: Function_Periodic_image_Icc"))
        except Exception:
            pass
    return results


def _r0073_image_uIcc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.image_uIcc
    # f '' uIcc a (a + c) = range f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 4)
    if args is not None:
        try:
            rhs = OOp("range", (OVar("f"),))
            results.append((rhs, "Mathlib: Function_Periodic_image_uIcc"))
        except Exception:
            pass
    return results


def _r0074_add_nat_mul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Antiperiodic.add_nat_mul_eq
    # f (x + n * c) = (-1) ^ n * f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("minus_1"), OVar("n"))), OOp("f", (OVar("x"),))))
            results.append((rhs, "Mathlib: Function_Antiperiodic_add_nat_mul_eq"))
        except Exception:
            pass
    return results


def _r0075_sub_nat_mul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Antiperiodic.sub_nat_mul_eq
    # f (x - n * c) = (-1) ^ n * f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("minus_1"), OVar("n"))), OOp("f", (OVar("x"),))))
            results.append((rhs, "Mathlib: Function_Antiperiodic_sub_nat_mul_eq"))
        except Exception:
            pass
    return results


def _r0076_nat_mul_sub_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Antiperiodic.nat_mul_sub_eq
    # f (n * c - x) = (-1) ^ n * f (-x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("minus_1"), OVar("n"))), OOp("f", (OVar("minus_x"),))))
            results.append((rhs, "Mathlib: Function_Antiperiodic_nat_mul_sub_eq"))
        except Exception:
            pass
    return results


def _r0077_smul_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.End.smul_def
    # f • a = f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 2)
    if args is not None:
        try:
            rhs = OOp("f", (args[1],))
            results.append((rhs, "Mathlib: Function_End_smul_def"))
        except Exception:
            pass
    return results


def _r0078_one_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.End.one_def
    # (1 : Function.End α) = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1", 3)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Function_End_one_def"))
        except Exception:
            pass
    return results


def _r0079_update_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.update_smul
    # update (c • f₁) i (c • x₁) = c • update f₁ i x₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "update", 3)
    if args is not None:
        try:
            rhs = OOp("c", (OVar("_unknown"), OVar("update"), OVar("f_1"), args[1], OVar("x_1"),))
            results.append((rhs, "Mathlib: Function_update_smul"))
        except Exception:
            pass
    return results


def _r0080_extend_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.extend_smul
    # extend f (r • g) (r • e) = r • extend f g e
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "extend", 3)
    if args is not None:
        try:
            rhs = OOp("r", (OVar("_unknown"), OVar("extend"), args[0], OVar("g"), OVar("e"),))
            results.append((rhs, "Mathlib: Function_extend_smul"))
        except Exception:
            pass
    return results


def _r0081_map_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: EmbeddingLike.map_eq_one_iff
    # f x = 1 ↔ x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[0])), OLit(1)))
            results.append((rhs, "Mathlib: EmbeddingLike_map_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0082_extend_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.extend_mul
    # Function.extend f (g₁ * g₂) (e₁ * e₂) = Function.extend f g₁ e₁ * Function.extend f g₂ e₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Function_extend", 3)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("Function_extend", (args[0], OVar("g_1"), OVar("e_1"),)), OOp("Function_extend", (args[0], OVar("g_2"), OVar("e_2"),))))
            results.append((rhs, "Mathlib: Function_extend_mul"))
        except Exception:
            pass
    return results


def _r0083_extend_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.extend_inv
    # Function.extend f g⁻¹ e⁻¹ = (Function.extend f g e)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Function_extend", 3)
    if args is not None:
        try:
            rhs = OVar("Function_extend_f_g_e_inv")
            results.append((rhs, "Mathlib: Function_extend_inv"))
        except Exception:
            pass
    return results


def _r0084_extend_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.extend_div
    # Function.extend f (g₁ / g₂) (e₁ / e₂) = Function.extend f g₁ e₁ / Function.extend f g₂ e₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Function_extend", 3)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("Function_extend", (args[0], OVar("g_1"), OVar("e_1"),)), OOp("Function_extend", (args[0], OVar("g_2"), OVar("e_2"),))))
            results.append((rhs, "Mathlib: Function_extend_div"))
        except Exception:
            pass
    return results


def _r0085_update_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.update_one
    # update (1 : ∀ i, f i) i 1 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "update", 3)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Function_update_one"))
        except Exception:
            pass
    return results


def _r0086_update_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.update_inv
    # update f₁⁻¹ i x₁⁻¹ = (update f₁ i x₁)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "update", 3)
    if args is not None:
        try:
            rhs = OVar("update_f_1_i_x_1_inv")
            results.append((rhs, "Mathlib: Function_update_inv"))
        except Exception:
            pass
    return results


def _r0087_update_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.update_div
    # update (f₁ / f₂) i (x₁ / x₂) = update f₁ i x₁ / update f₂ i x₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "update", 3)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("update", (OVar("f_1"), args[1], OVar("x_1"),)), OOp("update", (OVar("f_2"), args[1], OVar("x_2"),))))
            results.append((rhs, "Mathlib: Function_update_div"))
        except Exception:
            pass
    return results


def _r0088_const_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.const_eq_one
    # const ι a = 1 ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "const", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[1])), OLit(1)))
            results.append((rhs, "Mathlib: Function_const_eq_one"))
        except Exception:
            pass
    return results


def _r0089_mulSupport_fun_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.mulSupport_fun_inv
    # (mulSupport fun x => (f x)⁻¹) = mulSupport f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulSupport", 4)
    if args is not None:
        try:
            rhs = OOp("mulSupport", (OVar("f"),))
            results.append((rhs, "Mathlib: Function_mulSupport_fun_inv"))
        except Exception:
            pass
    return results


def _r0090_lieModule_lcs_map_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Surjective.lieModule_lcs_map_eq
    # (lowerCentralSeries R L M k : Submodule R M).map g = lowerCentralSeries R L₂ M₂ k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lowerCentralSeries_R_L_M_k_colon_Submodule_R_M_map", 1)
    if args is not None:
        try:
            rhs = OOp("lowerCentralSeries", (OVar("R"), OVar("L_2"), OVar("M_2"), OVar("k"),))
            results.append((rhs, "Mathlib: Function_Surjective_lieModule_lcs_map_eq"))
        except Exception:
            pass
    return results


def _r0091_support_const_smul_of_ne_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.support_const_smul_of_ne_zero
    # support (c • g) = support g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "support", 1)
    if args is not None:
        try:
            rhs = OOp("support", (OVar("g"),))
            results.append((rhs, "Mathlib: Function_support_const_smul_of_ne_zero"))
        except Exception:
            pass
    return results


def _r0092_support_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.support_smul
    # support (f • g) = support f ∩ support g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "support", 1)
    if args is not None:
        try:
            rhs = OOp("inter", (OOp("support", (OVar("f"),)), OOp("support", (OVar("g"),))))
            results.append((rhs, "Mathlib: Function_support_smul"))
        except Exception:
            pass
    return results


def _r0093_const_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.const_one
    # const α (1 : M) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "const", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Function_const_one"))
        except Exception:
            pass
    return results


def _r0094_const_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.const_mul
    # const ι a * const ι b = const ι (a * b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("const", (OVar("i"), OOp("*", (OVar("a"), OVar("b"))),))
            results.append((rhs, "Mathlib: Function_const_mul"))
        except Exception:
            pass
    return results


def _r0095_const_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.const_inv
    # (const ι a)⁻¹ = const ι a⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("const_i_a_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("const", (OVar("i"), OVar("ainv"),))
            results.append((rhs, "Mathlib: Function_const_inv"))
    except Exception:
        pass
    return results


def _r0096_const_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.const_div
    # const ι a / const ι b = const ι (a / b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("const", (OVar("i"), OOp("//", (OVar("a"), OVar("b"))),))
            results.append((rhs, "Mathlib: Function_const_div"))
        except Exception:
            pass
    return results


def _r0097_const_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.const_pow
    # const ι a ^ b = const ι (a ^ b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("const", (OVar("i"), OOp("**", (OVar("a"), args[1])),))
            results.append((rhs, "Mathlib: Function_const_pow"))
        except Exception:
            pass
    return results


def _r0098_mulSupport_eq_preimage(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.mulSupport_eq_preimage
    # mulSupport f = f ⁻¹' {1}ᶜ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulSupport", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("inv_prime"), OVar("_1"),))
            results.append((rhs, "Mathlib: Function_mulSupport_eq_preimage"))
        except Exception:
            pass
    return results


def _r0099_notMem_mulSupport(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.notMem_mulSupport
    # x ∉ mulSupport f ↔ f x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Function_notMem_mulSupport"))
        except Exception:
            pass
    return results


def _r0100_compl_mulSupport(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.compl_mulSupport
    # (mulSupport f)ᶜ = {x | f x = 1}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mulSupport_f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x_pipe_f_x_eq_1")
            results.append((rhs, "Mathlib: Function_compl_mulSupport"))
    except Exception:
        pass
    return results


def _r0101_mulSupport_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.mulSupport_eq_iff
    # mulSupport f = s ↔ (∀ x, x ∈ s → f x ≠ 1) ∧ ∀ x, x ∉ s → f x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Function_mulSupport_eq_iff"))
        except Exception:
            pass
    return results


def _r0102_ext_iff_mulSupport(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.ext_iff_mulSupport
    # f = g ↔ f.mulSupport = g.mulSupport ∧ ∀ x ∈ f.mulSupport, f x = g x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("g"), OVar("f_mulSupport"))), OOp("==", (OOp("and", (OVar("g_mulSupport"), OOp("in", (OOp("forall", (OVar("x"),)), OOp("f_mulSupport", (OVar("f"), OVar("x"),)))))), OOp("g", (OVar("x"),))))))
            results.append((rhs, "Mathlib: Function_ext_iff_mulSupport"))
    except Exception:
        pass
    return results


def _r0103_mulSupport_update_of_ne_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.mulSupport_update_of_ne_one
    # mulSupport (update f x y) = insert x (mulSupport f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulSupport", 1)
    if args is not None:
        try:
            rhs = OOp("insert", (OVar("x"), OOp("mulSupport", (OVar("f"),)),))
            results.append((rhs, "Mathlib: Function_mulSupport_update_of_ne_one"))
        except Exception:
            pass
    return results


def _r0104_mulSupport_update_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.mulSupport_update_one
    # mulSupport (update f x 1) = mulSupport f \\ {x}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulSupport", 1)
    if args is not None:
        try:
            rhs = OOp("mulSupport", (OVar("f"), OVar("bsl"), OVar("x"),))
            results.append((rhs, "Mathlib: Function_mulSupport_update_one"))
        except Exception:
            pass
    return results


def _r0105_mulSupport_update_eq_ite(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.mulSupport_update_eq_ite
    # mulSupport (update f x y) = if y = 1 then mulSupport f \\ {x} else insert x (mulSupport f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulSupport", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (OVar("y"),)), OOp("_1", (OVar("then"), OVar("mulSupport"), OVar("f"), OVar("bsl"), OVar("x"), OVar("else"), OVar("insert"), OVar("x"), OOp("mulSupport", (OVar("f"),)),))))
            results.append((rhs, "Mathlib: Function_mulSupport_update_eq_ite"))
        except Exception:
            pass
    return results


def _r0106_mulSupport_extend_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.mulSupport_extend_one
    # mulSupport (f.extend g 1) = f '' mulSupport g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulSupport", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("prime_prime"), OVar("mulSupport"), OVar("g"),))
            results.append((rhs, "Mathlib: Function_mulSupport_extend_one"))
        except Exception:
            pass
    return results


def _r0107_mulSupport_eq_empty_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.mulSupport_eq_empty_iff
    # mulSupport f = ∅ ↔ f = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulSupport", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("empty"), args[0])), OLit(1)))
            results.append((rhs, "Mathlib: Function_mulSupport_eq_empty_iff"))
        except Exception:
            pass
    return results


def _r0108_range_eq_image_or_of_mulSupport_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.range_eq_image_or_of_mulSupport_subset
    # range f = f '' k ∨ range f = insert 1 (f '' k)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OOp("f", (OVar("prime_prime"), OVar("k"),)), OOp("range", (args[0],)))), OOp("insert", (OLit(1), OOp("f", (OVar("prime_prime"), OVar("k"),)),))))
            results.append((rhs, "Mathlib: Function_range_eq_image_or_of_mulSupport_subset"))
        except Exception:
            pass
    return results


def _r0109_mulSupport_eq_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.mulSupport_eq_univ
    # mulSupport f = Set.univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulSupport", 1)
    if args is not None:
        try:
            rhs = OVar("Set_univ")
            results.append((rhs, "Mathlib: Function_mulSupport_eq_univ"))
        except Exception:
            pass
    return results


def _r0110_mulSupport_comp_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.mulSupport_comp_eq
    # mulSupport (g ∘ f) = mulSupport f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulSupport", 1)
    if args is not None:
        try:
            rhs = OOp("mulSupport", (OVar("f"),))
            results.append((rhs, "Mathlib: Function_mulSupport_comp_eq"))
        except Exception:
            pass
    return results


def _r0111_mulSupport_comp_eq_of_range_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.mulSupport_comp_eq_of_range_subset
    # mulSupport (g ∘ f) = mulSupport f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulSupport", 1)
    if args is not None:
        try:
            rhs = OOp("mulSupport", (OVar("f"),))
            results.append((rhs, "Mathlib: Function_mulSupport_comp_eq_of_range_subset"))
        except Exception:
            pass
    return results


def _r0112_mulSupport_comp_eq_preimage(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.mulSupport_comp_eq_preimage
    # mulSupport (g ∘ f) = f ⁻¹' mulSupport g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulSupport", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("inv_prime"), OVar("mulSupport"), OVar("g"),))
            results.append((rhs, "Mathlib: Function_mulSupport_comp_eq_preimage"))
        except Exception:
            pass
    return results


def _r0113_mulSupport_prodMk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.mulSupport_prodMk
    # mulSupport (fun x ↦ (f x, g x)) = mulSupport f ∪ mulSupport g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulSupport", 1)
    if args is not None:
        try:
            rhs = OOp("union", (OOp("mulSupport", (OVar("f"),)), OOp("mulSupport", (OVar("g"),))))
            results.append((rhs, "Mathlib: Function_mulSupport_prodMk"))
        except Exception:
            pass
    return results


def _r0114_mulSupport_curry(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.mulSupport_curry
    # (mulSupport f.curry) = (mulSupport f).image Prod.fst
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulSupport", 1)
    if args is not None:
        try:
            rhs = OOp("mulSupport_f_image", (OVar("Prod_fst"),))
            results.append((rhs, "Mathlib: Function_mulSupport_curry"))
        except Exception:
            pass
    return results


def _r0115_mulSupport_fun_curry(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.mulSupport_fun_curry
    # mulSupport (fun i j ↦ f (i, j)) = (mulSupport f).image Prod.fst
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulSupport", 1)
    if args is not None:
        try:
            rhs = OOp("mulSupport_f_image", (OVar("Prod_fst"),))
            results.append((rhs, "Mathlib: Function_mulSupport_fun_curry"))
        except Exception:
            pass
    return results


def _r0116_iterate_two_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Involutive.iterate_two_mul
    # f^[2 * n] = id
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("fpow_2_star_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Function_Involutive_iterate_two_mul"))
    except Exception:
        pass
    return results


def _r0117_iterate_two_mul_add_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Involutive.iterate_two_mul_add_one
    # f^[2 * n + 1] = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("fpow_2_star_n_plus_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Function_Involutive_iterate_two_mul_add_one"))
    except Exception:
        pass
    return results


def _r0118_iterate_even(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Involutive.iterate_even
    # f^[n] = id
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("fpow_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Function_Involutive_iterate_even"))
    except Exception:
        pass
    return results


def _r0119_iterate_odd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Involutive.iterate_odd
    # f^[n] = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("fpow_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Function_Involutive_iterate_odd"))
    except Exception:
        pass
    return results


def _r0120_iterate_eq_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Involutive.iterate_eq_self
    # f^[n] = f ↔ Odd n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("fpow_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("f"), OOp("Odd", (OVar("n"),))))
            results.append((rhs, "Mathlib: Function_Involutive_iterate_eq_self"))
    except Exception:
        pass
    return results


def _r0121_iterate_eq_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Involutive.iterate_eq_id
    # f^[n] = id ↔ Even n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("fpow_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("id"), OOp("Even", (OVar("n"),))))
            results.append((rhs, "Mathlib: Function_Involutive_iterate_eq_id"))
    except Exception:
        pass
    return results


def _r0122_sub_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.sub_eq
    # f (x - c) = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("x"),))
            results.append((rhs, "Mathlib: Function_Periodic_sub_eq"))
        except Exception:
            pass
    return results


def _r0123_sub_nsmul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.sub_nsmul_eq
    # f (x - n • c) = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("x"),))
            results.append((rhs, "Mathlib: Function_Periodic_sub_nsmul_eq"))
        except Exception:
            pass
    return results


def _r0124_sub_nat_mul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.sub_nat_mul_eq
    # f (x - n * c) = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("x"),))
            results.append((rhs, "Mathlib: Function_Periodic_sub_nat_mul_eq"))
        except Exception:
            pass
    return results


def _r0125_nsmul_sub_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.nsmul_sub_eq
    # f (n • c - x) = f (-x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("minus_x"),))
            results.append((rhs, "Mathlib: Function_Periodic_nsmul_sub_eq"))
        except Exception:
            pass
    return results


def _r0126_nat_mul_sub_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.nat_mul_sub_eq
    # f (n * c - x) = f (-x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("minus_x"),))
            results.append((rhs, "Mathlib: Function_Periodic_nat_mul_sub_eq"))
        except Exception:
            pass
    return results


def _r0127_sub_zsmul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.sub_zsmul_eq
    # f (x - n • c) = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("x"),))
            results.append((rhs, "Mathlib: Function_Periodic_sub_zsmul_eq"))
        except Exception:
            pass
    return results


def _r0128_sub_int_mul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.sub_int_mul_eq
    # f (x - n * c) = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("x"),))
            results.append((rhs, "Mathlib: Function_Periodic_sub_int_mul_eq"))
        except Exception:
            pass
    return results


def _r0129_zsmul_sub_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.zsmul_sub_eq
    # f (n • c - x) = f (-x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("minus_x"),))
            results.append((rhs, "Mathlib: Function_Periodic_zsmul_sub_eq"))
        except Exception:
            pass
    return results


def _r0130_int_mul_sub_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.int_mul_sub_eq
    # f (n * c - x) = f (-x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("minus_x"),))
            results.append((rhs, "Mathlib: Function_Periodic_int_mul_sub_eq"))
        except Exception:
            pass
    return results


def _r0131_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.eq
    # f c = f 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OLit(0),))
            results.append((rhs, "Mathlib: Function_Periodic_eq"))
        except Exception:
            pass
    return results


def _r0132_neg_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.neg_eq
    # f (-c) = f 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OLit(0),))
            results.append((rhs, "Mathlib: Function_Periodic_neg_eq"))
        except Exception:
            pass
    return results


def _r0133_nsmul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.nsmul_eq
    # f (n • c) = f 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OLit(0),))
            results.append((rhs, "Mathlib: Function_Periodic_nsmul_eq"))
        except Exception:
            pass
    return results


def _r0134_nat_mul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.nat_mul_eq
    # f (n * c) = f 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OLit(0),))
            results.append((rhs, "Mathlib: Function_Periodic_nat_mul_eq"))
        except Exception:
            pass
    return results


def _r0135_zsmul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.zsmul_eq
    # f (n • c) = f 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OLit(0),))
            results.append((rhs, "Mathlib: Function_Periodic_zsmul_eq"))
        except Exception:
            pass
    return results


def _r0136_int_mul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.int_mul_eq
    # f (n * c) = f 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OLit(0),))
            results.append((rhs, "Mathlib: Function_Periodic_int_mul_eq"))
        except Exception:
            pass
    return results


def _r0137_map_vadd_zmultiples(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.map_vadd_zmultiples
    # f (a +ᵥ x) = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("x"),))
            results.append((rhs, "Mathlib: Function_Periodic_map_vadd_zmultiples"))
        except Exception:
            pass
    return results


def _r0138_map_vadd_multiples(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.map_vadd_multiples
    # f (a +ᵥ x) = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("x"),))
            results.append((rhs, "Mathlib: Function_Periodic_map_vadd_multiples"))
        except Exception:
            pass
    return results


def _r0139_lift_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.lift_coe
    # h.lift (a : α ⧸ AddSubgroup.zmultiples c) = f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_lift", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("a"),))
            results.append((rhs, "Mathlib: Function_Periodic_lift_coe"))
        except Exception:
            pass
    return results


def _r0140_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Antiperiodic.eq
    # f c = -f 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("minus_f", (OLit(0),))
            results.append((rhs, "Mathlib: Function_Antiperiodic_eq"))
        except Exception:
            pass
    return results


def _r0141_sub_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Antiperiodic.sub_eq
    # f (x - c) = -f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("minus_f", (OVar("x"),))
            results.append((rhs, "Mathlib: Function_Antiperiodic_sub_eq"))
        except Exception:
            pass
    return results


def _r0142_neg_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Antiperiodic.neg_eq
    # f (-c) = -f 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("minus_f", (OLit(0),))
            results.append((rhs, "Mathlib: Function_Antiperiodic_neg_eq"))
        except Exception:
            pass
    return results


def _r0143_nat_mul_eq_of_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Antiperiodic.nat_mul_eq_of_eq_zero
    # ∀ n : ℕ, f (n * c) = 0   | 0 =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("_0", (OVar("pipe"), OLit(0), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: Function_Antiperiodic_nat_mul_eq_of_eq_zero"))
        except Exception:
            pass
    return results


def _r0144_int_mul_eq_of_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Antiperiodic.int_mul_eq_of_eq_zero
    # ∀ n : ℤ, f (n * c) = 0   | (n : ℕ) =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("_0", (OVar("pipe"), OOp("n", (OVar("colon"), OVar("_unknown"),)), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: Function_Antiperiodic_int_mul_eq_of_eq_zero"))
        except Exception:
            pass
    return results


def _r0145_add_zsmul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Antiperiodic.add_zsmul_eq
    # f (x + n • c) = (n.negOnePow : ℤ) • f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("n_negOnePow_colon", (OVar("_unknown"), OVar("f"), OVar("x"),))
            results.append((rhs, "Mathlib: Function_Antiperiodic_add_zsmul_eq"))
        except Exception:
            pass
    return results


def _r0146_sub_zsmul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Antiperiodic.sub_zsmul_eq
    # f (x - n • c) = (n.negOnePow : ℤ) • f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("n_negOnePow_colon", (OVar("_unknown"), OVar("f"), OVar("x"),))
            results.append((rhs, "Mathlib: Function_Antiperiodic_sub_zsmul_eq"))
        except Exception:
            pass
    return results


def _r0147_zsmul_sub_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Antiperiodic.zsmul_sub_eq
    # f (n • c - x) = (n.negOnePow : ℤ) • f (-x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("n_negOnePow_colon", (OVar("_unknown"), OVar("f"), OVar("minus_x"),))
            results.append((rhs, "Mathlib: Function_Antiperiodic_zsmul_sub_eq"))
        except Exception:
            pass
    return results


def _r0148_add_int_mul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Antiperiodic.add_int_mul_eq
    # f (x + n * c) = (n.negOnePow : ℤ) * f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("n_negOnePow", (OVar("colon"), OVar("_unknown"),)), OOp("f", (OVar("x"),))))
            results.append((rhs, "Mathlib: Function_Antiperiodic_add_int_mul_eq"))
        except Exception:
            pass
    return results


def _r0149_sub_int_mul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Antiperiodic.sub_int_mul_eq
    # f (x - n * c) = (n.negOnePow : ℤ) * f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("n_negOnePow", (OVar("colon"), OVar("_unknown"),)), OOp("f", (OVar("x"),))))
            results.append((rhs, "Mathlib: Function_Antiperiodic_sub_int_mul_eq"))
        except Exception:
            pass
    return results


def _r0150_int_mul_sub_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Antiperiodic.int_mul_sub_eq
    # f (n * c - x) = (n.negOnePow : ℤ) * f (-x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("n_negOnePow", (OVar("colon"), OVar("_unknown"),)), OOp("f", (OVar("minus_x"),))))
            results.append((rhs, "Mathlib: Function_Antiperiodic_int_mul_sub_eq"))
        except Exception:
            pass
    return results


def _r0151_add_nsmul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Antiperiodic.add_nsmul_eq
    # f (x + n • c) = (-1) ^ n • f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("minus_1"), OOp("n", (OVar("_unknown"), OVar("f"), OVar("x"),))))
            results.append((rhs, "Mathlib: Function_Antiperiodic_add_nsmul_eq"))
        except Exception:
            pass
    return results


def _r0152_sub_nsmul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Antiperiodic.sub_nsmul_eq
    # f (x - n • c) = (-1) ^ n • f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("minus_1"), OOp("n", (OVar("_unknown"), OVar("f"), OVar("x"),))))
            results.append((rhs, "Mathlib: Function_Antiperiodic_sub_nsmul_eq"))
        except Exception:
            pass
    return results


def _r0153_nsmul_sub_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Antiperiodic.nsmul_sub_eq
    # f (n • c - x) = (-1) ^ n • f (-x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("minus_1"), OOp("n", (OVar("_unknown"), OVar("f"), OVar("minus_x"),))))
            results.append((rhs, "Mathlib: Function_Antiperiodic_nsmul_sub_eq"))
        except Exception:
            pass
    return results


def _r0154_add_antiperiod_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.add_antiperiod_eq
    # f (c₁ + c₂) = -f 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("minus_f", (OLit(0),))
            results.append((rhs, "Mathlib: Function_Periodic_add_antiperiod_eq"))
        except Exception:
            pass
    return results


def _r0155_sub_antiperiod_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.sub_antiperiod_eq
    # f (c₁ - c₂) = -f 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("minus_f", (OLit(0),))
            results.append((rhs, "Mathlib: Function_Periodic_sub_antiperiod_eq"))
        except Exception:
            pass
    return results


def _r0156_update_star(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.update_star
    # Function.update (star h) i (star a) = star (Function.update h i a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Function_update", 3)
    if args is not None:
        try:
            rhs = OOp("star", (OOp("Function_update", (OVar("h"), args[1], OVar("a"),)),))
            results.append((rhs, "Mathlib: Function_update_star"))
        except Exception:
            pass
    return results


def _r0157_star_sumElim(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.star_sumElim
    # star (Sum.elim x y) = Sum.elim (star x) (star y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "star", 1)
    if args is not None:
        try:
            rhs = OOp("Sum_elim", (OOp("star", (OVar("x"),)), OOp("star", (OVar("y"),)),))
            results.append((rhs, "Mathlib: Function_star_sumElim"))
        except Exception:
            pass
    return results


def _r0158_norm_qParam(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.norm_qParam
    # ‖𝕢 h z‖ = Real.exp (-2 * π * im z / h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 2)
    if args is not None:
        try:
            rhs = OOp("Real_exp", (OOp("*", (OVar("minus_2"), OOp("*", (OVar("pi"), OOp("//", (OOp("im", (args[1],)), args[0])))))),))
            results.append((rhs, "Mathlib: Function_Periodic_norm_qParam"))
        except Exception:
            pass
    return results


def _r0159_im_invQParam(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.im_invQParam
    # im (invQParam h q) = -h / (2 * π) * Real.log ‖q‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "im", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("//", (OVar("minus_h"), OOp("*", (OLit(2), OVar("pi"))))), OOp("Real_log", (OVar("q"),))))
            results.append((rhs, "Mathlib: Function_Periodic_im_invQParam"))
        except Exception:
            pass
    return results


def _r0160_qParam_right_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.qParam_right_inv
    # 𝕢 h (invQParam h q) = q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 2)
    if args is not None:
        try:
            rhs = OVar("q")
            results.append((rhs, "Mathlib: Function_Periodic_qParam_right_inv"))
        except Exception:
            pass
    return results


def _r0161_qParam_left_inv_mod_period(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.qParam_left_inv_mod_period
    # ∃ m : ℤ, invQParam h (𝕢 h z) = z + m * h
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 6)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("z"), OOp("*", (args[0], args[4]))))
            results.append((rhs, "Mathlib: Function_Periodic_qParam_left_inv_mod_period"))
        except Exception:
            pass
    return results


def _r0162_zero_iff_logCounting_bounded(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.locallyFinsuppWithin.zero_iff_logCounting_bounded
    # D = 0 ↔ logCounting D =O[atTop] (1 : ℝ → ℝ)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("D")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OLit(0), OOp("logCounting", (OVar("D"), OVar("eq_O_atTop"), OOp("implies", (OOp("_1", (OVar("colon"), OVar("_unknown"),)), OVar("_unknown"))),))))
            results.append((rhs, "Mathlib: Function_locallyFinsuppWithin_zero_iff_logCounting_bounded"))
    except Exception:
        pass
    return results


def _r0163_toClosedBall_eval_within(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.locallyFinsuppWithin.toClosedBall_eval_within
    # toClosedBall r f z = f z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toClosedBall", 3)
    if args is not None:
        try:
            rhs = OOp("f", (args[2],))
            results.append((rhs, "Mathlib: Function_locallyFinsuppWithin_toClosedBall_eval_within"))
        except Exception:
            pass
    return results


def _r0164_toClosedBall_divisor(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.locallyFinsuppWithin.toClosedBall_divisor
    # (divisor f (closedBall 0 |r|)) = (locallyFinsuppWithin.toClosedBall r) (divisor f univ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "divisor", 2)
    if args is not None:
        try:
            rhs = OOp("locallyFinsuppWithin_toClosedBall_r", (OOp("divisor", (args[0], OVar("univ"),)),))
            results.append((rhs, "Mathlib: Function_locallyFinsuppWithin_toClosedBall_divisor"))
        except Exception:
            pass
    return results


def _r0165_logCounting_eval_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.locallyFinsuppWithin.logCounting_eval_zero
    # logCounting D 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logCounting", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Function_locallyFinsuppWithin_logCounting_eval_zero"))
        except Exception:
            pass
    return results


def _r0166_logCounting_single_eq_log_sub_const(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.locallyFinsuppWithin.logCounting_single_eq_log_sub_const
    # logCounting (single e n) r = n * (log r - log ‖e‖)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logCounting", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("n"), OOp("-", (OOp("log", (args[1],)), OOp("log", (OVar("e"),))))))
            results.append((rhs, "Mathlib: Function_locallyFinsuppWithin_logCounting_single_eq_log_sub_const"))
        except Exception:
            pass
    return results


def _r0167_logCounting_divisor_eq_circleAverage_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const
    # logCounting (divisor f ⊤) R =       circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logCounting", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("circleAverage", (OOp("log", (OVar("f"), OVar("_unknown"),)), OLit(0), args[1],)), OOp("log", (OVar("meromorphicTrailingCoeffAt"), OVar("f"), OVar("_0"),))))
            results.append((rhs, "Mathlib: Function_locallyFinsuppWithin_logCounting_divisor_eq_circleAverage_sub_const"))
        except Exception:
            pass
    return results


def _r0168_hasTemperateGrowth_iff_isBigO(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.hasTemperateGrowth_iff_isBigO
    # f.HasTemperateGrowth ↔ ContDiff ℝ ∞ f ∧       ∀ n, ∃ k, iteratedFDeriv ℝ n f =O[⊤] (fun x ↦ (1 + ‖x‖) ^ k)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("O_top", (OOp("**", (OOp("fun", (OVar("x"), OVar("_unknown"), OOp("+", (OLit(1), OVar("x"))),)), OVar("k"))),))
            results.append((rhs, "Mathlib: Function_hasTemperateGrowth_iff_isBigO"))
        except Exception:
            pass
    return results


def _r0169_isBigO(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.HasTemperateGrowth.isBigO
    # ∃ k, iteratedFDeriv ℝ n f =O[⊤] (fun x ↦ (1 + ‖x‖) ^ k)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 5)
    if args is not None:
        try:
            rhs = OOp("O_top", (OOp("**", (OOp("fun", (OVar("x"), args[2], OOp("+", (OLit(1), OVar("x"))),)), args[0])),))
            results.append((rhs, "Mathlib: Function_HasTemperateGrowth_isBigO"))
        except Exception:
            pass
    return results


def _r0170_isBigO_uniform(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.HasTemperateGrowth.isBigO_uniform
    # ∃ k, ∀ n ≤ N, iteratedFDeriv ℝ n f =O[⊤] (fun x ↦ (1 + ‖x‖) ^ k)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("O_top", (OOp("**", (OOp("fun", (OVar("x"), OVar("_unknown"), OOp("+", (OLit(1), OVar("x"))),)), OVar("k"))),))
            results.append((rhs, "Mathlib: Function_HasTemperateGrowth_isBigO_uniform"))
        except Exception:
            pass
    return results


def _r0171_toTemperedDistribution_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.HasTemperateGrowth.toTemperedDistribution_apply
    # toTemperedDistribution μ hf g = ∫ (x : E), g x • f x ∂μ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toTemperedDistribution", 3)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("x_colon_E"), args[2], OVar("x"), OVar("_unknown"), OVar("f"), OVar("x"), args[0],))
            results.append((rhs, "Mathlib: Function_HasTemperateGrowth_toTemperedDistribution_apply"))
        except Exception:
            pass
    return results


def _r0172_mulSupport(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.FactorizedRational.mulSupport
    # (fun u ↦ (· - u) ^ d u).mulSupport = d.support
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("fun_u_minus_u_pow_d_u_mulSupport")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("d_support")
            results.append((rhs, "Mathlib: Function_FactorizedRational_mulSupport"))
    except Exception:
        pass
    return results


def _r0173_finprod_eq_fun(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.FactorizedRational.finprod_eq_fun
    # (∏ᶠ u, (· - u) ^ d u) = fun x ↦ ∏ᶠ u, (x - u) ^ d u
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("fun", (OVar("x"), OVar("_unknown"), OVar("_unknown"), OVar("u"), OOp("-", (OVar("x"), OVar("u"))),)), OOp("d", (OVar("u"),))))
            results.append((rhs, "Mathlib: Function_FactorizedRational_finprod_eq_fun"))
        except Exception:
            pass
    return results


def _r0174_extractFactor(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.FactorizedRational.extractFactor
    # (∏ᶠ u, (· - u) ^ d u) = ((· - u₀) ^ d u₀) * (∏ᶠ u, (· - u) ^ (update d u₀ 0 u))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OOp("-", (OVar("_unknown"), OVar("u_0"))), OOp("d", (OVar("u_0"),)))), OOp("**", (OOp("_unknown", (OVar("u"), OOp("-", (OVar("_unknown"), OVar("u"))),)), OOp("update", (OVar("d"), OVar("u_0"), OLit(0), OVar("u"),))))))
            results.append((rhs, "Mathlib: Function_FactorizedRational_extractFactor"))
        except Exception:
            pass
    return results


def _r0175_meromorphicOrderAt_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.FactorizedRational.meromorphicOrderAt_eq
    # meromorphicOrderAt (∏ᶠ u, (· - u) ^ d u) z = d z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "meromorphicOrderAt", 2)
    if args is not None:
        try:
            rhs = OOp("d", (args[1],))
            results.append((rhs, "Mathlib: Function_FactorizedRational_meromorphicOrderAt_eq"))
        except Exception:
            pass
    return results


def _r0176_divisor(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.FactorizedRational.divisor
    # MeromorphicOn.divisor (∏ᶠ u, (· - u) ^ D u) U = D
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "MeromorphicOn_divisor", 2)
    if args is not None:
        try:
            rhs = OVar("D")
            results.append((rhs, "Mathlib: Function_FactorizedRational_divisor"))
        except Exception:
            pass
    return results


def _r0177_meromorphicTrailingCoeffAt_factorizedRat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.FactorizedRational.meromorphicTrailingCoeffAt_factorizedRational
    # meromorphicTrailingCoeffAt (∏ᶠ u, (· - u) ^ d u) x = ∏ᶠ u, (x - u) ^ update d x 0 u
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "meromorphicTrailingCoeffAt", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("_unknown", (OVar("u"), OOp("-", (args[1], OVar("u"))),)), OOp("update", (OVar("d"), args[1], OLit(0), OVar("u"),))))
            results.append((rhs, "Mathlib: Function_FactorizedRational_meromorphicTrailingCoeffAt_factorizedRational"))
        except Exception:
            pass
    return results


def _r0178_meromorphicTrailingCoeffAt_factorizedRat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.FactorizedRational.meromorphicTrailingCoeffAt_factorizedRational_off_support
    # meromorphicTrailingCoeffAt (∏ᶠ u, (· - u) ^ d u) x = ∏ᶠ u, (x - u) ^ d u
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "meromorphicTrailingCoeffAt", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("_unknown", (OVar("u"), OOp("-", (args[1], OVar("u"))),)), OOp("d", (OVar("u"),))))
            results.append((rhs, "Mathlib: Function_FactorizedRational_meromorphicTrailingCoeffAt_factorizedRational_off_support"))
        except Exception:
            pass
    return results


def _r0179_log_norm_meromorphicTrailingCoeffAt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.FactorizedRational.log_norm_meromorphicTrailingCoeffAt
    # log ‖meromorphicTrailingCoeffAt (∏ᶠ u, (· - u) ^ d u) x‖ = ∑ᶠ u, (d u) * log ‖x - u‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 3)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("_unknown", (OVar("u"), OOp("d", (OVar("u"),)),)), OOp("-", (OOp("log", (args[2],)), OVar("u")))))
            results.append((rhs, "Mathlib: Function_FactorizedRational_log_norm_meromorphicTrailingCoeffAt"))
        except Exception:
            pass
    return results


def _r0180_update_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.update_exp
    # Function.update (exp x) j (exp xj) = exp (Function.update x j xj)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Function_update", 3)
    if args is not None:
        try:
            rhs = OOp("exp", (OOp("Function_update", (OVar("x"), args[1], OVar("xj"),)),))
            results.append((rhs, "Mathlib: Function_update_exp"))
        except Exception:
            pass
    return results


def _r0181_iso_hom_naturality(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: InjectiveResolution.iso_hom_naturality
    # (injectiveResolutions C).map f ≫ J.iso.hom =       I.iso.hom ≫ (HomotopyCategory.quotient _ _).map φ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "injectiveResolutions_C_map", 3)
    if args is not None:
        try:
            rhs = OOp("I_iso_hom", (args[1], OVar("HomotopyCategory_quotient_map"), OVar("phi"),))
            results.append((rhs, "Mathlib: InjectiveResolution_iso_hom_naturality"))
        except Exception:
            pass
    return results


def _r0182_iso_inv_naturality(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: InjectiveResolution.iso_inv_naturality
    # I.iso.inv ≫ (injectiveResolutions C).map f =       (HomotopyCategory.quotient _ _).map φ ≫ J.iso.inv
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "I_iso_inv", 3)
    if args is not None:
        try:
            rhs = OOp("HomotopyCategory_quotient_map", (OVar("phi"), args[0], OVar("J_iso_inv"),))
            results.append((rhs, "Mathlib: InjectiveResolution_iso_inv_naturality"))
        except Exception:
            pass
    return results


def _r0183_ofCocomplex_d_0_1(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: InjectiveResolution.ofCocomplex_d_0_1
    # (ofCocomplex Z).d 0 1 = d (Injective.ι Z)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofCocomplex_Z_d", 2)
    if args is not None:
        try:
            rhs = OOp("d", (OOp("Injective_i", (OVar("Z"),)),))
            results.append((rhs, "Mathlib: InjectiveResolution_ofCocomplex_d_0_1"))
        except Exception:
            pass
    return results


def _r0184_comp_factorThru(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Injective.comp_factorThru
    # f ≫ factorThru g f = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 4)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: Injective_comp_factorThru"))
        except Exception:
            pass
    return results


def _r0185_i_f_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: InjectiveResolution.ι_f_succ
    # I.ι.f (n + 1) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "I_i_f", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: InjectiveResolution_i_f_succ"))
        except Exception:
            pass
    return results


def _r0186_i_f_zero_comp_complex_d(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: InjectiveResolution.ι_f_zero_comp_complex_d
    # I.ι.f 0 ≫ I.cocomplex.d 0 1 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "I_i_f", 5)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: InjectiveResolution_i_f_zero_comp_complex_d"))
        except Exception:
            pass
    return results


def _r0187_complex_d_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: InjectiveResolution.complex_d_comp
    # I.cocomplex.d n (n + 1) ≫ I.cocomplex.d (n + 1) (n + 2) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "I_cocomplex_d", 6)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: InjectiveResolution_complex_d_comp"))
        except Exception:
            pass
    return results


def _r0188_i_comp_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: InjectiveResolution.Hom.ι_comp_hom
    # I.ι ≫ φ.hom = (single₀ C).map f ≫ I'.ι
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "I_i", 2)
    if args is not None:
        try:
            rhs = OOp("single_0_C_map", (OVar("f"), args[0], OVar("I_prime_i"),))
            results.append((rhs, "Mathlib: InjectiveResolution_Hom_i_comp_hom"))
        except Exception:
            pass
    return results


def _r0189_uncurry_apply_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.FromTypes.uncurry_apply_cons
    # uncurry f (Fin.cons a args) = @uncurry _ p _ (f a) args
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "uncurry", 2)
    if args is not None:
        try:
            rhs = OOp("at_uncurry", (OVar("_unknown"), OVar("p"), OVar("_unknown"), OOp("f", (OVar("a"),)), OVar("args"),))
            results.append((rhs, "Mathlib: Function_FromTypes_uncurry_apply_cons"))
        except Exception:
            pass
    return results


def _r0190_uncurry_apply_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.FromTypes.uncurry_apply_succ
    # uncurry f args = uncurry (f (args 0)) (Fin.tail args)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "uncurry", 2)
    if args is not None:
        try:
            rhs = OOp("uncurry", (OOp("f", (OOp("args", (OLit(0),)),)), OOp("Fin_tail", (args[1],)),))
            results.append((rhs, "Mathlib: Function_FromTypes_uncurry_apply_succ"))
        except Exception:
            pass
    return results


def _r0191_curry_apply_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.FromTypes.curry_apply_cons
    # curry f a = @curry _ p _ (f ∘' Fin.cons a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "curry", 2)
    if args is not None:
        try:
            rhs = OOp("at_curry", (OVar("_unknown"), OVar("p"), OVar("_unknown"), OOp("f", (OVar("comp_prime"), OVar("Fin_cons"), args[1],)),))
            results.append((rhs, "Mathlib: Function_FromTypes_curry_apply_cons"))
        except Exception:
            pass
    return results


def _r0192_curry_apply_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.FromTypes.curry_apply_succ
    # curry f a = curry (f ∘ Fin.cons a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "curry", 2)
    if args is not None:
        try:
            rhs = OOp("curry", (OOp("comp", (args[0], OOp("Fin_cons", (args[1],)))),))
            results.append((rhs, "Mathlib: Function_FromTypes_curry_apply_succ"))
        except Exception:
            pass
    return results


def _r0193_curry_uncurry(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.FromTypes.curry_uncurry
    # curry (uncurry f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "curry", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Function_FromTypes_curry_uncurry"))
        except Exception:
            pass
    return results


def _r0194_uncurry_curry(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.FromTypes.uncurry_curry
    # uncurry (curry f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "uncurry", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Function_FromTypes_uncurry_curry"))
        except Exception:
            pass
    return results


def _r0195_curry_two_eq_curry(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.FromTypes.curry_two_eq_curry
    # curry f = Function.curry (f ∘ (piFinTwoEquiv p).symm)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "curry", 1)
    if args is not None:
        try:
            rhs = OOp("Function_curry", (OOp("comp", (args[0], OVar("piFinTwoEquiv_p_symm"))),))
            results.append((rhs, "Mathlib: Function_FromTypes_curry_two_eq_curry"))
        except Exception:
            pass
    return results


def _r0196_uncurry_two_eq_uncurry(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.FromTypes.uncurry_two_eq_uncurry
    # uncurry f = Function.uncurry f ∘ piFinTwoEquiv p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "uncurry", 1)
    if args is not None:
        try:
            rhs = OOp("comp", (OOp("Function_uncurry", (args[0],)), OOp("piFinTwoEquiv", (OVar("p"),))))
            results.append((rhs, "Mathlib: Function_FromTypes_uncurry_two_eq_uncurry"))
        except Exception:
            pass
    return results


def _r0197_curry_uncurry(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.OfArity.curry_uncurry
    # curry (uncurry f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "curry", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Function_OfArity_curry_uncurry"))
        except Exception:
            pass
    return results


def _r0198_uncurry_two_eq_uncurry(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.OfArity.uncurry_two_eq_uncurry
    # uncurry f = Function.uncurry f ∘ (finTwoArrowEquiv α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "uncurry", 1)
    if args is not None:
        try:
            rhs = OOp("comp", (OOp("Function_uncurry", (args[0],)), OOp("finTwoArrowEquiv", (OVar("a"),))))
            results.append((rhs, "Mathlib: Function_OfArity_uncurry_two_eq_uncurry"))
        except Exception:
            pass
    return results


def _r0199_embFinTwo_apply_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.embFinTwo_apply_zero
    # embFinTwo h 0 = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "embFinTwo", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Function_Embedding_embFinTwo_apply_zero"))
        except Exception:
            pass
    return results


def _r0200_embFinTwo_apply_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.embFinTwo_apply_one
    # embFinTwo h 1 = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "embFinTwo", 2)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: Function_Embedding_embFinTwo_apply_one"))
        except Exception:
            pass
    return results


def _r0201_updateFinset_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.updateFinset_def
    # updateFinset x s y = fun i ↦ if hi : i ∈ s then y ⟨i, hi⟩ else x i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "updateFinset", 3)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("fun", (OVar("i"), OVar("_unknown"), OVar("if"), OVar("hi"), OVar("colon"), OVar("i"),)), OOp("s", (OVar("then"), args[2], OVar("i_hi"), OVar("else"), args[0], OVar("i"),))))
            results.append((rhs, "Mathlib: Function_updateFinset_def"))
        except Exception:
            pass
    return results


def _r0202_updateFinset_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.updateFinset_empty
    # updateFinset x ∅ y = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "updateFinset", 3)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Function_updateFinset_empty"))
        except Exception:
            pass
    return results


def _r0203_update_eq_updateFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.update_eq_updateFinset
    # Function.update x i y = updateFinset x {i} (uniqueElim y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Function_update", 3)
    if args is not None:
        try:
            rhs = OOp("updateFinset", (args[0], args[1], OOp("uniqueElim", (args[2],)),))
            results.append((rhs, "Mathlib: Function_update_eq_updateFinset"))
        except Exception:
            pass
    return results


def _r0204_updateFinset_updateFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.updateFinset_updateFinset
    # updateFinset (updateFinset x s y) t z =     updateFinset x (s ∪ t) (Equiv.piFinsetUnion π hst ⟨y, z⟩)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "updateFinset", 3)
    if args is not None:
        try:
            rhs = OOp("updateFinset", (OVar("x"), OOp("union", (OVar("s"), args[1])), OOp("Equiv_piFinsetUnion", (OVar("pi"), OVar("hst"), OVar("y_z"),)),))
            results.append((rhs, "Mathlib: Function_updateFinset_updateFinset"))
        except Exception:
            pass
    return results


def _r0205_updateFinset_updateFinset_of_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.updateFinset_updateFinset_of_subset
    # updateFinset (updateFinset x s y) t z = updateFinset x t z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "updateFinset", 3)
    if args is not None:
        try:
            rhs = OOp("updateFinset", (OVar("x"), args[1], args[2],))
            results.append((rhs, "Mathlib: Function_updateFinset_updateFinset_of_subset"))
        except Exception:
            pass
    return results


def _r0206_restrict_updateFinset_of_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.restrict_updateFinset_of_subset
    # s.restrict (updateFinset x t y) = restrict₂ hst y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_restrict", 1)
    if args is not None:
        try:
            rhs = OOp("restrict_2", (OVar("hst"), OVar("y"),))
            results.append((rhs, "Mathlib: Function_restrict_updateFinset_of_subset"))
        except Exception:
            pass
    return results


def _r0207_restrict_updateFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.restrict_updateFinset
    # s.restrict (updateFinset x s y) = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_restrict", 1)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: Function_restrict_updateFinset"))
        except Exception:
            pass
    return results


def _r0208_updateFinset_restrict(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.updateFinset_restrict
    # updateFinset x s (s.restrict x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "updateFinset", 3)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Function_updateFinset_restrict"))
        except Exception:
            pass
    return results


def _r0209_update_updateFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.update_updateFinset
    # Function.update (updateFinset x s y) i z = updateFinset x (s ∪ {i})       ((Equiv.piFinsetUnion π <| Finset.disjoint_sin
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Function_update", 3)
    if args is not None:
        try:
            rhs = OOp("updateFinset", (OVar("x"), OOp("union", (OVar("s"), args[1])), OOp("Equiv_piFinsetUnion_pi_lt_pipe_Finset_disjoint_singleton_right_mpr_hi", (OOp("y", (OVar("uniqueElim"), args[2],)),)),))
            results.append((rhs, "Mathlib: Function_update_updateFinset"))
        except Exception:
            pass
    return results


def _r0210_updateFinset_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.updateFinset_congr
    # updateFinset x s y = updateFinset x t (fun i ↦ y ⟨i, h ▸ i.prop⟩)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "updateFinset", 3)
    if args is not None:
        try:
            rhs = OOp("updateFinset", (args[0], OVar("t"), OOp("fun", (OVar("i"), OVar("_unknown"), args[2], OVar("i_h_i_prop"),)),))
            results.append((rhs, "Mathlib: Function_updateFinset_congr"))
        except Exception:
            pass
    return results


def _r0211_updateFinset_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.updateFinset_univ
    # updateFinset x .univ y = fun i : ι ↦ y ⟨i, Finset.mem_univ i⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "updateFinset", 3)
    if args is not None:
        try:
            rhs = OOp("fun", (OVar("i"), OVar("colon"), OVar("i"), OVar("_unknown"), args[2], OVar("i_Finset_mem_univ_i"),))
            results.append((rhs, "Mathlib: Function_updateFinset_univ"))
        except Exception:
            pass
    return results


def _r0212_updateFinset_univ_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.updateFinset_univ_apply
    # updateFinset x .univ y i = y ⟨i, Finset.mem_univ i⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "updateFinset", 4)
    if args is not None:
        try:
            rhs = OOp("y", (OVar("i_Finset_mem_univ_i"),))
            results.append((rhs, "Mathlib: Function_updateFinset_univ_apply"))
        except Exception:
            pass
    return results


def _r0213_toEmbedding_equivOfFiniteSelfEmbedding(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.toEmbedding_equivOfFiniteSelfEmbedding
    # e.equivOfFiniteSelfEmbedding.toEmbedding = e
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_equivOfFiniteSelfEmbedding_toEmbedding")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e")
            results.append((rhs, "Mathlib: Function_Embedding_toEmbedding_equivOfFiniteSelfEmbedding"))
    except Exception:
        pass
    return results


def _r0214_exists_of_card_eq_finset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.exists_of_card_eq_finset
    # ∃ f : α ↪ β, Finset.univ.map f = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 7)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Function_Embedding_exists_of_card_eq_finset"))
        except Exception:
            pass
    return results


def _r0215_left_inv_of_invOfMemRange(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Injective.left_inv_of_invOfMemRange
    # f (hf.invOfMemRange b) = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: Function_Injective_left_inv_of_invOfMemRange"))
        except Exception:
            pass
    return results


def _r0216_right_inv_of_invOfMemRange(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Injective.right_inv_of_invOfMemRange
    # hf.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hf_invOfMemRange", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Function_Injective_right_inv_of_invOfMemRange"))
        except Exception:
            pass
    return results


def _r0217_left_inv_of_invOfMemRange(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.left_inv_of_invOfMemRange
    # f (f.invOfMemRange b) = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: Function_Embedding_left_inv_of_invOfMemRange"))
        except Exception:
            pass
    return results


def _r0218_apply_eq_iff_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: EmbeddingLike.apply_eq_iff_eq
    # f x = f y ↔ x = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("f", (OVar("y"),)), args[0])), OVar("y")))
            results.append((rhs, "Mathlib: EmbeddingLike_apply_eq_iff_eq"))
        except Exception:
            pass
    return results


def _r0219_list_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.LeftInverse.list_map
    # LeftInverse (map f) (map g)   | [] =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LeftInverse", 4)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: Function_LeftInverse_list_map"))
        except Exception:
            pass
    return results


def _r0220_mem_graph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.mem_graph
    # a ~[f.graph] b ↔ f a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: Function_mem_graph"))
        except Exception:
            pass
    return results


def _r0221_graph_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.graph_inj
    # f.graph = g.graph ↔ f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_graph")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("g_graph"), OVar("f"))), OVar("g")))
            results.append((rhs, "Mathlib: Function_graph_inj"))
    except Exception:
        pass
    return results


def _r0222_encard_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Injective.encard_image
    # (f '' s).encard = s.encard
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_prime_prime_s_encard")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_encard")
            results.append((rhs, "Mathlib: Function_Injective_encard_image"))
    except Exception:
        pass
    return results


def _r0223_card_le_card_add_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Surjective.card_le_card_add_one_iff
    # Nat.card α ≤ Nat.card β + 1 ↔ ∀ a b c d,       f a = f b → f c = f d → a ≠ b → c ≠ d → {a, b} = ({c, d} : Set α)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("c_d", (OVar("colon"), OVar("Set"), OVar("a"),))
            results.append((rhs, "Mathlib: Function_Surjective_card_le_card_add_one_iff"))
    except Exception:
        pass
    return results


def _r0224_invFunOn_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.invFunOn_pos
    # invFunOn f s b ∈ s ∧ f (invFunOn f s b) = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: Function_invFunOn_pos"))
        except Exception:
            pass
    return results


def _r0225_invFunOn_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.invFunOn_eq
    # f (invFunOn f s b) = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: Function_invFunOn_eq"))
        except Exception:
            pass
    return results


def _r0226_invFunOn_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.invFunOn_neg
    # invFunOn f s b = Classical.choice ‹Nonempty α›
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "invFunOn", 3)
    if args is not None:
        try:
            rhs = OOp("Classical_choice", (OVar("Nonempty"), OVar("a"),))
            results.append((rhs, "Mathlib: Function_invFunOn_neg"))
        except Exception:
            pass
    return results


def _r0227_update_comp_eq_of_notMem_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.update_comp_eq_of_notMem_range
    # update g i a ∘ f = g ∘ f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("comp", (OVar("g"), args[1]))
            results.append((rhs, "Mathlib: Function_update_comp_eq_of_notMem_range"))
        except Exception:
            pass
    return results


def _r0228_insert_injOn(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.insert_injOn
    # sᶜ.InjOn fun a => insert a s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_InjOn", 2)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("insert"), args[1], OVar("s"),))
            results.append((rhs, "Mathlib: Function_insert_injOn"))
        except Exception:
            pass
    return results


def _r0229_apply_eq_of_range_eq_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.apply_eq_of_range_eq_singleton
    # f a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: Function_apply_eq_of_range_eq_singleton"))
        except Exception:
            pass
    return results


def _r0230_image_eq_preimage_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Involutive.image_eq_preimage_symm
    # image f = preimage f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image", 1)
    if args is not None:
        try:
            rhs = OOp("preimage", (args[0],))
            results.append((rhs, "Mathlib: Function_Involutive_image_eq_preimage_symm"))
        except Exception:
            pass
    return results


def _r0231_preimage_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Injective.preimage_image
    # f ⁻¹' (f '' s) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Function_Injective_preimage_image"))
        except Exception:
            pass
    return results


def _r0232_image_preimage(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Surjective.image_preimage
    # f '' (f ⁻¹' s) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Function_Surjective_image_preimage"))
        except Exception:
            pass
    return results


def _r0233_range_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Surjective.range_comp
    # range (g ∘ f) = range g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OOp("range", (OVar("g"),))
            results.append((rhs, "Mathlib: Function_Surjective_range_comp"))
        except Exception:
            pass
    return results


def _r0234_mem_range_iff_existsUnique(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Injective.mem_range_iff_existsUnique
    # b ∈ range f ↔ ∃! a, f a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: Function_Injective_mem_range_iff_existsUnique"))
        except Exception:
            pass
    return results


def _r0235_compl_image_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Injective.compl_image_eq
    # (f '' s)ᶜ = f '' sᶜ ∪ (range f)ᶜ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_prime_prime_s")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("union", (OOp("f", (OVar("prime_prime"), OVar("s"),)), OVar("range_f")))
            results.append((rhs, "Mathlib: Function_Injective_compl_image_eq"))
    except Exception:
        pass
    return results


def _r0236_image_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.LeftInverse.image_image
    # g '' (f '' s) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Function_LeftInverse_image_image"))
        except Exception:
            pass
    return results


def _r0237_preimage_preimage(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.LeftInverse.preimage_preimage
    # f ⁻¹' (g ⁻¹' s) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Function_LeftInverse_preimage_preimage"))
        except Exception:
            pass
    return results


def _r0238_image_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.LeftInverse.image_eq
    # f '' s = range f ∩ g ⁻¹' s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 2)
    if args is not None:
        try:
            rhs = OOp("inter", (OOp("range", (OVar("f"),)), OOp("g", (OVar("inv_prime"), args[1],))))
            results.append((rhs, "Mathlib: Function_LeftInverse_image_eq"))
        except Exception:
            pass
    return results


def _r0239_iUnion_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Surjective.iUnion_comp
    # ⋃ x, g (f x) = ⋃ y, g y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("y"), args[1], OVar("y"),))
            results.append((rhs, "Mathlib: Function_Surjective_iUnion_comp"))
        except Exception:
            pass
    return results


def _r0240_iInter_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Surjective.iInter_comp
    # ⋂ x, g (f x) = ⋂ y, g y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("y"), args[1], OVar("y"),))
            results.append((rhs, "Mathlib: Function_Surjective_iInter_comp"))
        except Exception:
            pass
    return results


def _r0241_pullback_comm_sq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.pullback_comm_sq
    # f ∘ @fst X Y Z f g = g ∘ @snd X Y Z f g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("comp", (OVar("g"), OOp("at_snd", (OVar("X"), OVar("Y"), OVar("Z"), args[0], OVar("g"),))))
            results.append((rhs, "Mathlib: Function_pullback_comm_sq"))
        except Exception:
            pass
    return results


def _r0242_preimage_pullbackDiagonal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Injective.preimage_pullbackDiagonal
    # mapPullback g id g (by rfl) (by rfl) ⁻¹' pullbackDiagonal f = pullbackDiagonal (f ∘ g)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapPullback", 8)
    if args is not None:
        try:
            rhs = OOp("pullbackDiagonal", (OOp("comp", (args[7], args[2])),))
            results.append((rhs, "Mathlib: Function_Injective_preimage_pullbackDiagonal"))
        except Exception:
            pass
    return results


def _r0243_sigma_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Injective.sigma_map
    # Injective (Sigma.map f₁ f₂)   | ⟨i, x⟩, ⟨j, y⟩, h =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "injective", 5)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: Function_Injective_sigma_map"))
        except Exception:
            pass
    return results


def _r0244_sumMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Surjective.sumMap
    # Surjective (Sum.map f g)   | inl y =>     let ⟨x, hx⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "surjective", 4)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("let"), OVar("x_hx"),))
            results.append((rhs, "Mathlib: Function_Surjective_sumMap"))
        except Exception:
            pass
    return results


def _r0245_birkhoffAverage_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.IsFixedPt.birkhoffAverage_eq
    # birkhoffAverage R f g n x = g x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "birkhoffAverage", 5)
    if args is not None:
        try:
            rhs = OOp("g", (args[4],))
            results.append((rhs, "Mathlib: Function_IsFixedPt_birkhoffAverage_eq"))
        except Exception:
            pass
    return results


def _r0246_birkhoffSum_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.IsFixedPt.birkhoffSum_eq
    # birkhoffSum f g n x = n • g x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "birkhoffSum", 4)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("_unknown"), args[1], args[3],))
            results.append((rhs, "Mathlib: Function_IsFixedPt_birkhoffSum_eq"))
        except Exception:
            pass
    return results


def _r0247_forall_isFixedPt_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.forall_isFixedPt_iff
    # (∀ x, IsFixedPt f x) ↔ f = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Function_forall_isFixedPt_iff"))
        except Exception:
            pass
    return results


def _r0248_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.IsFixedPt.eq
    # f x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Function_IsFixedPt_eq"))
        except Exception:
            pass
    return results


def _r0249_perm_zpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.IsFixedPt.perm_zpow
    # ∀ n : ℤ, IsFixedPt (⇑(e ^ n)) x   | Int.ofNat _ => h.perm_pow _   | Int.negSucc n => (h.perm_pow <| n + 1).perm_inv  end
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsFixedPt", 5)
    if args is not None:
        try:
            rhs = OOp("iff", (OOp("gt", (OVar("h_perm_pow"), args[4], args[2], OVar("Int_negSucc"), OVar("n"), OVar("eq_gt"), OVar("h_perm_pow_lt_pipe_n_plus_1_perm_inv_end"), OVar("IsFixedPt_at_simp_theorem"), OVar("Injective_isFixedPt_apply_iff"), OOp("hf", (OVar("colon"), OVar("Injective"), OVar("f"),)), OVar("x_colon_a"), OVar("colon"), OVar("IsFixedPt"), OVar("f"), OOp("f", (args[1],)),)), OOp("IsFixedPt", (OVar("f"), args[1],))))
            results.append((rhs, "Mathlib: Function_IsFixedPt_perm_zpow"))
        except Exception:
            pass
    return results


def _r0250_fixedPoints_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.fixedPoints_id
    # fixedPoints (@id α) = Set.univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fixedPoints", 1)
    if args is not None:
        try:
            rhs = OVar("Set_univ")
            results.append((rhs, "Mathlib: Function_fixedPoints_id"))
        except Exception:
            pass
    return results


def _r0251_iterate_mod_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.IsPeriodicPt.iterate_mod_apply
    # f^[m % n] x = f^[m] x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fpow_m_n", 1)
    if args is not None:
        try:
            rhs = OOp("fpow_m", (args[0],))
            results.append((rhs, "Mathlib: Function_IsPeriodicPt_iterate_mod_apply"))
        except Exception:
            pass
    return results


def _r0252_eq_of_apply_eq_same(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.IsPeriodicPt.eq_of_apply_eq_same
    # x = y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("y")
            results.append((rhs, "Mathlib: Function_IsPeriodicPt_eq_of_apply_eq_same"))
    except Exception:
        pass
    return results


def _r0253_eq_of_apply_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.IsPeriodicPt.eq_of_apply_eq
    # x = y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("y")
            results.append((rhs, "Mathlib: Function_IsPeriodicPt_eq_of_apply_eq"))
    except Exception:
        pass
    return results


def _r0254_bUnion_ptsOfPeriod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.bUnion_ptsOfPeriod
    # ⋃ n > 0, ptsOfPeriod f n = periodicPts f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, ">", 2)
    if args is not None:
        try:
            rhs = OOp("periodicPts", (OVar("f"),))
            results.append((rhs, "Mathlib: Function_bUnion_ptsOfPeriod"))
        except Exception:
            pass
    return results


def _r0255_iUnion_pnat_ptsOfPeriod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.iUnion_pnat_ptsOfPeriod
    # ⋃ n : ℕ+, ptsOfPeriod f n = periodicPts f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 6)
    if args is not None:
        try:
            rhs = OOp("periodicPts", (args[4],))
            results.append((rhs, "Mathlib: Function_iUnion_pnat_ptsOfPeriod"))
        except Exception:
            pass
    return results


def _r0256_iterate_minimalPeriod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.iterate_minimalPeriod
    # f^[minimalPeriod f x] x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fpow_minimalPeriod_f_x", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Function_iterate_minimalPeriod"))
        except Exception:
            pass
    return results


def _r0257_iterate_mod_minimalPeriod_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.iterate_mod_minimalPeriod_eq
    # f^[n % minimalPeriod f x] x = f^[n] x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fpow_n_minimalPeriod_f_x", 1)
    if args is not None:
        try:
            rhs = OOp("fpow_n", (args[0],))
            results.append((rhs, "Mathlib: Function_iterate_mod_minimalPeriod_eq"))
        except Exception:
            pass
    return results


def _r0258_minimalPeriod_eq_zero_of_notMem_periodic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.minimalPeriod_eq_zero_of_notMem_periodicPts
    # minimalPeriod f x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minimalPeriod", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Function_minimalPeriod_eq_zero_of_notMem_periodicPts"))
        except Exception:
            pass
    return results


def _r0259_minimalPeriod_eq_zero_iff_notMem_periodi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.minimalPeriod_eq_zero_iff_notMem_periodicPts
    # minimalPeriod f x = 0 ↔ x ∉ periodicPts f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minimalPeriod", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (OLit(0), OOp("not_in", (args[1], OOp("periodicPts", (args[0],))))))
            results.append((rhs, "Mathlib: Function_minimalPeriod_eq_zero_iff_notMem_periodicPts"))
        except Exception:
            pass
    return results


def _r0260_minimalPeriod_apply_iterate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.minimalPeriod_apply_iterate
    # minimalPeriod f (f^[n] x) = minimalPeriod f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minimalPeriod", 2)
    if args is not None:
        try:
            rhs = OOp("minimalPeriod", (args[0], OVar("x"),))
            results.append((rhs, "Mathlib: Function_minimalPeriod_apply_iterate"))
        except Exception:
            pass
    return results


def _r0261_minimalPeriod_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.minimalPeriod_apply
    # minimalPeriod f (f x) = minimalPeriod f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minimalPeriod", 2)
    if args is not None:
        try:
            rhs = OOp("minimalPeriod", (args[0], OVar("x"),))
            results.append((rhs, "Mathlib: Function_minimalPeriod_apply"))
        except Exception:
            pass
    return results


def _r0262_iterate_eq_iterate_iff_of_lt_minimalPeri(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
    # f^[m] x = f^[n] x ↔ m = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fpow_m", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("fpow_n", (args[0],)), OVar("m"))), OVar("n")))
            results.append((rhs, "Mathlib: Function_iterate_eq_iterate_iff_of_lt_minimalPeriod"))
        except Exception:
            pass
    return results


def _r0263_minimalPeriod_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.minimalPeriod_id
    # minimalPeriod id x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minimalPeriod", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Function_minimalPeriod_id"))
        except Exception:
            pass
    return results


def _r0264_minimalPeriod_eq_one_iff_isFixedPt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.minimalPeriod_eq_one_iff_isFixedPt
    # minimalPeriod f x = 1 ↔ IsFixedPt f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minimalPeriod", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (OLit(1), OOp("IsFixedPt", (args[0], args[1],))))
            results.append((rhs, "Mathlib: Function_minimalPeriod_eq_one_iff_isFixedPt"))
        except Exception:
            pass
    return results


def _r0265_minimalPeriod_eq_one_of_subsingleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.minimalPeriod_eq_one_of_subsingleton
    # minimalPeriod f x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minimalPeriod", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Function_minimalPeriod_eq_one_of_subsingleton"))
        except Exception:
            pass
    return results


def _r0266_eq_zero_of_lt_minimalPeriod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.IsPeriodicPt.eq_zero_of_lt_minimalPeriod
    # n = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Function_IsPeriodicPt_eq_zero_of_lt_minimalPeriod"))
    except Exception:
        pass
    return results


def _r0267_not_isPeriodicPt_of_pos_of_lt_minimalPer(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod
    # ∀ {n : ℕ} (_ : n ≠ 0) (_ : n < minimalPeriod f x), ¬IsPeriodicPt f n x   | 0, n0, _ => (n0 rfl).elim   | _ + 1, _, hn =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "not_IsPeriodicPt", 7)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("gt", (OVar("n0_rfl_elim"), args[3], args[6],)), OOp("_1", (args[6], OVar("hn"), OVar("eq_gt"), OVar("fun"), OVar("hp"), OVar("eq_gt"), OVar("Nat_succ_ne_zero"), args[6], OVar("hp_eq_zero_of_lt_minimalPeriod_hn_theorem"), OVar("IsPeriodicPt_minimalPeriod_dvd"), OOp("hx", (OVar("colon"), OVar("IsPeriodicPt"), args[0], args[1], args[2],)), OVar("colon"), OVar("minimalPeriod"), args[0], args[2], args[6], args[1],))))
            results.append((rhs, "Mathlib: Function_not_isPeriodicPt_of_pos_of_lt_minimalPeriod"))
        except Exception:
            pass
    return results


def _r0268_minimalPeriod_eq_minimalPeriod_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.minimalPeriod_eq_minimalPeriod_iff
    # minimalPeriod f x = minimalPeriod g y ↔ ∀ n, IsPeriodicPt f n x ↔ IsPeriodicPt g n y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minimalPeriod", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (OOp("minimalPeriod", (OVar("g"), OVar("y"),)), OOp("iff", (OOp("forall", (OVar("n"), OVar("IsPeriodicPt"), args[0], OVar("n"), args[1],)), OOp("IsPeriodicPt", (OVar("g"), OVar("n"), OVar("y"),))))))
            results.append((rhs, "Mathlib: Function_minimalPeriod_eq_minimalPeriod_iff"))
        except Exception:
            pass
    return results


def _r0269_minimalPeriod_iterate_eq_div_gcd_aux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.minimalPeriod_iterate_eq_div_gcd_aux
    # minimalPeriod f^[n] x = minimalPeriod f x / Nat.gcd (minimalPeriod f x) n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minimalPeriod", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("minimalPeriod", (OVar("f"), args[1],)), OOp("gcd", (OOp("minimalPeriod", (OVar("f"), args[1],)), OVar("n"),))))
            results.append((rhs, "Mathlib: Function_minimalPeriod_iterate_eq_div_gcd_aux"))
        except Exception:
            pass
    return results


def _r0270_minimalPeriod_iterate_eq_div_gcd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.minimalPeriod_iterate_eq_div_gcd
    # minimalPeriod f^[n] x = minimalPeriod f x / Nat.gcd (minimalPeriod f x) n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minimalPeriod", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("minimalPeriod", (OVar("f"), args[1],)), OOp("gcd", (OOp("minimalPeriod", (OVar("f"), args[1],)), OVar("n"),))))
            results.append((rhs, "Mathlib: Function_minimalPeriod_iterate_eq_div_gcd"))
        except Exception:
            pass
    return results


def _r0271_periodicOrbit_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.periodicOrbit_def
    # periodicOrbit f x = (List.range (minimalPeriod f x)).map fun n => f^[n] x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "periodicOrbit", 2)
    if args is not None:
        try:
            rhs = OOp("List_range_minimalPeriod_f_x_map", (OVar("fun"), OVar("n"), OVar("eq_gt"), OVar("fpow_n"), args[1],))
            results.append((rhs, "Mathlib: Function_periodicOrbit_def"))
        except Exception:
            pass
    return results


def _r0272_periodicOrbit_eq_cycle_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.periodicOrbit_eq_cycle_map
    # periodicOrbit f x = (List.range (minimalPeriod f x) : Cycle ℕ).map fun n => f^[n] x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "periodicOrbit", 2)
    if args is not None:
        try:
            rhs = OOp("List_range_minimalPeriod_f_x_colon_Cycle_map", (OVar("fun"), OVar("n"), OVar("eq_gt"), OVar("fpow_n"), args[1],))
            results.append((rhs, "Mathlib: Function_periodicOrbit_eq_cycle_map"))
        except Exception:
            pass
    return results


def _r0273_periodicOrbit_length(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.periodicOrbit_length
    # (periodicOrbit f x).length = minimalPeriod f x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("periodicOrbit_f_x_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("minimalPeriod", (OVar("f"), OVar("x"),))
            results.append((rhs, "Mathlib: Function_periodicOrbit_length"))
    except Exception:
        pass
    return results


def _r0274_periodicOrbit_eq_nil_of_not_periodic_pt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.periodicOrbit_eq_nil_of_not_periodic_pt
    # periodicOrbit f x = Cycle.nil
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "periodicOrbit", 2)
    if args is not None:
        try:
            rhs = OVar("Cycle_nil")
            results.append((rhs, "Mathlib: Function_periodicOrbit_eq_nil_of_not_periodic_pt"))
        except Exception:
            pass
    return results


def _r0275_mem_periodicOrbit_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.mem_periodicOrbit_iff
    # y ∈ periodicOrbit f x ↔ ∃ n, f^[n] x = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: Function_mem_periodicOrbit_iff"))
        except Exception:
            pass
    return results


def _r0276_exists_iterate_apply_eq_of_mem_periodicP(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.exists_iterate_apply_eq_of_mem_periodicPts
    # ∃ n, f^[n] x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: Function_exists_iterate_apply_eq_of_mem_periodicPts"))
        except Exception:
            pass
    return results


def _r0277_periodicOrbit_apply_iterate_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.periodicOrbit_apply_iterate_eq
    # periodicOrbit f (f^[n] x) = periodicOrbit f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "periodicOrbit", 2)
    if args is not None:
        try:
            rhs = OOp("periodicOrbit", (args[0], OVar("x"),))
            results.append((rhs, "Mathlib: Function_periodicOrbit_apply_iterate_eq"))
        except Exception:
            pass
    return results


def _r0278_periodicOrbit_apply_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.periodicOrbit_apply_eq
    # periodicOrbit f (f x) = periodicOrbit f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "periodicOrbit", 2)
    if args is not None:
        try:
            rhs = OOp("periodicOrbit", (args[0], OVar("x"),))
            results.append((rhs, "Mathlib: Function_periodicOrbit_apply_eq"))
        except Exception:
            pass
    return results


def _r0279_directed_ptsOfPeriod_pnat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.directed_ptsOfPeriod_pnat
    # Directed (· ⊆ ·) fun n : ℕ+ => ptsOfPeriod f n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Directed", 5)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("ptsOfPeriod"), OVar("f"), args[2],))
            results.append((rhs, "Mathlib: Function_directed_ptsOfPeriod_pnat"))
        except Exception:
            pass
    return results


def _r0280_minimalPeriod_eq_prime_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.minimalPeriod_eq_prime_iff
    # minimalPeriod f x = p ↔ IsPeriodicPt f p x ∧ ¬IsFixedPt f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minimalPeriod", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("iff", (OVar("p"), OOp("IsPeriodicPt", (args[0], OVar("p"), args[1],)))), OOp("not_IsFixedPt", (args[0], args[1],))))
            results.append((rhs, "Mathlib: Function_minimalPeriod_eq_prime_iff"))
        except Exception:
            pass
    return results


def _r0281_minimalPeriod_eq_sInf_n_pos_IsPeriodicPt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.minimalPeriod_eq_sInf_n_pos_IsPeriodicPt
    # minimalPeriod f x = sInf { n > 0 | IsPeriodicPt f n x }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minimalPeriod", 2)
    if args is not None:
        try:
            rhs = OOp("sInf", (OVar("n_gt_0_pipe_IsPeriodicPt_f_n_x"),))
            results.append((rhs, "Mathlib: Function_minimalPeriod_eq_sInf_n_pos_IsPeriodicPt"))
        except Exception:
            pass
    return results


def _r0282_minimalPeriod_eq_prime(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.minimalPeriod_eq_prime
    # minimalPeriod f x = p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minimalPeriod", 2)
    if args is not None:
        try:
            rhs = OVar("p")
            results.append((rhs, "Mathlib: Function_minimalPeriod_eq_prime"))
        except Exception:
            pass
    return results


def _r0283_minimalPeriod_eq_prime_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.minimalPeriod_eq_prime_pow
    # minimalPeriod f x = p ^ (k + 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minimalPeriod", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("p"), OOp("+", (OVar("k"), OLit(1)))))
            results.append((rhs, "Mathlib: Function_minimalPeriod_eq_prime_pow"))
        except Exception:
            pass
    return results


def _r0284_minimalPeriod_of_comp_eq_mul_of_coprime(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Commute.minimalPeriod_of_comp_eq_mul_of_coprime
    # minimalPeriod (f ∘ g) x = minimalPeriod f x * minimalPeriod g x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minimalPeriod", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("minimalPeriod", (OVar("f"), args[1],)), OOp("minimalPeriod", (OVar("g"), args[1],))))
            results.append((rhs, "Mathlib: Function_Commute_minimalPeriod_of_comp_eq_mul_of_coprime"))
        except Exception:
            pass
    return results


def _r0285_injective_iff_periodicPts_eq_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.injective_iff_periodicPts_eq_univ
    # Injective f ↔ periodicPts f = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: Function_injective_iff_periodicPts_eq_univ"))
        except Exception:
            pass
    return results


def _r0286_injective_iff_iterate_factorial_card_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.injective_iff_iterate_factorial_card_eq_id
    # Injective f ↔ f^[(card α)!] = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Function_injective_iff_iterate_factorial_card_eq_id"))
        except Exception:
            pass
    return results


def _r0287_minimalPeriod_prodMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.minimalPeriod_prodMap
    # minimalPeriod (Prod.map f g) x = (minimalPeriod f x.1).lcm (minimalPeriod g x.2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minimalPeriod", 2)
    if args is not None:
        try:
            rhs = OOp("minimalPeriod_f_x_1_lcm", (OOp("minimalPeriod", (OVar("g"), OVar("x_2"),)),))
            results.append((rhs, "Mathlib: Function_minimalPeriod_prodMap"))
        except Exception:
            pass
    return results


def _r0288_preimage_dynEntourage(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Semiconj.preimage_dynEntourage
    # (map φ φ) ⁻¹' (dynEntourage T U n) = dynEntourage S ((map φ φ) ⁻¹' U) n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_phi_phi", 2)
    if args is not None:
        try:
            rhs = OOp("dynEntourage", (OVar("S"), OOp("map_phi_phi", (args[0], OVar("U"),)), OVar("n"),))
            results.append((rhs, "Mathlib: Function_Semiconj_preimage_dynEntourage"))
        except Exception:
            pass
    return results


def _r0289_smul_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.smul_def
    # g • f = f.trans (MulAction.toPerm g).toEmbedding
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g", 2)
    if args is not None:
        try:
            rhs = OOp("f_trans", (OVar("MulAction_toPerm_g_toEmbedding"),))
            results.append((rhs, "Mathlib: Function_Embedding_smul_def"))
        except Exception:
            pass
    return results


def _r0290_smul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.smul_apply
    # (g • f) a = g • f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_f", 1)
    if args is not None:
        try:
            rhs = OOp("g", (OVar("_unknown"), OVar("f"), args[0],))
            results.append((rhs, "Mathlib: Function_Embedding_smul_apply"))
        except Exception:
            pass
    return results


def _r0291_mulActionHom_embedding_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Injective.mulActionHom_embedding_apply
    # hf.mulActionHom_embedding ι x i = f (x i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hf_mulActionHom_embedding", 3)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("x", (args[2],)),))
            results.append((rhs, "Mathlib: Function_Injective_mulActionHom_embedding_apply"))
        except Exception:
            pass
    return results


def _r0292_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.ext
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: Function_Embedding_ext"))
    except Exception:
        pass
    return results


def _r0293_toFun_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.toFun_eq_coe
    # toFun f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFun", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Function_Embedding_toFun_eq_coe"))
        except Exception:
            pass
    return results


def _r0294_apply_eq_iff_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.apply_eq_iff_eq
    # f x = f y ↔ x = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("f", (OVar("y"),)), args[0])), OVar("y")))
            results.append((rhs, "Mathlib: Function_Embedding_apply_eq_iff_eq"))
        except Exception:
            pass
    return results


def _r0295_mk_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.mk_id
    # mk id injective_id = .refl α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 2)
    if args is not None:
        try:
            rhs = OOp("refl", (OVar("a"),))
            results.append((rhs, "Mathlib: Function_Embedding_mk_id"))
        except Exception:
            pass
    return results


def _r0296_equiv_symm_toEmbedding_trans_toEmbedding(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding
    # e.symm.toEmbedding.trans e.toEmbedding = Embedding.refl _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_symm_toEmbedding_trans", 1)
    if args is not None:
        try:
            rhs = OOp("Embedding_refl", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: Function_Embedding_equiv_symm_toEmbedding_trans_toEmbedding"))
        except Exception:
            pass
    return results


def _r0297_setValue_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.setValue_eq
    # setValue f a b a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "setValue", 4)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: Function_Embedding_setValue_eq"))
        except Exception:
            pass
    return results


def _r0298_setValue_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.setValue_eq_iff
    # setValue f a b a' = b ↔ a' = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "setValue", 4)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (args[2], args[3])), args[1]))
            results.append((rhs, "Mathlib: Function_Embedding_setValue_eq_iff"))
        except Exception:
            pass
    return results


def _r0299_setValue_eq_of_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.setValue_eq_of_ne
    # setValue f a b c = f c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "setValue", 4)
    if args is not None:
        try:
            rhs = OOp("f", (args[3],))
            results.append((rhs, "Mathlib: Function_Embedding_setValue_eq_of_ne"))
        except Exception:
            pass
    return results


def _r0300_setValue_right_apply_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.setValue_right_apply_eq
    # setValue f a (f c) c = f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "setValue", 4)
    if args is not None:
        try:
            rhs = OOp("f", (args[1],))
            results.append((rhs, "Mathlib: Function_Embedding_setValue_right_apply_eq"))
        except Exception:
            pass
    return results


def _r0301_subtype_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.subtype_apply
    # subtype p x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "subtype", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Function_Embedding_subtype_apply"))
        except Exception:
            pass
    return results


def _r0302_coe_subtype(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.coe_subtype
    # ↑(subtype p) = Subtype.val
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("subtype_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Subtype_val")
            results.append((rhs, "Mathlib: Function_Embedding_coe_subtype"))
    except Exception:
        pass
    return results


def _r0303_coe_quotientOut(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.coe_quotientOut
    # ↑(quotientOut α) = Quotient.out
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("quotientOut_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Quotient_out")
            results.append((rhs, "Mathlib: Function_Embedding_coe_quotientOut"))
    except Exception:
        pass
    return results


def _r0304_coe_prodMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.coe_prodMap
    # e₁.prodMap e₂ = Prod.map e₁ e₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_1_prodMap", 1)
    if args is not None:
        try:
            rhs = OOp("Prod_map", (OVar("e_1"), args[0],))
            results.append((rhs, "Mathlib: Function_Embedding_coe_prodMap"))
        except Exception:
            pass
    return results


def _r0305_coe_sumMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.coe_sumMap
    # sumMap e₁ e₂ = Sum.map e₁ e₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumMap", 2)
    if args is not None:
        try:
            rhs = OOp("Sum_map", (args[0], args[1],))
            results.append((rhs, "Mathlib: Function_Embedding_coe_sumMap"))
        except Exception:
            pass
    return results


def _r0306_codRestrict_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.codRestrict_apply
    # codRestrict p f H a = ⟨f a, H a⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "codRestrict", 4)
    if args is not None:
        try:
            rhs = OVar("f_a_H_a")
            results.append((rhs, "Mathlib: Function_Embedding_codRestrict_apply"))
        except Exception:
            pass
    return results


def _r0307_sumSet_preimage_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.sumSet_preimage_inl
    # .inl ⁻¹' (Function.Embedding.sumSet h ⁻¹' r) = r ∩ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inl", 2)
    if args is not None:
        try:
            rhs = OOp("inter", (OVar("r"), OVar("s")))
            results.append((rhs, "Mathlib: Function_Embedding_sumSet_preimage_inl"))
        except Exception:
            pass
    return results


def _r0308_sigmaSet_preimage(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.sigmaSet_preimage
    # Sigma.mk i ⁻¹' (Function.Embedding.sigmaSet h ⁻¹' r) = r ∩ s i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_mk", 3)
    if args is not None:
        try:
            rhs = OOp("inter", (OVar("r"), OOp("s", (args[0],))))
            results.append((rhs, "Mathlib: Function_Embedding_sigmaSet_preimage"))
        except Exception:
            pass
    return results


def _r0309_sigmaSet_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.sigmaSet_range
    # Set.range (Function.Embedding.sigmaSet h) = ⋃ i, s i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_range", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), OVar("s"), OVar("i"),))
            results.append((rhs, "Mathlib: Function_Embedding_sigmaSet_range"))
        except Exception:
            pass
    return results


def _r0310_symm_eq_self_of_involutive(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Involutive.symm_eq_self_of_involutive
    # f.symm = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Function_Involutive_symm_eq_self_of_involutive"))
    except Exception:
        pass
    return results


def _r0311_map_swap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Injective.map_swap
    # f (Equiv.swap x y z) = Equiv.swap (f x) (f y) (f z)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("Equiv_swap", (OOp("f", (OVar("x"),)), OOp("f", (OVar("y"),)), OOp("f", (OVar("z"),)),))
            results.append((rhs, "Mathlib: Function_Injective_map_swap"))
        except Exception:
            pass
    return results


def _r0312_swap_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Injective.swap_apply
    # Equiv.swap (f x) (f y) (f z) = f (Equiv.swap x y z)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Equiv_swap", 3)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("Equiv_swap", (OVar("x"), OVar("y"), OVar("z"),)),))
            results.append((rhs, "Mathlib: Function_Injective_swap_apply"))
        except Exception:
            pass
    return results


def _r0313_swap_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Injective.swap_comp
    # Equiv.swap (f x) (f y) ∘ f = f ∘ Equiv.swap x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("comp", (args[1], OOp("Equiv_swap", (OVar("x"), OVar("y"),))))
            results.append((rhs, "Mathlib: Function_Injective_swap_comp"))
        except Exception:
            pass
    return results


def _r0314_update_comp_equiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.update_comp_equiv
    # update f a v ∘ g = update (f ∘ g) (g.symm a) v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("update", (OOp("comp", (OVar("f"), args[1])), OOp("g_symm", (OVar("a"),)), OVar("v"),))
            results.append((rhs, "Mathlib: Function_update_comp_equiv"))
        except Exception:
            pass
    return results


def _r0315_update_apply_equiv_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.update_apply_equiv_apply
    # update f a v (g a') = update (f ∘ g) (g.symm a) v a'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "update", 4)
    if args is not None:
        try:
            rhs = OOp("update", (OOp("comp", (args[0], OVar("g"))), OOp("g_symm", (args[1],)), args[2], OVar("a_prime"),))
            results.append((rhs, "Mathlib: Function_update_apply_equiv_apply"))
        except Exception:
            pass
    return results


def _r0316_toEquivRange_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.toEquivRange_apply
    # f.toEquivRange a = ⟨f a, Set.mem_range_self a⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_toEquivRange", 1)
    if args is not None:
        try:
            rhs = OVar("f_a_Set_mem_range_self_a")
            results.append((rhs, "Mathlib: Function_Embedding_toEquivRange_apply"))
        except Exception:
            pass
    return results


def _r0317_toEquivRange_symm_apply_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Embedding.toEquivRange_symm_apply_self
    # f.toEquivRange.symm ⟨f a, Set.mem_range_self a⟩ = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_toEquivRange_symm", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Function_Embedding_toEquivRange_symm_apply_self"))
        except Exception:
            pass
    return results


def _r0318_const_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.const_def
    # (fun _ : α ↦ y) = const α y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun", 5)
    if args is not None:
        try:
            rhs = OOp("const", (args[2], args[4],))
            results.append((rhs, "Mathlib: Function_const_def"))
        except Exception:
            pass
    return results


def _r0319_const_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.const_inj
    # const α y₁ = const α y₂ ↔ y₁ = y₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "const", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("const", (args[0], OVar("y_2"),)), args[1])), OVar("y_2")))
            results.append((rhs, "Mathlib: Function_const_inj"))
        except Exception:
            pass
    return results


def _r0320_funext_iff_of_subsingleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.funext_iff_of_subsingleton
    # f x = g y ↔ f = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("g", (OVar("y"),)), OVar("f"))), OVar("g")))
            results.append((rhs, "Mathlib: Function_funext_iff_of_subsingleton"))
        except Exception:
            pass
    return results


def _r0321_not_injective_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.not_injective_iff
    # ¬ Injective f ↔ ∃ a b, f a = f b ∧ a ≠ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("and", (OOp("f", (OVar("b"),)), OVar("a"))), OVar("b")))
            results.append((rhs, "Mathlib: Function_not_injective_iff"))
        except Exception:
            pass
    return results


def _r0322_right_cancellable(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Surjective.right_cancellable
    # g₁ ∘ f = g₂ ∘ f ↔ g₁ = g₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("comp", (OVar("g_2"), args[1])), args[0])), OVar("g_2")))
            results.append((rhs, "Mathlib: Function_Surjective_right_cancellable"))
        except Exception:
            pass
    return results


def _r0323_bijective_iff_existsUnique(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.bijective_iff_existsUnique
    # Bijective f ↔ ∀ b : β, ∃! a : α, f a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: Function_bijective_iff_existsUnique"))
        except Exception:
            pass
    return results


def _r0324_existsUnique(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Bijective.existsUnique
    # ∃! a : α, f a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists_bang", 5)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: Function_Bijective_existsUnique"))
        except Exception:
            pass
    return results


def _r0325_exists_fixed_point_of_surjective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.exists_fixed_point_of_surjective
    # ∃ x, g x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: Function_exists_fixed_point_of_surjective"))
        except Exception:
            pass
    return results


def _r0326_cantor_injective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.cantor_injective
    # ¬Injective f   | i => cantor_surjective (fun a ↦ {b | ∀ U, a = f U → b ∈ U}) <|          RightInverse.surjective (fun U 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "not_Injective", 3)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("cantor_surjective"), OOp("fun", (OVar("a"), OVar("_unknown"), OVar("b_pipe_forall_U_a_eq_f_U_to_b_in_U"),)), OVar("lt_pipe"), OVar("RightInverse_surjective"), OVar("fun_U_Set_ext_fun_fun_h_h_U_rfl_fun_h_e_i_e_h_theorem"), OVar("not_surjective_Type"), OVar("a_colon_Type_u"), OOp("implies", (OOp("f", (OVar("colon"), OVar("a"),)), OOp("Type", (OVar("max"), OVar("u"), OVar("v"),)))), OVar("colon"), OOp("not", (OVar("Surjective"),)), args[0],))
            results.append((rhs, "Mathlib: Function_cantor_injective"))
        except Exception:
            pass
    return results


def _r0327_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.IsPartialInv.eq
    # g (f x) = some x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g", 1)
    if args is not None:
        try:
            rhs = OOp("some", (OVar("x"),))
            results.append((rhs, "Mathlib: Function_IsPartialInv_eq"))
        except Exception:
            pass
    return results


def _r0328_get_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.IsPartialInv.get_eq
    # f (g x |>.get h) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Function_IsPartialInv_get_eq"))
        except Exception:
            pass
    return results


def _r0329_injective_of_isPartialInv_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.injective_of_isPartialInv_right
    # x = y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("y")
            results.append((rhs, "Mathlib: Function_injective_of_isPartialInv_right"))
    except Exception:
        pass
    return results


def _r0330_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.LeftInverse.eq
    # g (f x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Function_LeftInverse_eq"))
        except Exception:
            pass
    return results


def _r0331_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.RightInverse.eq
    # f (g x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Function_RightInverse_eq"))
        except Exception:
            pass
    return results


def _r0332_comp_eq_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.LeftInverse.comp_eq_id
    # f ∘ g = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Function_LeftInverse_comp_eq_id"))
        except Exception:
            pass
    return results


def _r0333_leftInverse_iff_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.leftInverse_iff_comp
    # LeftInverse f g ↔ f ∘ g = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Function_leftInverse_iff_comp"))
        except Exception:
            pass
    return results


def _r0334_comp_eq_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.RightInverse.comp_eq_id
    # g ∘ f = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Function_RightInverse_comp_eq_id"))
        except Exception:
            pass
    return results


def _r0335_rightInverse_iff_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.rightInverse_iff_comp
    # RightInverse f g ↔ g ∘ f = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Function_rightInverse_iff_comp"))
        except Exception:
            pass
    return results


def _r0336_eq_rightInverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.LeftInverse.eq_rightInverse
    # g₁ = g₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("g_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g_2")
            results.append((rhs, "Mathlib: Function_LeftInverse_eq_rightInverse"))
    except Exception:
        pass
    return results


def _r0337_isPartialInv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Injective.isPartialInv
    # IsPartialInv f (partialInv f)   | a, b =>   ⟨fun h =>     open scoped Classical in     have hpi : partialInv f b = if h 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsPartialInv", 5)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("fun_h_eq_gt_open_scoped_Classical_in_have_hpi_colon_partialInv_f_b_eq_if_h_colon_exists_a_f_a_eq_b_then_some_Classical_choose_h_else_none"),))
            results.append((rhs, "Mathlib: Function_Injective_isPartialInv"))
        except Exception:
            pass
    return results


def _r0338_partialInv_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.partialInv_left
    # ∀ x, partialInv f (f x) = some x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "partialInv", 2)
    if args is not None:
        try:
            rhs = OOp("some", (OVar("x"),))
            results.append((rhs, "Mathlib: Function_partialInv_left"))
        except Exception:
            pass
    return results


def _r0339_extend_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Injective.extend_apply
    # extend f g e' (f a) = g a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "extend", 4)
    if args is not None:
        try:
            rhs = OOp("g", (OVar("a"),))
            results.append((rhs, "Mathlib: Injective_extend_apply"))
        except Exception:
            pass
    return results


def _r0340_extend_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Injective.extend_comp
    # extend (f₂₃ ∘ f₁₂) g e' = extend f₂₃ (extend f₁₂ g (e' ∘ f₂₃)) e'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "extend", 3)
    if args is not None:
        try:
            rhs = OOp("extend", (OVar("f_2_3"), OOp("extend", (OVar("f_1_2"), args[1], OOp("comp", (args[2], OVar("f_2_3"))),)), args[2],))
            results.append((rhs, "Mathlib: Injective_extend_comp"))
        except Exception:
            pass
    return results


def _r0341_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Injective2.eq_iff
    # f a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("f", (OVar("a_2"), OVar("b_2"),)), args[0])), OOp("==", (OOp("and", (OVar("a_2"), args[1])), OVar("b_2")))))
            results.append((rhs, "Mathlib: Injective2_eq_iff"))
        except Exception:
            pass
    return results


def _r0342_eq_rec_on_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.LeftInverse.eq_rec_on_eq
    # @Eq.recOn β (f (g (f a))) (fun x _ ↦ γ x) (f a) (congr_arg f (h a)) (C (g (f a))) = C a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_Eq_recOn", 6)
    if args is not None:
        try:
            rhs = OOp("C", (OVar("a"),))
            results.append((rhs, "Mathlib: Function_LeftInverse_eq_rec_on_eq"))
        except Exception:
            pass
    return results


def _r0343_cast_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.LeftInverse.cast_eq
    # cast (congr_arg (fun a ↦ γ (f a)) (h a)) (C (g (f a))) = C a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cast", 2)
    if args is not None:
        try:
            rhs = OOp("C", (OVar("a"),))
            results.append((rhs, "Mathlib: Function_LeftInverse_cast_eq"))
        except Exception:
            pass
    return results


def _r0344_condition(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Coequalizer.condition
    # mk f g (f x) = mk f g (g x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 3)
    if args is not None:
        try:
            rhs = OOp("pair", (args[0], args[1], OOp("g", (OVar("x"),)),))
            results.append((rhs, "Mathlib: Function_Coequalizer_condition"))
        except Exception:
            pass
    return results


def _r0345_desc_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Coequalizer.desc_mk
    # desc f g u hu (mk f g x) = u x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "desc", 5)
    if args is not None:
        try:
            rhs = OOp("u", (OVar("x"),))
            results.append((rhs, "Mathlib: Function_Coequalizer_desc_mk"))
        except Exception:
            pass
    return results


def _r0346_semiconj_iff_comp_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.semiconj_iff_comp_eq
    # Semiconj f ga gb ↔ f ∘ ga = gb ∘ f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("comp", (OVar("gb"), OVar("f")))
            results.append((rhs, "Mathlib: Function_semiconj_iff_comp_eq"))
        except Exception:
            pass
    return results


def _r0347_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Semiconj.eq
    # f (ga x) = gb (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("gb", (OOp("f", (OVar("x"),)),))
            results.append((rhs, "Mathlib: Function_Semiconj_eq"))
        except Exception:
            pass
    return results


def _r0348_option_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Semiconj.option_map
    # Semiconj (Option.map f) (Option.map ga) (Option.map gb)   | none => rfl   | some _ => congr_arg some <| h _  end Semicon
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Semiconj", 5)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("rfl"), args[3], OVar("some"), OVar("_unknown"), OVar("eq_gt"), OVar("congr_arg"), OVar("some"), OVar("lt_pipe"), OVar("h"), OVar("end"), OVar("Semiconj_protected"), OVar("def"), OVar("Commute"), OOp("implies", (OOp("f", (OVar("g"), OVar("colon"), OVar("a"),)), OVar("a"))), OVar("colon"), OVar("Prop"),))
            results.append((rhs, "Mathlib: Function_Semiconj_option_map"))
        except Exception:
            pass
    return results


def _r0349_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Semiconj₂.eq
    # f (ga x y) = gb (f x) (f y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("gb", (OOp("f", (OVar("x"),)), OOp("f", (OVar("y"),)),))
            results.append((rhs, "Mathlib: Function_Semiconj_2_eq"))
        except Exception:
            pass
    return results


def _r0350_comp_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Semiconj₂.comp_eq
    # bicompr f ga = bicompl gb f f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bicompr", 2)
    if args is not None:
        try:
            rhs = OOp("bicompl", (OVar("gb"), args[0], args[0],))
            results.append((rhs, "Mathlib: Function_Semiconj_2_comp_eq"))
        except Exception:
            pass
    return results


def _r0351_flip_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.flip_def
    # flip f = fun b a => f a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "flip", 1)
    if args is not None:
        try:
            rhs = OOp("fun", (OVar("b"), OVar("a"), OVar("eq_gt"), args[0], OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Function_flip_def"))
        except Exception:
            pass
    return results


def _r0352_swap_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.swap_def
    # swap f = fun y x => f x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "swap", 1)
    if args is not None:
        try:
            rhs = OOp("fun", (OVar("y"), OVar("x"), OVar("eq_gt"), args[0], OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: Function_swap_def"))
        except Exception:
            pass
    return results


def _r0353_comp_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.comp_assoc
    # (f ∘ g) ∘ h = f ∘ g ∘ h
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("comp", (OVar("f"), OOp("comp", (OVar("g"), args[1]))))
            results.append((rhs, "Mathlib: Function_comp_assoc"))
        except Exception:
            pass
    return results


def _r0354_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Bijective.comp
    # Bijective g → Bijective f → Bijective (g ∘ f)   | ⟨h_ginj, h_gsurj⟩, ⟨h_finj, h_fsurj⟩ => ⟨h_ginj.comp h_finj, h_gsurj.c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bijective", 4)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("h_ginj_comp_h_finj_h_gsurj_comp_h_fsurj_theorem"), OVar("bijective_id"), OVar("colon"), OVar("Bijective"), OOp("at_id", (OVar("a"),)),))
            results.append((rhs, "Mathlib: Function_Bijective_comp"))
        except Exception:
            pass
    return results


def _r0355_beq_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Injective.beq_eq
    # (f a == f b) = (a == b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 4)
    if args is not None:
        try:
            rhs = OOp("a", (args[1], args[3],))
            results.append((rhs, "Mathlib: Function_Injective_beq_eq"))
        except Exception:
            pass
    return results


def _r0356_eq_fiber_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Fiber.eq_fiber_image
    # a.1 = f ⁻¹' {a.image}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f", (OVar("inv_prime"), OVar("a_image"),))
            results.append((rhs, "Mathlib: Function_Fiber_eq_fiber_image"))
    except Exception:
        pass
    return results


def _r0357_map_eq_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Fiber.map_eq_image
    # f x = a.image
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OVar("a_image")
            results.append((rhs, "Mathlib: Function_Fiber_map_eq_image"))
        except Exception:
            pass
    return results


def _r0358_mk_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Fiber.mk_image
    # (Fiber.mk f y).image = f y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Fiber_mk_f_y_image")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f", (OVar("y"),))
            results.append((rhs, "Mathlib: Function_Fiber_mk_image"))
    except Exception:
        pass
    return results


def _r0359_mem_iff_eq_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Fiber.mem_iff_eq_image
    # y ∈ a.val ↔ f y = a.image
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("a_image")
            results.append((rhs, "Mathlib: Function_Fiber_mem_iff_eq_image"))
        except Exception:
            pass
    return results


def _r0360_map_preimage_eq_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Fiber.map_preimage_eq_image
    # f a.preimage = a.image
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OVar("a_image")
            results.append((rhs, "Mathlib: Function_Fiber_map_preimage_eq_image"))
        except Exception:
            pass
    return results


def _r0361_map_preimage_eq_image_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Fiber.map_preimage_eq_image_map
    # g (f a.preimage) = a.image
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g", 1)
    if args is not None:
        try:
            rhs = OVar("a_image")
            results.append((rhs, "Mathlib: Function_Fiber_map_preimage_eq_image_map"))
        except Exception:
            pass
    return results


def _r0362_image_eq_image_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Fiber.image_eq_image_mk
    # a.image = (Fiber.mk f (g (a.preimage _))).image
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_image")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Fiber_mk_f_g_a_preimage_image")
            results.append((rhs, "Mathlib: Function_Fiber_image_eq_image_mk"))
    except Exception:
        pass
    return results


def _r0363_fromTypes_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.fromTypes_zero
    # FromTypes p τ = τ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "FromTypes", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Function_fromTypes_zero"))
        except Exception:
            pass
    return results


def _r0364_fromTypes_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.fromTypes_nil
    # FromTypes ![] τ = τ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "FromTypes", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Function_fromTypes_nil"))
        except Exception:
            pass
    return results


def _r0365_fromTypes_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.fromTypes_succ
    # FromTypes p τ = (vecHead p → FromTypes (vecTail p) τ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "FromTypes", 2)
    if args is not None:
        try:
            rhs = OOp("implies", (OOp("vecHead", (args[0],)), OOp("FromTypes", (OOp("vecTail", (args[0],)), args[1],))))
            results.append((rhs, "Mathlib: Function_fromTypes_succ"))
        except Exception:
            pass
    return results


def _r0366_fromTypes_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.fromTypes_cons
    # FromTypes (vecCons α p) τ = (α → FromTypes p τ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "FromTypes", 2)
    if args is not None:
        try:
            rhs = OOp("implies", (OVar("a"), OOp("FromTypes", (OVar("p"), args[1],))))
            results.append((rhs, "Mathlib: Function_fromTypes_cons"))
        except Exception:
            pass
    return results


def _r0367_const_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.FromTypes.const_zero
    # const p t = t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "const", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Function_FromTypes_const_zero"))
        except Exception:
            pass
    return results


def _r0368_iterate_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.iterate_zero
    # f^[0] = id
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("fpow_0")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Function_iterate_zero"))
    except Exception:
        pass
    return results


def _r0369_iterate_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.iterate_succ
    # f^[n.succ] = f^[n] ∘ f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("fpow_n_succ")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comp", (OVar("fpow_n"), OVar("f")))
            results.append((rhs, "Mathlib: Function_iterate_succ"))
    except Exception:
        pass
    return results


def _r0370_iterate_add_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.iterate_add_apply
    # f^[m + n] x = f^[m] (f^[n] x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fpow_m_plus_n", 1)
    if args is not None:
        try:
            rhs = OOp("fpow_m", (OOp("fpow_n", (args[0],)),))
            results.append((rhs, "Mathlib: Function_iterate_add_apply"))
        except Exception:
            pass
    return results


def _r0371_iterate_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.iterate_one
    # f^[1] = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("fpow_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Function_iterate_one"))
    except Exception:
        pass
    return results


def _r0372_iterate_fixed(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.iterate_fixed
    # f^[n] x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fpow_n", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Function_iterate_fixed"))
        except Exception:
            pass
    return results


def _r0373_iterate_invariant(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.iterate_invariant
    # g ∘ f^[n] = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Function_iterate_invariant"))
        except Exception:
            pass
    return results


def _r0374_iterate_eq_of_map_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Commute.iterate_eq_of_map_eq
    # f^[n] x = g^[n] x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fpow_n", 1)
    if args is not None:
        try:
            rhs = OOp("gpow_n", (args[0],))
            results.append((rhs, "Mathlib: Function_Commute_iterate_eq_of_map_eq"))
        except Exception:
            pass
    return results


def _r0375_comp_iterate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Commute.comp_iterate
    # (f ∘ g)^[n] = f^[n] ∘ g^[n]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_comp_g_pow_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comp", (OVar("fpow_n"), OVar("gpow_n")))
            results.append((rhs, "Mathlib: Function_Commute_comp_iterate"))
    except Exception:
        pass
    return results


def _r0376_iterate_pred_comp_of_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.iterate_pred_comp_of_pos
    # f^[n.pred] ∘ f = f^[n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("fpow_n")
            results.append((rhs, "Mathlib: Function_iterate_pred_comp_of_pos"))
        except Exception:
            pass
    return results


def _r0377_comp_iterate_pred_of_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.comp_iterate_pred_of_pos
    # f ∘ f^[n.pred] = f^[n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("fpow_n")
            results.append((rhs, "Mathlib: Function_comp_iterate_pred_of_pos"))
        except Exception:
            pass
    return results


def _r0378_rec_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Iterate.rec_zero
    # Iterate.rec motive arg app 0 = arg
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iterate_rec", 4)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Function_Iterate_rec_zero"))
        except Exception:
            pass
    return results


def _r0379_iterate_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.iterate_comm
    # f^[n]^[m] = f^[m]^[n]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("fpow_n_pow_m")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("fpow_m_pow_n")
            results.append((rhs, "Mathlib: Function_iterate_comm"))
    except Exception:
        pass
    return results


def _r0380_iterate_add_eq_iterate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.iterate_add_eq_iterate
    # f^[m + n] a = f^[n] a ↔ f^[m] a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fpow_m_plus_n", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("fpow_n", (args[0],)), OOp("fpow_m", (args[0],)))), args[0]))
            results.append((rhs, "Mathlib: Function_iterate_add_eq_iterate"))
        except Exception:
            pass
    return results


def _r0381_iterate_cancel(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.iterate_cancel
    # f^[m - n] a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fpow_m_minus_n", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Function_iterate_cancel"))
        except Exception:
            pass
    return results


def _r0382_involutive_iff_iter_2_eq_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.involutive_iff_iter_2_eq_id
    # Involutive f ↔ f^[2] = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Function_involutive_iff_iter_2_eq_id"))
        except Exception:
            pass
    return results


def _r0383_ofArity_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.ofArity_zero
    # OfArity α β 0 = β
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "OfArity", 3)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Function_ofArity_zero"))
        except Exception:
            pass
    return results


def _r0384_const_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.OfArity.const_zero
    # const α b 0 = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "const", 3)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Function_OfArity_const_zero"))
        except Exception:
            pass
    return results


def _r0385_const_succ_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.OfArity.const_succ_apply
    # const α b n.succ x = const _ b n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "const", 4)
    if args is not None:
        try:
            rhs = OOp("const", (OVar("_unknown"), args[1], OVar("n"),))
            results.append((rhs, "Mathlib: Function_OfArity_const_succ_apply"))
        except Exception:
            pass
    return results


def _r0386_fromTypes_fin_const(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.FromTypes.fromTypes_fin_const
    # FromTypes (fun (_ : Fin n) => α) β = OfArity α β n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "FromTypes", 2)
    if args is not None:
        try:
            rhs = OOp("OfArity", (OVar("a"), args[1], OVar("n"),))
            results.append((rhs, "Mathlib: Function_FromTypes_fromTypes_fin_const"))
        except Exception:
            pass
    return results


def _r0387_extend_of_isEmpty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.extend_of_isEmpty
    # Function.extend f g h = h
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Function_extend", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: Function_extend_of_isEmpty"))
        except Exception:
            pass
    return results


def _r0388_intervalIntegral_add_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.intervalIntegral_add_eq
    # ∫ x in t..t + T, f x = ∫ x in s..s + T, f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("_unknown", (OVar("x"), OVar("in"), OVar("s_s"),)), OOp("T", (OVar("f"), OVar("x"),))))
            results.append((rhs, "Mathlib: Function_Periodic_intervalIntegral_add_eq"))
        except Exception:
            pass
    return results


def _r0389_intervalIntegral_add_eq_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.intervalIntegral_add_eq_add
    # ∫ x in t..s + T, f x = (∫ x in t..s, f x) + ∫ x in t..t + T, f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("_unknown", (OVar("x"), OVar("in"), OVar("t_s"), OVar("f"), OVar("x"),)), OOp("+", (OOp("_unknown", (OVar("x"), OVar("in"), OVar("t_t"),)), OOp("T", (OVar("f"), OVar("x"),))))))
            results.append((rhs, "Mathlib: Function_Periodic_intervalIntegral_add_eq_add"))
        except Exception:
            pass
    return results


def _r0390_intervalIntegral_add_zsmul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Periodic.intervalIntegral_add_zsmul_eq
    # ∫ x in t..t + n • T, f x = n • ∫ x in t..t + T, f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("n", (OVar("_unknown"), OVar("_unknown"), OVar("x"), OVar("in"), OVar("t_t"),)), OOp("T", (OVar("f"), OVar("x"),))))
            results.append((rhs, "Mathlib: Function_Periodic_intervalIntegral_add_zsmul_eq"))
        except Exception:
            pass
    return results


def _r0391_map_fun(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Embedding.map_fun
    # φ (funMap f x) = funMap f (φ ∘ x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi", 1)
    if args is not None:
        try:
            rhs = OOp("funMap", (OVar("f"), OOp("comp", (OVar("phi"), OVar("x"))),))
            results.append((rhs, "Mathlib: FirstOrder_Language_Embedding_map_fun"))
        except Exception:
            pass
    return results


def _r0392_map_constants(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Embedding.map_constants
    # φ c = c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: FirstOrder_Language_Embedding_map_constants"))
        except Exception:
            pass
    return results


def _r0393_toHom_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Embedding.toHom_inj
    # f.toHom = g.toHom ↔ f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toHom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("g_toHom"), OVar("f"))), OVar("g")))
            results.append((rhs, "Mathlib: FirstOrder_Language_Embedding_toHom_inj"))
    except Exception:
        pass
    return results


def _r0394_ofInjective_toHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Embedding.ofInjective_toHom
    # (ofInjective hf).toHom = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofInjective_hf_toHom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: FirstOrder_Language_Embedding_ofInjective_toHom"))
    except Exception:
        pass
    return results


def _r0395_refl_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Embedding.refl_apply
    # refl L M x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "refl", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: FirstOrder_Language_Embedding_refl_apply"))
        except Exception:
            pass
    return results


def _r0396_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Embedding.comp_apply
    # g.comp f x = g (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_comp", 2)
    if args is not None:
        try:
            rhs = OOp("g", (OOp("f", (args[1],)),))
            results.append((rhs, "Mathlib: FirstOrder_Language_Embedding_comp_apply"))
        except Exception:
            pass
    return results


def _r0397_comp_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Embedding.comp_assoc
    # (h.comp g).comp f = h.comp (g.comp f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_comp_g_comp", 1)
    if args is not None:
        try:
            rhs = OOp("h_comp", (OOp("g_comp", (args[0],)),))
            results.append((rhs, "Mathlib: FirstOrder_Language_Embedding_comp_assoc"))
        except Exception:
            pass
    return results


def _r0398_comp_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Embedding.comp_inj
    # h.comp f = h.comp g ↔ f = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_comp", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("h_comp", (OVar("g"),)), args[0])), OVar("g")))
            results.append((rhs, "Mathlib: FirstOrder_Language_Embedding_comp_inj"))
        except Exception:
            pass
    return results


def _r0399_toHom_comp_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Embedding.toHom_comp_inj
    # h.toHom.comp f = h.toHom.comp g ↔ f = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_toHom_comp", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("h_toHom_comp", (OVar("g"),)), args[0])), OVar("g")))
            results.append((rhs, "Mathlib: FirstOrder_Language_Embedding_toHom_comp_inj"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_function rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("*", "**", "+", "-", "//", "<=", ">", "C", "ContDiff", "D", "Directed", "Equiv_swap", "Equiv_symm", "Fin_cons", "FromTypes", "Function_Embedding_sigmaSet", "Function_Embedding_sumSet", "Function_extend", "Function_update", "I_cocomplex_d", "I_i", "I_i_f", "I_iso_inv", "Ico", "Involutive", "Ioc", "IsFixedPt", "IsPartialInv", "Iterate_rec", "LeftInverse", "MeromorphicOn_divisor", "N", "N_pipe_h_eq_gt_DFunLike_ext_prime_iff_mpr_h_at_ext_theorem_ext_f_g_colon_M_L_N_h", "OfArity", "Prod_map", "RightInverse", "Semiconj", "Set_range", "Set_range_f_restrict", "Sigma_map", "Sigma_mk", "Sum_elim", "Sum_map", "T", "_0", "_1", "_1_colon_B", "_unknown", "a", "ainv",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_function axioms."""
    if recognizes(term):
        return 0.8
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_function rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_mul_def(term, ctx))
    results.extend(_r0001_update_mul(term, ctx))
    results.extend(_r0002_mulSupport_inv(term, ctx))
    results.extend(_r0003_mulSupport_eq(term, ctx))
    results.extend(_r0004_mulSupport_const(term, ctx))
    results.extend(_r0005_funext(term, ctx))
    results.extend(_r0006_funext(term, ctx))
    results.extend(_r0007_uncurry_curry(term, ctx))
    results.extend(_r0008_curry_two_eq_curry(term, ctx))
    results.extend(_r0009_updateFinset_singleton(term, ctx))
    results.extend(_r0010_invFun_restrict(term, ctx))
    results.extend(_r0011_right_inv_of_invOfMemRange(term, ctx))
    results.extend(_r0012_invFun_restrict(term, ctx))
    results.extend(_r0013_list_map(term, ctx))
    results.extend(_r0014_graph_comp(term, ctx))
    results.extend(_r0015_invFunOn_apply_eq(term, ctx))
    results.extend(_r0016_mem_fixedPoints_iff(term, ctx))
    results.extend(_r0017_iterate_add_minimalPeriod_eq(term, ctx))
    results.extend(_r0018_periodicOrbit_eq_nil_iff_not_periodic_pt(term, ctx))
    results.extend(_r0019_coe_smul(term, ctx))
    results.extend(_r0020_mk_coe(term, ctx))
    results.extend(_r0021_coe_refl(term, ctx))
    results.extend(_r0022_coe_trans(term, ctx))
    results.extend(_r0023_mk_trans_mk(term, ctx))
    results.extend(_r0024_equiv_toEmbedding_trans_symm_toEmbedding(term, ctx))
    results.extend(_r0025_sumSet_preimage_inr(term, ctx))
    results.extend(_r0026_sumSet_range(term, ctx))
    results.extend(_r0027_toPerm_symm(term, ctx))
    results.extend(_r0028_toEquivRange_eq_ofInjective(term, ctx))
    results.extend(_r0029_eval_apply(term, ctx))
    results.extend(_r0030_onFun_apply(term, ctx))
    results.extend(_r0031_eq_rec_eq(term, ctx))
    results.extend(_r0032_const_succ(term, ctx))
    results.extend(_r0033_const_succ_apply(term, ctx))
    results.extend(_r0034_iterate_zero_apply(term, ctx))
    results.extend(_r0035_iterate_succ_apply(term, ctx))
    results.extend(_r0036_iterate_add(term, ctx))
    results.extend(_r0037_iterate_mul(term, ctx))
    results.extend(_r0038_ofArity_succ(term, ctx))
    results.extend(_r0039_const_succ(term, ctx))
    results.extend(_r0040_coe_injective(term, ctx))
    results.extend(_r0041_comp_toHom(term, ctx))
    results.extend(_r0042_refl_comp(term, ctx))
    results.extend(_r0043_refl_toHom(term, ctx))
    results.extend(_r0044_subtype_equivRange(term, ctx))
    results.extend(_r0045_X_zpow(term, ctx))
    results.extend(_r0046_negPart_apply(term, ctx))
    results.extend(_r0047_mul_smul(term, ctx))
    results.extend(_r0048_one_smul(term, ctx))
    results.extend(_r0049_fromCoset_eq_of_mem_range(term, ctx))
    results.extend(_r0050_tau_apply_infinity(term, ctx))
    results.extend(_r0051_tau_apply_fromCoset(term, ctx))
    results.extend(_r0052_tau_symm_apply_fromCoset(term, ctx))
    results.extend(_r0053_tau_symm_apply_infinity(term, ctx))
    results.extend(_r0054_g_apply_fromCoset(term, ctx))
    results.extend(_r0055_g_apply_infinity(term, ctx))
    results.extend(_r0056_h_apply_infinity(term, ctx))
    results.extend(_r0057_h_apply_fromCoset(term, ctx))
    results.extend(_r0058_h_apply_fromCoset_nin_range(term, ctx))
    results.extend(_r0059_agree(term, ctx))
    results.extend(_r0060_comp_eq(term, ctx))
    results.extend(_r0061_apply_apply_eq_one(term, ctx))
    results.extend(_r0062_comp_eq_one(term, ctx))
    results.extend(_r0063_monoidHom_ker_eq(term, ctx))
    results.extend(_r0064_monoidHom_comp_eq_zero(term, ctx))
    results.extend(_r0065_linearMap_ker_eq(term, ctx))
    results.extend(_r0066_linearMap_comp_eq_zero(term, ctx))
    results.extend(_r0067_linearEquivOfSurjective_symm_apply(term, ctx))
    results.extend(_r0068_exists_mem_Ico_0(term, ctx))
    results.extend(_r0069_exists_mem_Ico(term, ctx))
    results.extend(_r0070_exists_mem_Ioc(term, ctx))
    results.extend(_r0071_image_Ioc(term, ctx))
    results.extend(_r0072_image_Icc(term, ctx))
    results.extend(_r0073_image_uIcc(term, ctx))
    results.extend(_r0074_add_nat_mul_eq(term, ctx))
    results.extend(_r0075_sub_nat_mul_eq(term, ctx))
    results.extend(_r0076_nat_mul_sub_eq(term, ctx))
    results.extend(_r0077_smul_def(term, ctx))
    results.extend(_r0078_one_def(term, ctx))
    results.extend(_r0079_update_smul(term, ctx))
    results.extend(_r0080_extend_smul(term, ctx))
    results.extend(_r0081_map_eq_one_iff(term, ctx))
    results.extend(_r0082_extend_mul(term, ctx))
    results.extend(_r0083_extend_inv(term, ctx))
    results.extend(_r0084_extend_div(term, ctx))
    results.extend(_r0085_update_one(term, ctx))
    results.extend(_r0086_update_inv(term, ctx))
    results.extend(_r0087_update_div(term, ctx))
    results.extend(_r0088_const_eq_one(term, ctx))
    results.extend(_r0089_mulSupport_fun_inv(term, ctx))
    results.extend(_r0090_lieModule_lcs_map_eq(term, ctx))
    results.extend(_r0091_support_const_smul_of_ne_zero(term, ctx))
    results.extend(_r0092_support_smul(term, ctx))
    results.extend(_r0093_const_one(term, ctx))
    results.extend(_r0094_const_mul(term, ctx))
    results.extend(_r0095_const_inv(term, ctx))
    results.extend(_r0096_const_div(term, ctx))
    results.extend(_r0097_const_pow(term, ctx))
    results.extend(_r0098_mulSupport_eq_preimage(term, ctx))
    results.extend(_r0099_notMem_mulSupport(term, ctx))
    results.extend(_r0100_compl_mulSupport(term, ctx))
    results.extend(_r0101_mulSupport_eq_iff(term, ctx))
    results.extend(_r0102_ext_iff_mulSupport(term, ctx))
    results.extend(_r0103_mulSupport_update_of_ne_one(term, ctx))
    results.extend(_r0104_mulSupport_update_one(term, ctx))
    results.extend(_r0105_mulSupport_update_eq_ite(term, ctx))
    results.extend(_r0106_mulSupport_extend_one(term, ctx))
    results.extend(_r0107_mulSupport_eq_empty_iff(term, ctx))
    results.extend(_r0108_range_eq_image_or_of_mulSupport_subset(term, ctx))
    results.extend(_r0109_mulSupport_eq_univ(term, ctx))
    results.extend(_r0110_mulSupport_comp_eq(term, ctx))
    results.extend(_r0111_mulSupport_comp_eq_of_range_subset(term, ctx))
    results.extend(_r0112_mulSupport_comp_eq_preimage(term, ctx))
    results.extend(_r0113_mulSupport_prodMk(term, ctx))
    results.extend(_r0114_mulSupport_curry(term, ctx))
    results.extend(_r0115_mulSupport_fun_curry(term, ctx))
    results.extend(_r0116_iterate_two_mul(term, ctx))
    results.extend(_r0117_iterate_two_mul_add_one(term, ctx))
    results.extend(_r0118_iterate_even(term, ctx))
    results.extend(_r0119_iterate_odd(term, ctx))
    results.extend(_r0120_iterate_eq_self(term, ctx))
    results.extend(_r0121_iterate_eq_id(term, ctx))
    results.extend(_r0122_sub_eq(term, ctx))
    results.extend(_r0123_sub_nsmul_eq(term, ctx))
    results.extend(_r0124_sub_nat_mul_eq(term, ctx))
    results.extend(_r0125_nsmul_sub_eq(term, ctx))
    results.extend(_r0126_nat_mul_sub_eq(term, ctx))
    results.extend(_r0127_sub_zsmul_eq(term, ctx))
    results.extend(_r0128_sub_int_mul_eq(term, ctx))
    results.extend(_r0129_zsmul_sub_eq(term, ctx))
    results.extend(_r0130_int_mul_sub_eq(term, ctx))
    results.extend(_r0131_eq(term, ctx))
    results.extend(_r0132_neg_eq(term, ctx))
    results.extend(_r0133_nsmul_eq(term, ctx))
    results.extend(_r0134_nat_mul_eq(term, ctx))
    results.extend(_r0135_zsmul_eq(term, ctx))
    results.extend(_r0136_int_mul_eq(term, ctx))
    results.extend(_r0137_map_vadd_zmultiples(term, ctx))
    results.extend(_r0138_map_vadd_multiples(term, ctx))
    results.extend(_r0139_lift_coe(term, ctx))
    results.extend(_r0140_eq(term, ctx))
    results.extend(_r0141_sub_eq(term, ctx))
    results.extend(_r0142_neg_eq(term, ctx))
    results.extend(_r0143_nat_mul_eq_of_eq_zero(term, ctx))
    results.extend(_r0144_int_mul_eq_of_eq_zero(term, ctx))
    results.extend(_r0145_add_zsmul_eq(term, ctx))
    results.extend(_r0146_sub_zsmul_eq(term, ctx))
    results.extend(_r0147_zsmul_sub_eq(term, ctx))
    results.extend(_r0148_add_int_mul_eq(term, ctx))
    results.extend(_r0149_sub_int_mul_eq(term, ctx))
    results.extend(_r0150_int_mul_sub_eq(term, ctx))
    results.extend(_r0151_add_nsmul_eq(term, ctx))
    results.extend(_r0152_sub_nsmul_eq(term, ctx))
    results.extend(_r0153_nsmul_sub_eq(term, ctx))
    results.extend(_r0154_add_antiperiod_eq(term, ctx))
    results.extend(_r0155_sub_antiperiod_eq(term, ctx))
    results.extend(_r0156_update_star(term, ctx))
    results.extend(_r0157_star_sumElim(term, ctx))
    results.extend(_r0158_norm_qParam(term, ctx))
    results.extend(_r0159_im_invQParam(term, ctx))
    results.extend(_r0160_qParam_right_inv(term, ctx))
    results.extend(_r0161_qParam_left_inv_mod_period(term, ctx))
    results.extend(_r0162_zero_iff_logCounting_bounded(term, ctx))
    results.extend(_r0163_toClosedBall_eval_within(term, ctx))
    results.extend(_r0164_toClosedBall_divisor(term, ctx))
    results.extend(_r0165_logCounting_eval_zero(term, ctx))
    results.extend(_r0166_logCounting_single_eq_log_sub_const(term, ctx))
    results.extend(_r0167_logCounting_divisor_eq_circleAverage_sub(term, ctx))
    results.extend(_r0168_hasTemperateGrowth_iff_isBigO(term, ctx))
    results.extend(_r0169_isBigO(term, ctx))
    results.extend(_r0170_isBigO_uniform(term, ctx))
    results.extend(_r0171_toTemperedDistribution_apply(term, ctx))
    results.extend(_r0172_mulSupport(term, ctx))
    results.extend(_r0173_finprod_eq_fun(term, ctx))
    results.extend(_r0174_extractFactor(term, ctx))
    results.extend(_r0175_meromorphicOrderAt_eq(term, ctx))
    results.extend(_r0176_divisor(term, ctx))
    results.extend(_r0177_meromorphicTrailingCoeffAt_factorizedRat(term, ctx))
    results.extend(_r0178_meromorphicTrailingCoeffAt_factorizedRat(term, ctx))
    results.extend(_r0179_log_norm_meromorphicTrailingCoeffAt(term, ctx))
    results.extend(_r0180_update_exp(term, ctx))
    results.extend(_r0181_iso_hom_naturality(term, ctx))
    results.extend(_r0182_iso_inv_naturality(term, ctx))
    results.extend(_r0183_ofCocomplex_d_0_1(term, ctx))
    results.extend(_r0184_comp_factorThru(term, ctx))
    results.extend(_r0185_i_f_succ(term, ctx))
    results.extend(_r0186_i_f_zero_comp_complex_d(term, ctx))
    results.extend(_r0187_complex_d_comp(term, ctx))
    results.extend(_r0188_i_comp_hom(term, ctx))
    results.extend(_r0189_uncurry_apply_cons(term, ctx))
    results.extend(_r0190_uncurry_apply_succ(term, ctx))
    results.extend(_r0191_curry_apply_cons(term, ctx))
    results.extend(_r0192_curry_apply_succ(term, ctx))
    results.extend(_r0193_curry_uncurry(term, ctx))
    results.extend(_r0194_uncurry_curry(term, ctx))
    results.extend(_r0195_curry_two_eq_curry(term, ctx))
    results.extend(_r0196_uncurry_two_eq_uncurry(term, ctx))
    results.extend(_r0197_curry_uncurry(term, ctx))
    results.extend(_r0198_uncurry_two_eq_uncurry(term, ctx))
    results.extend(_r0199_embFinTwo_apply_zero(term, ctx))
    results.extend(_r0200_embFinTwo_apply_one(term, ctx))
    results.extend(_r0201_updateFinset_def(term, ctx))
    results.extend(_r0202_updateFinset_empty(term, ctx))
    results.extend(_r0203_update_eq_updateFinset(term, ctx))
    results.extend(_r0204_updateFinset_updateFinset(term, ctx))
    results.extend(_r0205_updateFinset_updateFinset_of_subset(term, ctx))
    results.extend(_r0206_restrict_updateFinset_of_subset(term, ctx))
    results.extend(_r0207_restrict_updateFinset(term, ctx))
    results.extend(_r0208_updateFinset_restrict(term, ctx))
    results.extend(_r0209_update_updateFinset(term, ctx))
    results.extend(_r0210_updateFinset_congr(term, ctx))
    results.extend(_r0211_updateFinset_univ(term, ctx))
    results.extend(_r0212_updateFinset_univ_apply(term, ctx))
    results.extend(_r0213_toEmbedding_equivOfFiniteSelfEmbedding(term, ctx))
    results.extend(_r0214_exists_of_card_eq_finset(term, ctx))
    results.extend(_r0215_left_inv_of_invOfMemRange(term, ctx))
    results.extend(_r0216_right_inv_of_invOfMemRange(term, ctx))
    results.extend(_r0217_left_inv_of_invOfMemRange(term, ctx))
    results.extend(_r0218_apply_eq_iff_eq(term, ctx))
    results.extend(_r0219_list_map(term, ctx))
    results.extend(_r0220_mem_graph(term, ctx))
    results.extend(_r0221_graph_inj(term, ctx))
    results.extend(_r0222_encard_image(term, ctx))
    results.extend(_r0223_card_le_card_add_one_iff(term, ctx))
    results.extend(_r0224_invFunOn_pos(term, ctx))
    results.extend(_r0225_invFunOn_eq(term, ctx))
    results.extend(_r0226_invFunOn_neg(term, ctx))
    results.extend(_r0227_update_comp_eq_of_notMem_range(term, ctx))
    results.extend(_r0228_insert_injOn(term, ctx))
    results.extend(_r0229_apply_eq_of_range_eq_singleton(term, ctx))
    results.extend(_r0230_image_eq_preimage_symm(term, ctx))
    results.extend(_r0231_preimage_image(term, ctx))
    results.extend(_r0232_image_preimage(term, ctx))
    results.extend(_r0233_range_comp(term, ctx))
    results.extend(_r0234_mem_range_iff_existsUnique(term, ctx))
    results.extend(_r0235_compl_image_eq(term, ctx))
    results.extend(_r0236_image_image(term, ctx))
    results.extend(_r0237_preimage_preimage(term, ctx))
    results.extend(_r0238_image_eq(term, ctx))
    results.extend(_r0239_iUnion_comp(term, ctx))
    results.extend(_r0240_iInter_comp(term, ctx))
    results.extend(_r0241_pullback_comm_sq(term, ctx))
    results.extend(_r0242_preimage_pullbackDiagonal(term, ctx))
    results.extend(_r0243_sigma_map(term, ctx))
    results.extend(_r0244_sumMap(term, ctx))
    results.extend(_r0245_birkhoffAverage_eq(term, ctx))
    results.extend(_r0246_birkhoffSum_eq(term, ctx))
    results.extend(_r0247_forall_isFixedPt_iff(term, ctx))
    results.extend(_r0248_eq(term, ctx))
    results.extend(_r0249_perm_zpow(term, ctx))
    results.extend(_r0250_fixedPoints_id(term, ctx))
    results.extend(_r0251_iterate_mod_apply(term, ctx))
    results.extend(_r0252_eq_of_apply_eq_same(term, ctx))
    results.extend(_r0253_eq_of_apply_eq(term, ctx))
    results.extend(_r0254_bUnion_ptsOfPeriod(term, ctx))
    results.extend(_r0255_iUnion_pnat_ptsOfPeriod(term, ctx))
    results.extend(_r0256_iterate_minimalPeriod(term, ctx))
    results.extend(_r0257_iterate_mod_minimalPeriod_eq(term, ctx))
    results.extend(_r0258_minimalPeriod_eq_zero_of_notMem_periodic(term, ctx))
    results.extend(_r0259_minimalPeriod_eq_zero_iff_notMem_periodi(term, ctx))
    results.extend(_r0260_minimalPeriod_apply_iterate(term, ctx))
    results.extend(_r0261_minimalPeriod_apply(term, ctx))
    results.extend(_r0262_iterate_eq_iterate_iff_of_lt_minimalPeri(term, ctx))
    results.extend(_r0263_minimalPeriod_id(term, ctx))
    results.extend(_r0264_minimalPeriod_eq_one_iff_isFixedPt(term, ctx))
    results.extend(_r0265_minimalPeriod_eq_one_of_subsingleton(term, ctx))
    results.extend(_r0266_eq_zero_of_lt_minimalPeriod(term, ctx))
    results.extend(_r0267_not_isPeriodicPt_of_pos_of_lt_minimalPer(term, ctx))
    results.extend(_r0268_minimalPeriod_eq_minimalPeriod_iff(term, ctx))
    results.extend(_r0269_minimalPeriod_iterate_eq_div_gcd_aux(term, ctx))
    results.extend(_r0270_minimalPeriod_iterate_eq_div_gcd(term, ctx))
    results.extend(_r0271_periodicOrbit_def(term, ctx))
    results.extend(_r0272_periodicOrbit_eq_cycle_map(term, ctx))
    results.extend(_r0273_periodicOrbit_length(term, ctx))
    results.extend(_r0274_periodicOrbit_eq_nil_of_not_periodic_pt(term, ctx))
    results.extend(_r0275_mem_periodicOrbit_iff(term, ctx))
    results.extend(_r0276_exists_iterate_apply_eq_of_mem_periodicP(term, ctx))
    results.extend(_r0277_periodicOrbit_apply_iterate_eq(term, ctx))
    results.extend(_r0278_periodicOrbit_apply_eq(term, ctx))
    results.extend(_r0279_directed_ptsOfPeriod_pnat(term, ctx))
    results.extend(_r0280_minimalPeriod_eq_prime_iff(term, ctx))
    results.extend(_r0281_minimalPeriod_eq_sInf_n_pos_IsPeriodicPt(term, ctx))
    results.extend(_r0282_minimalPeriod_eq_prime(term, ctx))
    results.extend(_r0283_minimalPeriod_eq_prime_pow(term, ctx))
    results.extend(_r0284_minimalPeriod_of_comp_eq_mul_of_coprime(term, ctx))
    results.extend(_r0285_injective_iff_periodicPts_eq_univ(term, ctx))
    results.extend(_r0286_injective_iff_iterate_factorial_card_eq(term, ctx))
    results.extend(_r0287_minimalPeriod_prodMap(term, ctx))
    results.extend(_r0288_preimage_dynEntourage(term, ctx))
    results.extend(_r0289_smul_def(term, ctx))
    results.extend(_r0290_smul_apply(term, ctx))
    results.extend(_r0291_mulActionHom_embedding_apply(term, ctx))
    results.extend(_r0292_ext(term, ctx))
    results.extend(_r0293_toFun_eq_coe(term, ctx))
    results.extend(_r0294_apply_eq_iff_eq(term, ctx))
    results.extend(_r0295_mk_id(term, ctx))
    results.extend(_r0296_equiv_symm_toEmbedding_trans_toEmbedding(term, ctx))
    results.extend(_r0297_setValue_eq(term, ctx))
    results.extend(_r0298_setValue_eq_iff(term, ctx))
    results.extend(_r0299_setValue_eq_of_ne(term, ctx))
    results.extend(_r0300_setValue_right_apply_eq(term, ctx))
    results.extend(_r0301_subtype_apply(term, ctx))
    results.extend(_r0302_coe_subtype(term, ctx))
    results.extend(_r0303_coe_quotientOut(term, ctx))
    results.extend(_r0304_coe_prodMap(term, ctx))
    results.extend(_r0305_coe_sumMap(term, ctx))
    results.extend(_r0306_codRestrict_apply(term, ctx))
    results.extend(_r0307_sumSet_preimage_inl(term, ctx))
    results.extend(_r0308_sigmaSet_preimage(term, ctx))
    results.extend(_r0309_sigmaSet_range(term, ctx))
    results.extend(_r0310_symm_eq_self_of_involutive(term, ctx))
    results.extend(_r0311_map_swap(term, ctx))
    results.extend(_r0312_swap_apply(term, ctx))
    results.extend(_r0313_swap_comp(term, ctx))
    results.extend(_r0314_update_comp_equiv(term, ctx))
    results.extend(_r0315_update_apply_equiv_apply(term, ctx))
    results.extend(_r0316_toEquivRange_apply(term, ctx))
    results.extend(_r0317_toEquivRange_symm_apply_self(term, ctx))
    results.extend(_r0318_const_def(term, ctx))
    results.extend(_r0319_const_inj(term, ctx))
    results.extend(_r0320_funext_iff_of_subsingleton(term, ctx))
    results.extend(_r0321_not_injective_iff(term, ctx))
    results.extend(_r0322_right_cancellable(term, ctx))
    results.extend(_r0323_bijective_iff_existsUnique(term, ctx))
    results.extend(_r0324_existsUnique(term, ctx))
    results.extend(_r0325_exists_fixed_point_of_surjective(term, ctx))
    results.extend(_r0326_cantor_injective(term, ctx))
    results.extend(_r0327_eq(term, ctx))
    results.extend(_r0328_get_eq(term, ctx))
    results.extend(_r0329_injective_of_isPartialInv_right(term, ctx))
    results.extend(_r0330_eq(term, ctx))
    results.extend(_r0331_eq(term, ctx))
    results.extend(_r0332_comp_eq_id(term, ctx))
    results.extend(_r0333_leftInverse_iff_comp(term, ctx))
    results.extend(_r0334_comp_eq_id(term, ctx))
    results.extend(_r0335_rightInverse_iff_comp(term, ctx))
    results.extend(_r0336_eq_rightInverse(term, ctx))
    results.extend(_r0337_isPartialInv(term, ctx))
    results.extend(_r0338_partialInv_left(term, ctx))
    results.extend(_r0339_extend_apply(term, ctx))
    results.extend(_r0340_extend_comp(term, ctx))
    results.extend(_r0341_eq_iff(term, ctx))
    results.extend(_r0342_eq_rec_on_eq(term, ctx))
    results.extend(_r0343_cast_eq(term, ctx))
    results.extend(_r0344_condition(term, ctx))
    results.extend(_r0345_desc_mk(term, ctx))
    results.extend(_r0346_semiconj_iff_comp_eq(term, ctx))
    results.extend(_r0347_eq(term, ctx))
    results.extend(_r0348_option_map(term, ctx))
    results.extend(_r0349_eq(term, ctx))
    results.extend(_r0350_comp_eq(term, ctx))
    results.extend(_r0351_flip_def(term, ctx))
    results.extend(_r0352_swap_def(term, ctx))
    results.extend(_r0353_comp_assoc(term, ctx))
    results.extend(_r0354_comp(term, ctx))
    results.extend(_r0355_beq_eq(term, ctx))
    results.extend(_r0356_eq_fiber_image(term, ctx))
    results.extend(_r0357_map_eq_image(term, ctx))
    results.extend(_r0358_mk_image(term, ctx))
    results.extend(_r0359_mem_iff_eq_image(term, ctx))
    results.extend(_r0360_map_preimage_eq_image(term, ctx))
    results.extend(_r0361_map_preimage_eq_image_map(term, ctx))
    results.extend(_r0362_image_eq_image_mk(term, ctx))
    results.extend(_r0363_fromTypes_zero(term, ctx))
    results.extend(_r0364_fromTypes_nil(term, ctx))
    results.extend(_r0365_fromTypes_succ(term, ctx))
    results.extend(_r0366_fromTypes_cons(term, ctx))
    results.extend(_r0367_const_zero(term, ctx))
    results.extend(_r0368_iterate_zero(term, ctx))
    results.extend(_r0369_iterate_succ(term, ctx))
    results.extend(_r0370_iterate_add_apply(term, ctx))
    results.extend(_r0371_iterate_one(term, ctx))
    results.extend(_r0372_iterate_fixed(term, ctx))
    results.extend(_r0373_iterate_invariant(term, ctx))
    results.extend(_r0374_iterate_eq_of_map_eq(term, ctx))
    results.extend(_r0375_comp_iterate(term, ctx))
    results.extend(_r0376_iterate_pred_comp_of_pos(term, ctx))
    results.extend(_r0377_comp_iterate_pred_of_pos(term, ctx))
    results.extend(_r0378_rec_zero(term, ctx))
    results.extend(_r0379_iterate_comm(term, ctx))
    results.extend(_r0380_iterate_add_eq_iterate(term, ctx))
    results.extend(_r0381_iterate_cancel(term, ctx))
    results.extend(_r0382_involutive_iff_iter_2_eq_id(term, ctx))
    results.extend(_r0383_ofArity_zero(term, ctx))
    results.extend(_r0384_const_zero(term, ctx))
    results.extend(_r0385_const_succ_apply(term, ctx))
    results.extend(_r0386_fromTypes_fin_const(term, ctx))
    results.extend(_r0387_extend_of_isEmpty(term, ctx))
    results.extend(_r0388_intervalIntegral_add_eq(term, ctx))
    results.extend(_r0389_intervalIntegral_add_eq_add(term, ctx))
    results.extend(_r0390_intervalIntegral_add_zsmul_eq(term, ctx))
    results.extend(_r0391_map_fun(term, ctx))
    results.extend(_r0392_map_constants(term, ctx))
    results.extend(_r0393_toHom_inj(term, ctx))
    results.extend(_r0394_ofInjective_toHom(term, ctx))
    results.extend(_r0395_refl_apply(term, ctx))
    results.extend(_r0396_comp_apply(term, ctx))
    results.extend(_r0397_comp_assoc(term, ctx))
    results.extend(_r0398_comp_inj(term, ctx))
    results.extend(_r0399_toHom_comp_inj(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_function rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("GrpCat_SurjectiveOfEpiAuxs_fromCoset_ne_of_nin_range", "fromCoset_b_f_hom_range_b_rfl_ne_fromCoset_f_hom_range_1_one_leftCoset", "Not an equality or iff proposition"),
    ("GrpCat_SurjectiveOfEpiAuxs_tau_apply_fromCoset", "_unknown", "Empty proposition"),
    ("GrpCat_SurjectiveOfEpiAuxs_h_apply_fromCoset", "_unknown", "Empty proposition"),
    ("GrpCat_SurjectiveOfEpiAuxs_g_ne_h", "g_ne_h", "Not an equality or iff proposition"),
    ("Function_MulExact_of_comp_of_mem_range", "MulExact_f_g", "Not an equality or iff proposition"),
    ("Function_MulExact_comp_injective", "MulExact_f_g_prime_comp_g", "Not an equality or iff proposition"),
    ("Function_MulExact_of_comp_eq_one_of_ker_in_range", "MulExact_f_g", "Not an equality or iff proposition"),
    ("Function_MulExact_iff_rangeFactorization", "letI_colon_One_Set_range_g", "Not an equality or iff proposition"),
    ("Function_MulExact_rangeFactorization", "letI_colon_One_Set_range_g", "Not an equality or iff proposition"),
    ("Function_MulExact_of_ladder_mulEquiv_of_mulExact", "MulExact_g_1_2_g_2_3", "Not an equality or iff proposition"),
    ("Function_MulExact_of_ladder_mulEquiv_of_mulExact", "_unknown", "Empty proposition"),
    ("Function_Exact_of_ladder_linearEquiv_of_exact", "Exact_g_1_2_g_2_3", "Not an equality or iff proposition"),
    ("Function_Exact_split_tfae", "_unknown", "Empty proposition"),
    ("Function_Exact_split_tfae", "List_TFAE_exists_l_g_comp_l_eq_LinearMap_id_exists_l_l_comp_f_eq_LinearMap_id", "Not an equality or iff proposition"),
    ("Function_Periodic_const_smul_0", "Periodic_fun_x_eq_gt_f_a_x_ainv_c", "Not an equality or iff proposition"),
    ("Function_Periodic_const_mul", "Periodic_fun_x_eq_gt_f_a_star_x_ainv_star_c", "Not an equality or iff proposition"),
    ("Function_Periodic_const_inv_smul_0", "Periodic_fun_x_eq_gt_f_ainv_x_a_c", "Not an equality or iff proposition"),
    ("Function_Periodic_const_inv_mul", "Periodic_fun_x_eq_gt_f_ainv_star_x_a_star_c", "Not an equality or iff proposition"),
    ("Function_Periodic_mul_const", "Periodic_fun_x_eq_gt_f_x_star_a_c_star_ainv", "Not an equality or iff proposition"),
    ("Function_Periodic_mul_const", "_unknown", "Empty proposition"),
    ("Function_Periodic_mul_const_inv", "Periodic_fun_x_eq_gt_f_x_star_ainv_c_star_a", "Not an equality or iff proposition"),
    ("Function_Periodic_div_const", "Periodic_fun_x_eq_gt_f_x_slash_a_c_star_a", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_const_smul_0", "Antiperiodic_fun_x_eq_gt_f_a_x_ainv_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_const_mul", "Antiperiodic_fun_x_eq_gt_f_a_star_x_ainv_star_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_const_inv_smul_0", "Antiperiodic_fun_x_eq_gt_f_ainv_x_a_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_const_inv_mul", "Antiperiodic_fun_x_eq_gt_f_ainv_star_x_a_star_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_mul_const", "Antiperiodic_fun_x_eq_gt_f_x_star_a_c_star_ainv", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_mul_const", "_unknown", "Empty proposition"),
    ("Function_Antiperiodic_mul_const_inv", "Antiperiodic_fun_x_eq_gt_f_x_star_ainv_c_star_a", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_div_inv", "Antiperiodic_fun_x_eq_gt_f_x_slash_a_c_star_a", "Not an equality or iff proposition"),
    ("Function_hasFiniteMulSupport_fun_one", "HasFiniteMulSupport_1_colon_a_to_M", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_fun_comp", "HasFiniteMulSupport_fun_a_g_f_a", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_comp", "HasFiniteMulSupport_g_comp_f", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_fst", "HasFiniteMulSupport_fun_a_f_a_fst", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_snd", "HasFiniteMulSupport_fun_a_f_a_snd", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_prodMk", "HasFiniteMulSupport_fun_a_f_a_g_a", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_mul", "HasFiniteMulSupport_f_star_g", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_inv", "HasFiniteMulSupport_finv", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_prod", "HasFiniteMulSupport_fun_a_i_in_s_f_i_a", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_div", "HasFiniteMulSupport_f_slash_g", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_pow", "HasFiniteMulSupport_f_pow_n", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_zpow", "HasFiniteMulSupport_f_pow_n", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_max", "HasFiniteMulSupport_fun_a_max_f_a_g_a", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_min", "HasFiniteMulSupport_fun_a_min_f_a_g_a", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_sup", "HasFiniteMulSupport_fun_a_f_a_g_a", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_inf", "HasFiniteMulSupport_fun_a_f_a_g_a", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_iSup", "HasFiniteMulSupport_fun_a_i_f_i_a", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_iInf", "HasFiniteMulSupport_fun_a_i_f_i_a", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_pi", "HasFiniteMulSupport_f", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_sup", "_unknown", "Empty proposition"),
    ("Function_HasFiniteMulSupport_inf", "_unknown", "Empty proposition"),
    ("Function_HasFiniteMulSupport_comp_of_injective", "f_comp_g_HasFiniteMulSupport", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_fun_comp_of_injective", "fun_a_f_g_a_HasFiniteMulSupport", "Not an equality or iff proposition"),
    ("Function_HasFiniteMulSupport_of_comp", "g_HasFiniteMulSupport", "Not an equality or iff proposition"),
    ("Function_hasFiniteMulSupport_one", "HasFiniteMulSupport_fun_colon_a_1_colon_M", "Not an equality or iff proposition"),
    ("Function_Injective_smulCommClass", "SMulCommClass_M_N_a", "Not an equality or iff proposition"),
    ("Function_Surjective_smulCommClass", "SMulCommClass_M_N_b", "Not an equality or iff proposition"),
    ("Function_Even_const", "Function_Even_fun_colon_a_b", "Not an equality or iff proposition"),
    ("Function_Even_zero", "Function_Even_fun_colon_a_0_colon_b", "Not an equality or iff proposition"),
    ("Function_Odd_zero", "Function_Odd_fun_colon_a_0_colon_b", "Not an equality or iff proposition"),
    ("Function_Even_left_comp", "f_comp_g_Even", "Not an equality or iff proposition"),
    ("Function_Even_comp_odd", "f_comp_g_Even", "Not an equality or iff proposition"),
    ("Function_Odd_comp_odd", "f_comp_g_Odd", "Not an equality or iff proposition"),
    ("Function_Injective_isMulTorsionFree", "IsMulTorsionFree_M", "Not an equality or iff proposition"),
    ("Function_Surjective_mul_comm", "IsMulCommutative_N", "Not an equality or iff proposition"),
    ("Function_Injective_isLeftCancelMul", "IsLeftCancelMul_M_1", "Not an equality or iff proposition"),
    ("Function_Injective_isRightCancelMul", "IsRightCancelMul_M_1", "Not an equality or iff proposition"),
    ("Function_Injective_isCancelMul", "IsCancelMul_M_1", "Not an equality or iff proposition"),
    ("Function_extend_one", "Function_extend_f_1_colon_a_to_g_1_colon_b_to_g_eq_1", "Not an equality or iff proposition"),
    ("Function_mulSupport_mul", "mulSupport_fun_x_f_x_star_g_x_sub_mulSupport_f_union_mulSupport_g", "Not an equality or iff proposition"),
    ("Function_mulSupport_pow", "mulSupport_fun_x_eq_gt_f_x_pow_n_sub_mulSupport_f", "Not an equality or iff proposition"),
    ("Function_mulSupport_mul_inv", "mulSupport_fun_x_eq_gt_f_x_star_g_x_inv_sub_mulSupport_f_union_mulSupport_g", "Not an equality or iff proposition"),
    ("Function_mulSupport_div", "mulSupport_fun_x_eq_gt_f_x_slash_g_x_sub_mulSupport_f_union_mulSupport_g", "Not an equality or iff proposition"),
    ("Function_support_one", "support_1_colon_i_to_R_eq_univ", "Not an equality or iff proposition"),
    ("Function_mulSupport_zero", "mulSupport_0_colon_i_to_R_eq_univ", "Not an equality or iff proposition"),
    ("Function_Injective_noZeroDivisors", "NoZeroDivisors_M_0", "Not an equality or iff proposition"),
    ("Function_Injective_isLeftCancelMulZero", "IsLeftCancelMulZero_M_0", "Not an equality or iff proposition"),
    ("Function_Injective_isRightCancelMulZero", "IsRightCancelMulZero_M_0", "Not an equality or iff proposition"),
    ("Function_Injective_isCancelMulZero", "IsCancelMulZero_M_0", "Not an equality or iff proposition"),
    ("Function_Injective_isLieAbelian", "IsLieAbelian_L_1", "Not an equality or iff proposition"),
    ("Function_Surjective_isLieAbelian", "IsLieAbelian_L_2", "Not an equality or iff proposition"),
    ("Function_Surjective_isEngelian", "LieAlgebra_IsEngelian_u_1_u_3_u_4_R_L_2", "Not an equality or iff proposition"),
    ("Function_Injective_lieModuleIsNilpotent", "IsNilpotent_L_M", "Not an equality or iff proposition"),
    ("Function_Surjective_lieModuleIsNilpotent", "IsNilpotent_L_2_M_2", "Not an equality or iff proposition"),
    ("Function_Injective_lieAlgebra_isNilpotent", "IsNilpotent_L", "Not an equality or iff proposition"),
    ("Function_Surjective_lieAlgebra_isNilpotent", "IsNilpotent_L_prime", "Not an equality or iff proposition"),
    ("Function_Injective_lieAlgebra_isSolvable", "IsSolvable_L_prime", "Not an equality or iff proposition"),
    ("Function_Surjective_lieAlgebra_isSolvable", "IsSolvable_L", "Not an equality or iff proposition"),
    ("Function_support_smul_subset_left", "support_f_g_sub_support_f", "Not an equality or iff proposition"),
    ("Function_support_smul_subset_right", "support_f_g_sub_support_g", "Not an equality or iff proposition"),
    ("Function_support_const_smul_subset", "support_a_f_sub_support_f", "Not an equality or iff proposition"),
    ("Function_Surjective_injective_linearMapComp_right", "Injective_fun_f_colon_M_2_to_sig_2_3_M_3_f_comp_g", "Not an equality or iff proposition"),
    ("Function_Injective_injective_linearMapComp_left", "Injective_fun_g_colon_M_1_to_sig_1_2_M_2_f_comp_g", "Not an equality or iff proposition"),
    ("Function_Injective_moduleIsTorsionFree", "IsTorsionFree_R_M", "Not an equality or iff proposition"),
    ("Function_Injective_noZeroSMulDivisors", "NoZeroSMulDivisors_R_M", "Not an equality or iff proposition"),
    ("Function_mulSupport_along_fiber_finite_of_finite", "HasFiniteMulSupport_fun_b_f_a_b", "Not an equality or iff proposition"),
    ("Function_mulSupport_subset_iff", "_unknown", "Empty proposition"),
    ("Function_mulSupport_extend_one_subset", "mulSupport_f_extend_g_1_sub_f_prime_prime_mulSupport_g", "Not an equality or iff proposition"),
    ("Function_range_subset_insert_image_mulSupport", "range_f_sub_insert_1_f_prime_prime_mulSupport_f", "Not an equality or iff proposition"),
    ("Function_mulSupport_one", "mulSupport_1_colon_i_to_M_eq_empty", "Not an equality or iff proposition"),
    ("Function_mulSupport_fun_one", "mulSupport_fun_1_colon_i_to_M_eq_empty", "Not an equality or iff proposition"),
    ("Function_mulSupport_binop_subset", "mulSupport_fun_x_op_f_x_g_x_sub_mulSupport_f_union_mulSupport_g", "Not an equality or iff proposition"),
    ("Function_mulSupport_comp_subset", "mulSupport_g_comp_f_sub_mulSupport_f", "Not an equality or iff proposition"),
    ("Function_mulSupport_subset_comp", "mulSupport_f_sub_mulSupport_g_comp_f", "Not an equality or iff proposition"),
    ("Function_mulSupport_prodMk", "_unknown", "Empty proposition"),
    ("Function_mulSupport_along_fiber_subset", "mulSupport_fun_j_f_i_j_sub_mulSupport_f_image_Prod_snd", "Not an equality or iff proposition"),
    ("Function_mulSupport_sup", "mulSupport_fun_x_f_x_g_x_sub_mulSupport_f_union_mulSupport_g", "Not an equality or iff proposition"),
    ("Function_mulSupport_inf", "mulSupport_fun_x_f_x_g_x_sub_mulSupport_f_union_mulSupport_g", "Not an equality or iff proposition"),
    ("Function_mulSupport_max", "mulSupport_fun_x_max_f_x_g_x_sub_mulSupport_f_union_mulSupport_g", "Not an equality or iff proposition"),
    ("Function_mulSupport_min", "mulSupport_fun_x_min_f_x_g_x_sub_mulSupport_f_union_mulSupport_g", "Not an equality or iff proposition"),
    ("Function_mulSupport_iSup", "mulSupport_fun_x_i_f_i_x_sub_i_mulSupport_f_i", "Not an equality or iff proposition"),
    ("Function_mulSupport_iInf", "mulSupport_fun_x_i_f_i_x_sub_i_mulSupport_f_i", "Not an equality or iff proposition"),
    ("Function_Injective_posMulMono", "PosMulMono_b", "Not an equality or iff proposition"),
    ("Function_Injective_mulPosMono", "MulPosMono_b", "Not an equality or iff proposition"),
    ("Function_Injective_posMulStrictMono", "PosMulStrictMono_b", "Not an equality or iff proposition"),
    ("Function_Injective_mulPosStrictMono", "MulPosStrictMono_b", "Not an equality or iff proposition"),
    ("Function_Injective_isOrderedMonoid", "IsOrderedMonoid_b", "Not an equality or iff proposition"),
    ("Function_Injective_isOrderedCancelMonoid", "IsOrderedCancelMonoid_b", "Not an equality or iff proposition"),
    ("Function_one_le_const_of_one_le", "_1_le_const_b_a", "Not an equality or iff proposition"),
    ("Function_const_le_one_of_le_one", "const_b_a_le_1", "Not an equality or iff proposition"),
    ("Function_Injective_isOrderedRing", "IsOrderedRing_S", "Not an equality or iff proposition"),
    ("Function_Injective_isStrictOrderedRing", "IsStrictOrderedRing_S", "Not an equality or iff proposition"),
    ("Function_support_natCast", "support_n_colon_a_to_R_eq_univ", "Not an equality or iff proposition"),
    ("Function_mulSupport_natCast", "mulSupport_n_colon_a_to_R_eq_univ", "Not an equality or iff proposition"),
    ("Function_Injective_isDomain", "IsDomain_b", "Not an equality or iff proposition"),
    ("Function_Injective_leftDistribClass", "LeftDistribClass_S", "Not an equality or iff proposition"),
    ("Function_Injective_rightDistribClass", "RightDistribClass_S", "Not an equality or iff proposition"),
    ("Function_Surjective_leftDistribClass", "LeftDistribClass_S", "Not an equality or iff proposition"),
    ("Function_Surjective_rightDistribClass", "RightDistribClass_S", "Not an equality or iff proposition"),
    ("Function_Periodic_comp", "Periodic_g_comp_f_c", "Not an equality or iff proposition"),
    ("Function_Periodic_comp_addHom", "Periodic_f_comp_g_g_inv_c", "Not an equality or iff proposition"),
    ("Function_Periodic_mul", "Periodic_f_star_g_c", "Not an equality or iff proposition"),
    ("Function_Periodic_div", "Periodic_f_slash_g_c", "Not an equality or iff proposition"),
    ("List_periodic_prod", "Periodic_l_prod_c", "Not an equality or iff proposition"),
    ("Multiset_periodic_prod", "Periodic_s_prod_c", "Not an equality or iff proposition"),
    ("Finset_periodic_prod", "Periodic_i_in_s_f_i_c", "Not an equality or iff proposition"),
    ("Function_Periodic_smul", "Periodic_a_f_c", "Not an equality or iff proposition"),
    ("Function_Periodic_const_smul", "Periodic_fun_x_eq_gt_f_a_x_ainv_c", "Not an equality or iff proposition"),
    ("Function_Periodic_const_inv_smul", "Periodic_fun_x_eq_gt_f_ainv_x_a_c", "Not an equality or iff proposition"),
    ("Function_Periodic_add_period", "Periodic_f_c_1_plus_c_2", "Not an equality or iff proposition"),
    ("Function_Periodic_sub_eq", "_unknown", "Empty proposition"),
    ("Function_Periodic_neg", "Periodic_f_minus_c", "Not an equality or iff proposition"),
    ("Function_Periodic_sub_period", "Periodic_f_c_1_minus_c_2", "Not an equality or iff proposition"),
    ("Function_Periodic_const_add", "Periodic_fun_x_eq_gt_f_a_plus_x_c", "Not an equality or iff proposition"),
    ("Function_Periodic_add_const", "Periodic_fun_x_eq_gt_f_x_plus_a_c", "Not an equality or iff proposition"),
    ("Function_Periodic_const_sub", "Periodic_fun_x_eq_gt_f_a_minus_x_c", "Not an equality or iff proposition"),
    ("Function_Periodic_sub_const", "Periodic_fun_x_eq_gt_f_x_minus_a_c", "Not an equality or iff proposition"),
    ("Function_Periodic_nsmul", "Periodic_f_n_c", "Not an equality or iff proposition"),
    ("Function_Periodic_nat_mul", "Periodic_f_n_star_c", "Not an equality or iff proposition"),
    ("Function_Periodic_neg_nsmul", "Periodic_f_minus_n_c", "Not an equality or iff proposition"),
    ("Function_Periodic_neg_nat_mul", "Periodic_f_minus_n_star_c", "Not an equality or iff proposition"),
    ("Function_Periodic_zsmul", "Periodic_f_n_c", "Not an equality or iff proposition"),
    ("Function_Periodic_int_mul", "Periodic_f_n_star_c", "Not an equality or iff proposition"),
    ("Function_periodic_with_period_zero", "Periodic_f_0", "Not an equality or iff proposition"),
    ("Function_Periodic_not_injective", "not_Injective_f", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_funext", "_unknown", "Empty proposition"),
    ("Function_Antiperiodic_periodic", "Periodic_f_2_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_periodic_two_mul", "Periodic_f_2_star_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_even_nsmul_periodic", "Periodic_f_2_star_n_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_nat_even_mul_periodic", "Periodic_f_n_star_2_star_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_odd_nsmul_antiperiodic", "Antiperiodic_f_2_star_n_plus_1_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_nat_odd_mul_antiperiodic", "Antiperiodic_f_n_star_2_star_c_plus_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_even_zsmul_periodic", "Periodic_f_2_star_n_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_int_even_mul_periodic", "Periodic_f_n_star_2_star_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_odd_zsmul_antiperiodic", "Antiperiodic_f_2_star_n_plus_1_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_int_odd_mul_antiperiodic", "Antiperiodic_f_n_star_2_star_c_plus_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_sub_eq", "_unknown", "Empty proposition"),
    ("Function_Antiperiodic_neg", "Antiperiodic_f_minus_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_const_add", "Antiperiodic_fun_x_eq_gt_f_a_plus_x_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_add_const", "Antiperiodic_fun_x_eq_gt_f_x_plus_a_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_const_sub", "Antiperiodic_fun_x_eq_gt_f_a_minus_x_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_sub_const", "Antiperiodic_fun_x_eq_gt_f_x_minus_a_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_smul", "Antiperiodic_a_f_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_const_smul", "Antiperiodic_fun_x_eq_gt_f_a_x_ainv_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_const_inv_smul", "Antiperiodic_fun_x_eq_gt_f_ainv_x_a_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_add", "Periodic_f_c_1_plus_c_2", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_sub", "Periodic_f_c_1_minus_c_2", "Not an equality or iff proposition"),
    ("Function_Periodic_add_antiperiod", "Antiperiodic_f_c_1_plus_c_2", "Not an equality or iff proposition"),
    ("Function_Periodic_sub_antiperiod", "Antiperiodic_f_c_1_minus_c_2", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_mul", "Periodic_f_star_g_c", "Not an equality or iff proposition"),
    ("Function_Antiperiodic_div", "Periodic_f_slash_g_c", "Not an equality or iff proposition"),
    ("Surjective_of_comp", "Surjective_g", "Not an equality or iff proposition"),
    ("Surjective_sigmaDesc_of_union_range_eq_univ", "Surjective_Limits_Sigma_desc_f", "Not an equality or iff proposition"),
    ("Function_Periodic_qParam_ne_zero", "h_z_ne_0", "Not an equality or iff proposition"),
    ("Function_Periodic_continuous_qParam", "Continuous_h", "Not an equality or iff proposition"),
    ("Function_Periodic_differentiable_qParam", "Differentiable_h", "Not an equality or iff proposition"),
    ("Function_Periodic_contDiff_qParam", "ContDiff_m_h", "Not an equality or iff proposition"),
    ("Function_Periodic_qParam_tendsto", "Tendsto_qParam_h_Iinf_ne_0", "Not an equality or iff proposition"),
    ("Function_Periodic_invQParam_tendsto", "Tendsto_invQParam_h_ne_0_Iinf", "Not an equality or iff proposition"),
    ("Function_Periodic_im_invQParam_pos_of_norm_lt_one", "_0_lt_im_Periodic_invQParam_h_q", "Not an equality or iff proposition"),
    ("Function_Periodic_norm_qParam_le_of_one_half_le_im", "_1_xi_le_rexp_minus_pi", "Not an equality or iff proposition"),
    ("Function_locallyFinsuppWithin_one_isLittleO_logCounting_single", "_1_colon_to_eq_o_atTop_logCounting_single_e_1", "Not an equality or iff proposition"),
    ("Function_locallyFinsuppWithin_toClosedBall_support_subset_closedBall", "toClosedBall_r_f_support_sub_closedBall_0_pipe_rpipe", "Not an equality or iff proposition"),
    ("Function_locallyFinsuppWithin_logCounting_even", "logCounting_D_Even", "Not an equality or iff proposition"),
    ("Function_locallyFinsuppWithin_logCounting_mono", "MonotoneOn_logCounting_D_Ioi_0", "Not an equality or iff proposition"),
    ("Function_locallyFinsuppWithin_logCounting_strictMono", "StrictMonoOn_logCounting_D_Ioi_e", "Not an equality or iff proposition"),
    ("Function_locallyFinsuppWithin_logCounting_nonneg", "_0_le_logCounting_f_r", "Not an equality or iff proposition"),
    ("Function_locallyFinsuppWithin_logCounting_le", "logCounting_f_1_r_le_logCounting_f_2_r", "Not an equality or iff proposition"),
    ("Function_locallyFinsuppWithin_logCounting_eventuallyLE", "logCounting_f_1_le_atTop_logCounting_f_2", "Not an equality or iff proposition"),
    ("Function_HasTemperateGrowth_norm_iteratedFDeriv_le_uniform", "exists_k_colon_C_colon_0_le_C_and_forall_N_le_n_forall_x_colon_E_iteratedFDeriv_N_f_x_le_C_star_1_plus", "Not an equality or iff proposition"),
]
