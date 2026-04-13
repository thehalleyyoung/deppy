"""CCTT Axiom System — the 48 dichotomy path constructors.

Each axiom module provides:
  - apply(term, ctx) → List[(OTerm, str)]   forward rewrite
  - apply_inverse(term, ctx)                reverse rewrite
  - recognizes(term) → bool                 quick applicability check
  - relevance_score(term, other) → float    how likely to help

Axiom groups (monograph chapters 19-25):
  Control Flow  (D1-D8):   rec↔iter, beta, guards, fold fusion
  Data Structure (D9-D14):  stack↔rec, ADT, histogram, indexing
  Algorithm     (D15-D20):  BFS↔DFS, memo↔DP, greedy, Yoneda
  Language      (D21-D24):  dispatch, try↔cond, sort, η
  Control Flow Transforms (D25-D30): unroll, short-circuit, guards, fusion, fission, CPS
  Python Idioms (P13-P24): bool, slicing, sets, types, context, decorators, walrus, args, cmp, fmt, iter, copy
"""
from __future__ import annotations

from typing import Callable, Dict, List, Optional, Tuple

# ── Imports of axiom modules ───────────────────────────────────
from cctt.axioms import (
    d01_fold_unfold,
    d02_beta,
    d03_guard_reorder,
    d04_comp_fusion,
    d05_fold_universal,
    d06_lazy_eager,
    d07_tailrec,
    d08_section_merge,
    d09_stack_rec,
    d10_priority_queue,
    d11_adt,
    d12_map_construct,
    d13_histogram,
    d14_indexing,
    d15_traversal,
    d16_memo_dp,
    d17_assoc,
    d18_greedy,
    d19_sort_scan,
    d20_spec_unify,
    d21_dispatch,
    d22_effect_elim,
    d23_sort_process,
    d25_loop_unroll,
    d26_short_circuit,
    d27_early_return,
    d28_loop_fusion,
    d29_loop_fission,
    d30_cps,
    d37_distributivity,
    d38_partial_eval,
    d39_defunc,
    d40_curry,
    d41_monad,
    d42_generator,
    p13_bool_idioms,
    p14_slicing,
    p15_set_ops,
    p16_type_convert,
    p17_context,
    p18_decorators,
    p19_walrus,
    p20_args,
    p21_comparisons,
    p22_format,
    p23_iteration,
    p24_copy,
)

# Re-export the OTerm type for convenience
from cctt.denotation import OTerm
from cctt.path_search import FiberCtx

# ── Type alias for axiom apply functions ───────────────────────
AxiomFn = Callable[['OTerm', 'FiberCtx'], List[Tuple['OTerm', str]]]

# ── Module list (ordered by recommended application priority) ──
_AXIOM_MODULES = [
    d01_fold_unfold,
    d02_beta,
    d03_guard_reorder,
    d04_comp_fusion,
    d05_fold_universal,
    d06_lazy_eager,
    d07_tailrec,
    d08_section_merge,
    d09_stack_rec,
    d10_priority_queue,
    d11_adt,
    d12_map_construct,
    d13_histogram,
    d14_indexing,
    d15_traversal,
    d16_memo_dp,
    d17_assoc,
    d18_greedy,
    d19_sort_scan,
    d20_spec_unify,
    d21_dispatch,
    d22_effect_elim,
    d23_sort_process,
    d25_loop_unroll,
    d26_short_circuit,
    d27_early_return,
    d28_loop_fusion,
    d29_loop_fission,
    d30_cps,
    d37_distributivity,
    d38_partial_eval,
    d39_defunc,
    d40_curry,
    d41_monad,
    d42_generator,
    p13_bool_idioms,
    p14_slicing,
    p15_set_ops,
    p16_type_convert,
    p17_context,
    p18_decorators,
    p19_walrus,
    p20_args,
    p21_comparisons,
    p22_format,
    p23_iteration,
    p24_copy,
]

# ── ALL_AXIOMS: ordered list of (name, apply_fn) pairs ────────
ALL_AXIOMS: List[Tuple[str, AxiomFn]] = [
    (mod.AXIOM_NAME, mod.apply) for mod in _AXIOM_MODULES
]

# ── AXIOM_REGISTRY: name → module for direct lookup ───────────
AXIOM_REGISTRY: Dict[str, object] = {
    mod.AXIOM_NAME: mod for mod in _AXIOM_MODULES
}


def get_axiom(name: str) -> Optional[object]:
    """Look up an axiom module by its canonical name.

    Returns the module object or ``None`` if not found.

    >>> mod = get_axiom('d1_fold_unfold')
    >>> mod.AXIOM_NAME
    'd1_fold_unfold'
    """
    return AXIOM_REGISTRY.get(name)


def get_apply_fn(name: str) -> Optional[AxiomFn]:
    """Return the ``apply`` function for the named axiom."""
    mod = AXIOM_REGISTRY.get(name)
    if mod is not None:
        return mod.apply  # type: ignore[union-attr]
    return None


def all_rewrites(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply every registered axiom to *term* and collect all rewrites."""
    results: List[Tuple[OTerm, str]] = []
    for mod in _AXIOM_MODULES:
        results.extend(mod.apply(term, ctx))
    return results


def dependency_graph() -> Dict[str, List[str]]:
    """Return the inter-axiom dependency graph.

    Keys are axiom names; values are lists of axioms that should
    fire before the key axiom (``REQUIRES``) plus axioms that
    compose well with it (``COMPOSES_WITH``).
    """
    graph: Dict[str, List[str]] = {}
    for mod in _AXIOM_MODULES:
        name = mod.AXIOM_NAME
        requires = getattr(mod, 'REQUIRES', [])
        composes = getattr(mod, 'COMPOSES_WITH', [])
        graph[name] = list(set(requires + composes))
    return graph


__all__ = [
    'ALL_AXIOMS',
    'AXIOM_REGISTRY',
    'AxiomFn',
    'all_rewrites',
    'dependency_graph',
    'get_apply_fn',
    'get_axiom',
    # Sub-modules
    'd01_fold_unfold',
    'd02_beta',
    'd03_guard_reorder',
    'd04_comp_fusion',
    'd05_fold_universal',
    'd06_lazy_eager',
    'd07_tailrec',
    'd08_section_merge',
    'd09_stack_rec',
    'd10_priority_queue',
    'd11_adt',
    'd12_map_construct',
    'd13_histogram',
    'd14_indexing',
    'd15_traversal',
    'd16_memo_dp',
    'd17_assoc',
    'd18_greedy',
    'd19_sort_scan',
    'd20_spec_unify',
    'd21_dispatch',
    'd22_effect_elim',
    'd23_sort_process',
    'd25_loop_unroll',
    'd26_short_circuit',
    'd27_early_return',
    'd28_loop_fusion',
    'd29_loop_fission',
    'd30_cps',
    'd37_distributivity',
    'd38_partial_eval',
    'd39_defunc',
    'd40_curry',
    'd41_monad',
    'd42_generator',
    'p13_bool_idioms',
    'p14_slicing',
    'p15_set_ops',
    'p16_type_convert',
    'p17_context',
    'p18_decorators',
    'p19_walrus',
    'p20_args',
    'p21_comparisons',
    'p22_format',
    'p23_iteration',
    'p24_copy',
]
