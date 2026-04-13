"""CCTT Axiom System — 48 dichotomy + 48 Python-idiom path constructors.

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
  Extended (D31-D48): AOS↔SOA, sparse, encoding, precompute, strength-reduce, CSE,
                      distributivity, partial-eval, defunc, curry, monad, generator,
                      sliding-window, two-pointer, divide-conquer, string-build,
                      bitwise, DeMorgan
  Utility axioms: algebra, fold, case, quotient
  Python Idioms (P1-P48): comprehensions, builtins, dict-ops, string-ops, sort-variants,
                          itertools, collections, unpacking, exceptions, class-patterns,
                          functional, numeric, bool, slicing, sets, types, context,
                          decorators, walrus, args, comparisons, format, iteration, copy,
                          regex, pathlib, dataclasses, typing, async, serialization,
                          counter, property, metaclass, generator-coroutine,
                          map-filter-reduce, dict-merge, range-enumerate, zip-patterns,
                          any-all, flatten, string-build, conditional, math-ops,
                          heap-bisect, functools, operator, dunder, match
"""
from __future__ import annotations

from typing import Callable, Dict, List, Optional, Tuple

# ── Imports of axiom modules ───────────────────────────────────
from cctt.axioms import (
    # Core dichotomy axioms (D1-D24)
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
    d24_eta,
    # Extended control flow transforms (D25-D30)
    d25_loop_unroll,
    d26_short_circuit,
    d27_early_return,
    d28_loop_fusion,
    d29_loop_fission,
    d30_cps,
    # Extended data/algorithm axioms (D31-D48)
    d31_aos_soa,
    d32_sparse_dense,
    d33_encoding,
    d34_precompute,
    d35_strength_reduce,
    d36_cse,
    d37_distributivity,
    d38_partial_eval,
    d39_defunc,
    d40_curry,
    d41_monad,
    d42_generator,
    d43_sliding_window,
    d44_two_pointer,
    d45_divide_conquer,
    d46_string_build,
    d47_bitwise,
    d48_demorgan,
    # Utility axioms
    algebra,
    fold,
    case,
    quotient,
    # Python idiom axioms (P1-P48)
    p01_comprehension,
    p02_builtins,
    p03_dict_ops,
    p04_string_ops,
    p05_sort_variants,
    p06_itertools,
    p07_collections,
    p08_unpacking,
    p09_exceptions,
    p10_class_patterns,
    p11_functional,
    p12_numeric,
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
    p25_regex,
    p26_pathlib,
    p27_dataclasses,
    p28_typing,
    p29_async,
    p30_serialization,
    p31_counter,
    p32_property,
    p33_metaclass,
    p34_generator,
    p35_map_filter_reduce,
    p36_dict_merge,
    p37_range_enumerate,
    p38_zip_patterns,
    # Python idiom axioms (P39-P48)
    p39_any_all,
    p40_flatten,
    p41_string_build,
    p42_conditional,
    p43_math_ops,
    p44_heap_bisect,
    p45_functools,
    p46_operator,
    p47_dunder,
    p48_match,
)

# Re-export the OTerm type for convenience
from cctt.denotation import OTerm
from cctt.path_search import FiberCtx

# ── Type alias for axiom apply functions ───────────────────────
AxiomFn = Callable[['OTerm', 'FiberCtx'], List[Tuple['OTerm', str]]]

# ── Module list (ordered by recommended application priority) ──
_AXIOM_MODULES = [
    # Core dichotomy axioms (D1-D24)
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
    d24_eta,
    # Extended (D25-D48)
    d25_loop_unroll,
    d26_short_circuit,
    d27_early_return,
    d28_loop_fusion,
    d29_loop_fission,
    d30_cps,
    d31_aos_soa,
    d32_sparse_dense,
    d33_encoding,
    d34_precompute,
    d35_strength_reduce,
    d36_cse,
    d37_distributivity,
    d38_partial_eval,
    d39_defunc,
    d40_curry,
    d41_monad,
    d42_generator,
    d43_sliding_window,
    d44_two_pointer,
    d45_divide_conquer,
    d46_string_build,
    d47_bitwise,
    d48_demorgan,
    # Utility axioms
    algebra,
    fold,
    case,
    quotient,
    # Python idioms (P1-P48)
    p01_comprehension,
    p02_builtins,
    p03_dict_ops,
    p04_string_ops,
    p05_sort_variants,
    p06_itertools,
    p07_collections,
    p08_unpacking,
    p09_exceptions,
    p10_class_patterns,
    p11_functional,
    p12_numeric,
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
    p25_regex,
    p26_pathlib,
    p27_dataclasses,
    p28_typing,
    p29_async,
    p30_serialization,
    p31_counter,
    p32_property,
    p33_metaclass,
    p34_generator,
    p35_map_filter_reduce,
    p36_dict_merge,
    p37_range_enumerate,
    p38_zip_patterns,
    p39_any_all,
    p40_flatten,
    p41_string_build,
    p42_conditional,
    p43_math_ops,
    p44_heap_bisect,
    p45_functools,
    p46_operator,
    p47_dunder,
    p48_match,
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
    # Core dichotomy axiom modules (D1-D24)
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
    'd24_eta',
    # Extended (D25-D48)
    'd25_loop_unroll',
    'd26_short_circuit',
    'd27_early_return',
    'd28_loop_fusion',
    'd29_loop_fission',
    'd30_cps',
    'd31_aos_soa',
    'd32_sparse_dense',
    'd33_encoding',
    'd34_precompute',
    'd35_strength_reduce',
    'd36_cse',
    'd37_distributivity',
    'd38_partial_eval',
    'd39_defunc',
    'd40_curry',
    'd41_monad',
    'd42_generator',
    'd43_sliding_window',
    'd44_two_pointer',
    'd45_divide_conquer',
    'd46_string_build',
    'd47_bitwise',
    'd48_demorgan',
    # Utility axioms
    'algebra',
    'fold',
    'case',
    'quotient',
    # Python idiom axioms (P1-P48)
    'p01_comprehension',
    'p02_builtins',
    'p03_dict_ops',
    'p04_string_ops',
    'p05_sort_variants',
    'p06_itertools',
    'p07_collections',
    'p08_unpacking',
    'p09_exceptions',
    'p10_class_patterns',
    'p11_functional',
    'p12_numeric',
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
    'p25_regex',
    'p26_pathlib',
    'p27_dataclasses',
    'p28_typing',
    'p29_async',
    'p30_serialization',
    'p31_counter',
    'p32_property',
    'p33_metaclass',
    'p34_generator',
    'p35_map_filter_reduce',
    'p36_dict_merge',
    'p37_range_enumerate',
    'p38_zip_patterns',
    'p39_any_all',
    'p40_flatten',
    'p41_string_build',
    'p42_conditional',
    'p43_math_ops',
    'p44_heap_bisect',
    'p45_functools',
    'p46_operator',
    'p47_dunder',
    'p48_match',
]

# ── Mathlib axioms (auto-generated from Mathlib4) ─────────────
try:
    from cctt.axioms.mathlib import MATHLIB_AXIOMS, MATHLIB_REGISTRY
    ALL_AXIOMS.extend(MATHLIB_AXIOMS)
    AXIOM_REGISTRY.update(MATHLIB_REGISTRY)
except ImportError:
    pass  # mathlib axioms not yet generated
