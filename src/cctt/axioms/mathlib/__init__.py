"""Mathlib4 axioms for CCTT — auto-generated.

Total rewrite rules: 108751
Total axiom modules: 32
"""
from __future__ import annotations

from typing import Dict, List, Tuple
from cctt.denotation import OTerm
from cctt.path_search import FiberCtx


# Import all mathlib axiom modules
from cctt.axioms.mathlib import ml_algebra_group
from cctt.axioms.mathlib import ml_algebra_ring
from cctt.axioms.mathlib import ml_analysis
from cctt.axioms.mathlib import ml_bool
from cctt.axioms.mathlib import ml_category
from cctt.axioms.mathlib import ml_combinatorics
from cctt.axioms.mathlib import ml_equiv
from cctt.axioms.mathlib import ml_function
from cctt.axioms.mathlib import ml_int_basic
from cctt.axioms.mathlib import ml_list
from cctt.axioms.mathlib import ml_list_basic
from cctt.axioms.mathlib import ml_list_filter
from cctt.axioms.mathlib import ml_list_fold
from cctt.axioms.mathlib import ml_list_map
from cctt.axioms.mathlib import ml_list_misc
from cctt.axioms.mathlib import ml_list_sort
from cctt.axioms.mathlib import ml_list_zip
from cctt.axioms.mathlib import ml_logic_basic
from cctt.axioms.mathlib import ml_logic_quantifier
from cctt.axioms.mathlib import ml_multiset
from cctt.axioms.mathlib import ml_nat_basic
from cctt.axioms.mathlib import ml_nat_div
from cctt.axioms.mathlib import ml_nat_order
from cctt.axioms.mathlib import ml_number_theory
from cctt.axioms.mathlib import ml_option
from cctt.axioms.mathlib import ml_order
from cctt.axioms.mathlib import ml_other
from cctt.axioms.mathlib import ml_prod
from cctt.axioms.mathlib import ml_set_basic
from cctt.axioms.mathlib import ml_set_theory
from cctt.axioms.mathlib import ml_string
from cctt.axioms.mathlib import ml_topology
from cctt.axioms.mathlib import ml_untranslatable


_MATHLIB_MODULES = [
    ml_algebra_group,
    ml_algebra_ring,
    ml_analysis,
    ml_bool,
    ml_category,
    ml_combinatorics,
    ml_equiv,
    ml_function,
    ml_int_basic,
    ml_list,
    ml_list_basic,
    ml_list_filter,
    ml_list_fold,
    ml_list_map,
    ml_list_misc,
    ml_list_sort,
    ml_list_zip,
    ml_logic_basic,
    ml_logic_quantifier,
    ml_multiset,
    ml_nat_basic,
    ml_nat_div,
    ml_nat_order,
    ml_number_theory,
    ml_option,
    ml_order,
    ml_other,
    ml_prod,
    ml_set_basic,
    ml_set_theory,
    ml_string,
    ml_topology,
]


# Ordered list of (name, apply_fn) pairs
MATHLIB_AXIOMS: List[Tuple[str, object]] = [
    (mod.AXIOM_NAME, mod.apply) for mod in _MATHLIB_MODULES
]


# Name → module registry
MATHLIB_REGISTRY: Dict[str, object] = {
    mod.AXIOM_NAME: mod for mod in _MATHLIB_MODULES
}


def all_mathlib_rewrites(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all Mathlib rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    for mod in _MATHLIB_MODULES:
        if mod.recognizes(term):
            results.extend(mod.apply(term, ctx))
    return results


TOTAL_RULES = 108751
TOTAL_MODULES = 32


def report() -> str:
    """Return a summary report of Mathlib axiom coverage."""
    parts = [
        f"Mathlib CCTT Axioms: 108751 rewrite rules in 32 modules",
    ]
    for mod in _MATHLIB_MODULES:
        name = mod.AXIOM_NAME
        n_untrans = len(getattr(mod, "UNTRANSLATABLE_THEOREMS", []))
        parts.append(f"  {name}: {n_untrans} untranslatable stored")
    return "\n".join(parts)
