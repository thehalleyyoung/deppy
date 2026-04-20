"""Deppy proofs — proof language, tactics, sugar, templates."""
from __future__ import annotations

from deppy.proofs.sugar import (
    guarantee, requires, ensures, pure, reads, mutates,
    total, partial_fn, invariant, decreases, verify,
    Pos, Nat, NonEmpty, Bounded, NonNull, Sorted, SizedExact, Refine,
    library_trust, Proof, FormalProof, ProofContext,
    refl, sym, trans, by_axiom, by_z3, by_cases,
    by_induction, by_list_induction, by_ext, by_cong,
    by_unfold, by_rewrite, by_transport, by_effect,
    given, extract_spec,
    set_global_kernel, get_global_kernel,
)

__all__ = [
    # Decorators
    "guarantee", "requires", "ensures", "pure", "reads", "mutates",
    "total", "partial_fn", "invariant", "decreases", "verify",
    # Refinement types
    "Pos", "Nat", "NonEmpty", "Bounded", "NonNull", "Sorted",
    "SizedExact", "Refine",
    # Library trust
    "library_trust",
    # Proof builders
    "Proof", "FormalProof", "ProofContext",
    # Quick combinators
    "refl", "sym", "trans", "by_axiom", "by_z3", "by_cases",
    "by_induction", "by_list_induction", "by_ext", "by_cong",
    "by_unfold", "by_rewrite", "by_transport", "by_effect",
    # Domain knowledge
    "given", "extract_spec",
    # Kernel management
    "set_global_kernel", "get_global_kernel",
]
