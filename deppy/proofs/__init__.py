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

# Cubical proof language and five-stage pipeline
from deppy.proofs.language import (
    CodeAxiom, UnfoldError, Goal, Tactic, T,
    function_to_axioms, class_to_axioms,
    install, eq, prove,
    AXIOM_SUFFIX_DEF, AXIOM_SUFFIX_CASE, AXIOM_SUFFIX_DEFAULT,
    AXIOM_SUFFIX_FOLD, AXIOM_SUFFIX_INDUCTION, AXIOM_SUFFIX_INIT,
    AXIOM_SUFFIX_PROPERTY, AXIOM_SUFFIX_INHERITED,
    axiom_case_suffix,
)
from deppy.proofs.pipeline import (
    AxiomRegistry, AxiomMeta,
    axiomize, deep_function_to_axioms, deep_class_to_axioms,
    foldl_universal_axioms, register_universal_axioms,
    Tactics, TFirst, TRepeat, TSimpWith, TIntro, TCases, TInduction,
    ProofTreeNode, ProofCertificate, prove_certificate,
    ProofScript, verify_proof_script,
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
    # Cubical proof language
    "CodeAxiom", "UnfoldError", "Goal", "Tactic", "T",
    "function_to_axioms", "class_to_axioms", "install", "eq", "prove",
    # Axiom-name grammar (single source of truth)
    "AXIOM_SUFFIX_DEF", "AXIOM_SUFFIX_CASE", "AXIOM_SUFFIX_DEFAULT",
    "AXIOM_SUFFIX_FOLD", "AXIOM_SUFFIX_INDUCTION", "AXIOM_SUFFIX_INIT",
    "AXIOM_SUFFIX_PROPERTY", "AXIOM_SUFFIX_INHERITED",
    "axiom_case_suffix",
    # Five-stage cubical pipeline
    "AxiomRegistry", "AxiomMeta",
    "axiomize", "deep_function_to_axioms", "deep_class_to_axioms",
    "foldl_universal_axioms", "register_universal_axioms",
    "Tactics", "TFirst", "TRepeat", "TSimpWith",
    "TIntro", "TCases", "TInduction",
    "ProofTreeNode", "ProofCertificate", "prove_certificate",
    "ProofScript", "verify_proof_script",
]
