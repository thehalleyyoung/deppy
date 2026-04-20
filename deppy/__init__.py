"""
Deppy — Synthetic Homotopy Python Type Theory

A formal verification system for Python based on cubical homotopy type theory.
"""
from __future__ import annotations

__version__ = "0.1.0"

# ── Public API re-exports ──
# These make ``from deppy import guarantee`` (etc.) work as shown in the
# Deppy tutorial book.  Everything delegates to internal modules.

from deppy.proofs.sugar import (          # noqa: F401  — decorators & DSL
    guarantee, requires, ensures, verify, pure, total,
    decreases, invariant, reads, mutates,
    given, library_trust,
    Proof, ProofBuilder, ProofContext,
    Nat, Pos, NonEmpty, NonNull, Sorted, Bounded, SizedExact,
    refl, sym, trans, path, path_chain, funext,
    transport_proof, transport_from, path_equivalent,
    by_z3, by_axiom, by_cases, by_induction, by_transport,
    by_cech_proof, by_fiber_proof, by_duck_type, by_ext,
    by_list_induction, by_cong, by_rewrite, by_unfold, by_effect,
    formal_check, formal_eq, extract_spec,
    Spec, SpecKind, DomainKnowledge,
    FormalProof, FunctionSpec,
    _get_spec,
)
from deppy.proofs.sugar import Refine as refined          # noqa: F401
from deppy.proofs.sugar import Refine                     # noqa: F401

from deppy.core.kernel import (           # noqa: F401  — proof terms
    ProofKernel, ProofTerm, TrustLevel, VerificationResult,
    Refl, Sym, Trans, Cong, Cut, Assume, Z3Proof,
    NatInduction, ListInduction, Cases, DuckPath,
    EffectWitness, AxiomInvocation, Ext, Unfold, Rewrite,
    Structural, TransportProof, PathComp, Ap, FunExt,
    CechGlue, Univalence, Fiber, Patch,
)

# Convenience aliases used in book examples
assume = requires          # F*-style name
check = invariant          # F*-style name
preserves_spec = guarantee # alias
transforms_spec = guarantee
implements = guarantee
def protocol_spec(cls_or_str=None):
    """Mark a Protocol class as a Deppy specification.

    Can be used as:
      - @protocol_spec (bare decorator on a Protocol class)
      - @protocol_spec("description") (with a spec string)
    """
    if isinstance(cls_or_str, str):
        return guarantee(cls_or_str)
    if isinstance(cls_or_str, type):
        _get_spec(cls_or_str)  # attach spec metadata
        return cls_or_str
    if cls_or_str is None:
        def decorator(cls):
            _get_spec(cls)
            return cls
        return decorator
    return cls_or_str
from deppy.lean.compiler import compile_to_lean  # noqa: F401

loop_variant = decreases
fuel = decreases
may_diverge = total        # marks intent (opposite semantics — placeholder)
Perm = Trans               # permutation path (alias for book examples)

def uses(*deps):
    """Declare that a lemma or proof uses other lemmas/theorems."""
    def decorator(fn):
        fn._deppy_uses = deps
        return fn
    return decorator

def induction(target):
    """Decorator marking a proof as proceeding by induction on `target`."""
    def decorator(fn):
        fn._deppy_induction_target = target
        return fn
    return decorator

def lemma(fn):
    """Decorator marking a function as a lemma (returns a proof term)."""
    fn._deppy_lemma = True
    return fn

def trust_boundary(fn):
    """Decorator marking a function as a trust boundary (FFI/external call)."""
    fn._deppy_trust_boundary = True
    return fn
