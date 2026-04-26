"""
deppy.classical — **inert stub** for classical logic markers.

``lem(P)`` returns the tuple ``("lem", P)``, ``dne(P)`` returns
``("dne", P)``.  These tuples are NOT recognised as proofs by
``ProofKernel.verify`` — the kernel will reject them if you try.  The
``@classical`` decorator attaches ``fn._deppy_classical = True`` which
nothing downstream reads.

Kept for backward compatibility with tutorial code.  To actually
introduce a classical axiom, register a ``FormalAxiomEntry`` with the
kernel via ``kernel.register_formal_axiom(...)``.
"""
from __future__ import annotations


def lem(prop: str):
    """Law of Excluded Middle: for any P, P ∨ ¬P."""
    return ("lem", prop)


def classical(fn):
    """Decorator marking a proof as using classical logic."""
    fn._deppy_classical = True
    return fn


def dne(prop: str):
    """Double Negation Elimination: ¬¬P → P."""
    return ("dne", prop)
