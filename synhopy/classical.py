"""
synhopy.classical — Classical logic constructs.

Provides classical axioms (LEM, double negation elimination) for
``from synhopy.classical import lem, classical``.
"""
from __future__ import annotations


def lem(prop: str):
    """Law of Excluded Middle: for any P, P ∨ ¬P."""
    return ("lem", prop)


def classical(fn):
    """Decorator marking a proof as using classical logic."""
    fn._synhopy_classical = True
    return fn


def dne(prop: str):
    """Double Negation Elimination: ¬¬P → P."""
    return ("dne", prop)
