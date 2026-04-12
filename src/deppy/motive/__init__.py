"""Computational Motives — A Foundational Type Theory for Program Analysis.

This package implements the theory of computational motives: finite algebraic
structures extracted from programs that serve as universal invariants.  The
theory synthesises ideas from:

  • Lawvere's functorial semantics  — programs as algebras over a sort lattice
  • Martin-Löf dependent type theory — refinement predicates as type fibers
  • Grothendieck's sheaf cohomology  — Čech complex over the data-flow site
  • Algebraic K-theory              — resource classification via K₀
  • Tropical geometry               — complexity profiles as semiring invariants
  • Homotopy type theory            — loop structure via fundamental groupoid

The motive M(f) of a program f is a triple (Σ, G, H):
  Σ = algebraic signature  (typed operations with refinements and effects)
  G = data-flow category   (how operations compose)
  H = cohomological data   (H⁰ global sections, H¹ obstruction rank)

Applications (all reduce to motive operations):
  • Equivalence checking   — M(f) ≅ M(g)  via Z3 SAT isomorphism query
  • Bug detection          — H¹(M(f)) ≠ 0  means type obstruction exists
  • Spec verification      — M(impl) refines M(spec)
  • Refactoring validation — M(before) ≅ M(after)
  • Code similarity        — distance(M(f), M(g)) in the motive category

Public API:
    from deppy.motive import (
        Sort, Refinement, Effect, TypedOp,      # algebra
        FlowEdge, Motive,                        # structure
        MotiveExtractor,                          # AST → Motive
        CechCohomology,                           # cohomology engine
        MotiveIsomorphismSolver,                  # Z3 SAT solver
        motive_of,                                # convenience: source → Motive
    )
"""

from __future__ import annotations

from deppy.motive.sorts import Sort, sorts_compatible, sort_join, sort_meet
from deppy.motive.operations import Refinement, Effect, TypedOp, FlowEdge
from deppy.motive.motive import Motive
from deppy.motive.extractor import MotiveExtractor, motive_of
from deppy.motive.cohomology import CechCohomology
from deppy.motive.isomorphism import MotiveIsomorphismSolver

__all__ = [
    "Sort", "sorts_compatible", "sort_join", "sort_meet",
    "Refinement", "Effect", "TypedOp", "FlowEdge",
    "Motive",
    "MotiveExtractor", "motive_of",
    "CechCohomology",
    "MotiveIsomorphismSolver",
]
