"""CCTT Proof Theory — Mechanically verified proofs of algorithmic equivalence.

This module provides a complete proof theory for CCTT that can prove ANY
algorithmic equivalence via explicit proof terms. The proof checker is
purely structural — no sampling, no oracles, no heuristics. If the proof
checks, the equivalence is PROVEN.

Architecture
============

    ProofTerm  (terms.py)       — the language of proofs
    check_proof (checker.py)    — deterministic, terminating proof checker
    tactics    (tactics.py)     — automated proof-term construction
    examples   (examples.py)    — complete worked examples
    serialization (serialization.py) — JSON / human-readable proof I/O
    integration (integration.py)— wiring into the CCTT checker pipeline

Proof Strategies
================

    Refl, Sym, Trans, Cong     — structural equality reasoning
    Beta, Delta, Eta           — computation rules
    NatInduction, ListInduction, WellFoundedInduction — induction
    AxiomApp                   — apply CCTT axioms as rewrite steps
    LoopInvariant              — prove loop correctness
    Simulation                 — prove equivalence via bisimulation
    AbstractionRefinement      — both refine the same spec
    CommDiagram, FunctorMap    — categorical reasoning
    Z3Discharge                — decidable subgoals to Z3
    FiberDecomposition, CechGluing — cohomological reasoning
"""
from __future__ import annotations

from cctt.proof_theory.terms import (
    ProofTerm,
    Refl, Sym, Trans, Cong,
    Beta, Delta, Eta,
    NatInduction, ListInduction, WellFoundedInduction,
    AxiomApp, MathlibTheorem,
    LoopInvariant, Simulation, AbstractionRefinement,
    CommDiagram, FunctorMap,
    Z3Discharge,
    FiberDecomposition, CechGluing,
    Assume, Cut, LetProof,
    CasesSplit, Ext,
    Rewrite, RewriteChain,
    FiberRestrict, Descent, PathCompose, MathLibAxiom, FiberwiseUnivalence,
)

from cctt.proof_theory.checker import (
    check_proof,
    VerificationResult,
    ProofContext,
)

__all__ = [
    # Terms
    'ProofTerm',
    'Refl', 'Sym', 'Trans', 'Cong',
    'Beta', 'Delta', 'Eta',
    'NatInduction', 'ListInduction', 'WellFoundedInduction',
    'AxiomApp', 'MathlibTheorem',
    'LoopInvariant', 'Simulation', 'AbstractionRefinement',
    'CommDiagram', 'FunctorMap',
    'Z3Discharge',
    'FiberDecomposition', 'CechGluing',
    'Assume', 'Cut', 'LetProof',
    'CasesSplit', 'Ext',
    'Rewrite', 'RewriteChain',
    # C⁴ calculus terms
    'FiberRestrict', 'Descent', 'PathCompose', 'MathLibAxiom', 'FiberwiseUnivalence',
    # Checker
    'check_proof', 'VerificationResult', 'ProofContext',
]
