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
    extraction (extraction.py) — code extraction from proofs (better than F*)
    dsl        (dsl.py)        — Pythonic proof DSL (calc, induction, etc.)
    python_patterns (python_patterns.py) — Python-specific proof templates
    spec_compiler (spec_compiler.py) — @guarantee → C⁴ Σ-type compiler

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

from cctt.proof_theory.extraction import (
    extract_from_proof,
    extract_from_document,
    extract_all,
    oterm_to_python,
    oterm_to_function,
    code_to_proof_obligation,
    verified,
    ExtractedCode,
    ExtractionCertificate,
)

from cctt.proof_theory.dsl import (
    ProofBuilder,
    ProofScript,
    CalcStep,
    c4_proof,
)

from cctt.proof_theory.python_patterns import (
    PatternInstance,
    by_pattern,
    list_patterns,
    PATTERNS,
)

from cctt.proof_theory.spec_compiler import (
    CompiledSpec,
    StructuralPredicate,
    SemanticPredicate,
    parse_guarantee,
    compile_guarantee_to_type,
    verify_against_spec,
    spec_to_markdown,
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
    # Extraction
    'extract_from_proof', 'extract_from_document', 'extract_all',
    'oterm_to_python', 'oterm_to_function',
    'code_to_proof_obligation', 'verified',
    'ExtractedCode', 'ExtractionCertificate',
    # DSL
    'ProofBuilder', 'ProofScript', 'CalcStep', 'c4_proof',
    # Python patterns
    'PatternInstance', 'by_pattern', 'list_patterns', 'PATTERNS',
    # Spec compiler
    'CompiledSpec', 'StructuralPredicate', 'SemanticPredicate',
    'parse_guarantee', 'compile_guarantee_to_type',
    'verify_against_spec', 'spec_to_markdown',
]
