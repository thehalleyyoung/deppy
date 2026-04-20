"""CCTT Proof Theory Integration — wire proofs into the checker pipeline.

This module integrates the proof theory with the existing CCTT
equivalence checker.  When a proof file exists alongside a program
pair, the checker verifies the proof INSTEAD of using heuristics.

Integration Points
==================
1. ``check_with_proof()`` — verify an explicit proof for two programs
2. ``load_proof_for_pair()`` — find and load a proof file
3. ``enhanced_check_equivalence()`` — drop-in replacement for
   ``check_equivalence()`` that tries proofs first

Convention
==========
Proof files are:
- ``*.proof.json`` — JSON-serialized ProofDocument
- ``*.proof.py`` — Python file defining ``PROOF``, ``LHS``, ``RHS``
"""
from __future__ import annotations

import importlib.util
import os
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
    compile_to_oterm,
)

from cctt.proof_theory.terms import ProofTerm
from cctt.proof_theory.checker import (
    check_proof, VerificationResult, ProofContext,
)
from cctt.proof_theory.serialization import (
    ProofDocument, load_proof,
)


# ═══════════════════════════════════════════════════════════════════
# Proof-based equivalence checking
# ═══════════════════════════════════════════════════════════════════

def check_with_proof(proof: ProofTerm,
                     source_f: str,
                     source_g: str,
                     ctx: Optional[ProofContext] = None) -> VerificationResult:
    """Verify an explicit proof that source_f ≡ source_g.

    Parameters
    ----------
    proof : ProofTerm
        The proof to verify.
    source_f : str
        Source code of function f.
    source_g : str
        Source code of function g.
    ctx : ProofContext, optional
        Additional context (definitions, etc.).

    Returns
    -------
    VerificationResult
        .valid is True iff the proof checks.
    """
    # Compile sources to OTerms
    result_f = compile_to_oterm(source_f)
    result_g = compile_to_oterm(source_g)

    if result_f is None:
        return VerificationResult(False, f'could not compile f: {source_f[:50]}')
    if result_g is None:
        return VerificationResult(False, f'could not compile g: {source_g[:50]}')

    oterm_f, _warnings_f = result_f
    oterm_g, _warnings_g = result_g

    return check_proof(proof, oterm_f, oterm_g, ctx)


def check_with_proof_terms(proof: ProofTerm,
                           lhs: OTerm,
                           rhs: OTerm,
                           ctx: Optional[ProofContext] = None) -> VerificationResult:
    """Verify a proof directly against OTerms."""
    return check_proof(proof, lhs, rhs, ctx)


# ═══════════════════════════════════════════════════════════════════
# Proof file discovery
# ═══════════════════════════════════════════════════════════════════

def find_proof_file(source_path: str) -> Optional[str]:
    """Find a proof file for a given source file.

    Looks for:
    1. source.proof.json  (JSON proof)
    2. source.proof.py    (Python proof)
    """
    base = source_path
    if base.endswith('.py'):
        base = base[:-3]

    json_path = f'{base}.proof.json'
    py_path = f'{base}.proof.py'

    if os.path.exists(json_path):
        return json_path
    if os.path.exists(py_path):
        return py_path

    return None


def load_proof_for_pair(path_f: str, path_g: str) -> Optional[ProofDocument]:
    """Load a proof for a pair of source files.

    Searches for proof files associated with either source file.
    """
    # Try proof file for f
    pf = find_proof_file(path_f)
    if pf is not None:
        return _load_proof_file(pf)

    # Try proof file for g
    pg = find_proof_file(path_g)
    if pg is not None:
        return _load_proof_file(pg)

    # Try a combined proof file: f_g.proof.json
    base_f = Path(path_f).stem
    base_g = Path(path_g).stem
    combined = Path(path_f).parent / f'{base_f}_{base_g}.proof.json'
    if combined.exists():
        return _load_proof_file(str(combined))

    return None


def _load_proof_file(path: str) -> Optional[ProofDocument]:
    """Load a proof from a file (JSON or Python)."""
    if path.endswith('.json'):
        try:
            return load_proof(path)
        except Exception:
            return None

    elif path.endswith('.py'):
        try:
            return _load_python_proof(path)
        except Exception:
            return None

    return None


def _load_python_proof(path: str) -> Optional[ProofDocument]:
    """Load a proof from a Python file.

    The file must define:
    - PROOF: ProofTerm
    - LHS: OTerm
    - RHS: OTerm
    - Optionally: NAME, DESCRIPTION, STRATEGY
    """
    spec = importlib.util.spec_from_file_location('_proof_module', path)
    if spec is None or spec.loader is None:
        return None

    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    proof = getattr(module, 'PROOF', None)
    lhs = getattr(module, 'LHS', None)
    rhs = getattr(module, 'RHS', None)

    if proof is None or lhs is None or rhs is None:
        return None

    name = getattr(module, 'NAME', Path(path).stem)
    desc = getattr(module, 'DESCRIPTION', '')
    strat = getattr(module, 'STRATEGY', '')

    return ProofDocument(
        name=name, lhs=lhs, rhs=rhs, proof=proof,
        description=desc, strategy=strat,
    )


# ═══════════════════════════════════════════════════════════════════
# Enhanced checker — proofs first, then heuristics
# ═══════════════════════════════════════════════════════════════════

def enhanced_check_equivalence(source_f: str, source_g: str,
                               timeout_ms: int = 5000,
                               proof: Optional[ProofTerm] = None,
                               proof_file: Optional[str] = None,
                               equiv_proof_text: Optional[str] = None) -> Any:
    """Drop-in replacement for ``check_equivalence()`` that tries
    explicit proofs before falling back to heuristics.

    Strategy ordering:
    0.  Explicit proof verification (if proof/proof_file given)
    0.25 Equiv proof script (LLM-written proof bridging different algorithms)
    0.5 Proof file discovery (look for *.proof.json / *.proof.py)
    1+  Original CCTT pipeline (denotational, Z3, Čech, bounded test)

    Parameters
    ----------
    source_f, source_g : str
        Source code of the two functions.
    timeout_ms : int
        Timeout for heuristic fallback.
    proof : ProofTerm, optional
        Explicit proof term.
    proof_file : str, optional
        Path to a proof file.
    equiv_proof_text : str, optional
        LLM-written equiv proof script (Lean-like surface syntax).

    Returns
    -------
    Result (from cctt.checker)
    """
    from cctt.checker import Result, check_equivalence

    # ── Strategy 0: Explicit proof ──
    if proof is not None:
        vr = check_with_proof(proof, source_f, source_g)
        if vr.valid:
            return Result(
                equivalent=True,
                explanation=f'proof verified: {vr.reason}',
                h0=1, h1=0, confidence=1.0,
            )

    # ── Strategy 0.25: Equiv proof script ──
    if equiv_proof_text is not None:
        try:
            from cctt.proof_theory.equiv_proof_language import try_equiv_proof
            verdict = try_equiv_proof(source_f, source_g, equiv_proof_text)
            if verdict is not None and verdict.equivalent:
                return Result(
                    equivalent=True,
                    explanation=(
                        f'equiv proof verified: {verdict.trust_level}'
                        f' ({verdict.detail})'
                    ),
                    h0=1, h1=0, confidence=1.0,
                )
        except Exception:
            pass  # Fall through to other strategies

    # ── Strategy 0.5: Proof file ──
    if proof_file is not None:
        doc = _load_proof_file(proof_file)
        if doc is not None:
            vr = check_with_proof(doc.proof, source_f, source_g)
            if vr.valid:
                return Result(
                    equivalent=True,
                    explanation=f'proof file verified: {doc.name}',
                    h0=1, h1=0, confidence=1.0,
                )

    # ── Strategy 1+: Original pipeline ──
    return check_equivalence(source_f, source_g, timeout_ms)


# ═══════════════════════════════════════════════════════════════════
# Proof registration — register proofs for program pairs
# ═══════════════════════════════════════════════════════════════════

# Global proof registry: (source_f_hash, source_g_hash) → ProofTerm
_PROOF_REGISTRY: Dict[Tuple[str, str], ProofTerm] = {}


def register_proof(source_f: str, source_g: str,
                   proof: ProofTerm) -> None:
    """Register a proof for a pair of programs.

    The proof will be used by enhanced_check_equivalence when
    checking these programs.
    """
    import hashlib
    hf = hashlib.md5(source_f.encode()).hexdigest()
    hg = hashlib.md5(source_g.encode()).hexdigest()
    _PROOF_REGISTRY[(hf, hg)] = proof
    _PROOF_REGISTRY[(hg, hf)] = proof


def lookup_proof(source_f: str, source_g: str) -> Optional[ProofTerm]:
    """Look up a registered proof for a program pair."""
    import hashlib
    hf = hashlib.md5(source_f.encode()).hexdigest()
    hg = hashlib.md5(source_g.encode()).hexdigest()
    return _PROOF_REGISTRY.get((hf, hg))


# ═══════════════════════════════════════════════════════════════════
# Verification report generation
# ═══════════════════════════════════════════════════════════════════

def generate_verification_report(doc: ProofDocument,
                                 result: VerificationResult) -> str:
    """Generate a human-readable verification report."""
    lines = [
        '═' * 60,
        f'  CCTT Proof Verification Report',
        '═' * 60,
        f'  Name:     {doc.name}',
        f'  Strategy: {doc.strategy or "not specified"}',
        f'  LHS:      {doc.lhs.canon()[:50]}',
        f'  RHS:      {doc.rhs.canon()[:50]}',
        '─' * 60,
    ]

    if result.valid:
        lines.extend([
            f'  Result:   ✓ VERIFIED',
            f'  Reason:   {result.reason}',
            f'  Depth:    {result.proof_depth}',
            f'  Z3 calls: {result.z3_calls}',
            f'  Time:     {result.time_ms:.1f} ms',
        ])
    else:
        lines.extend([
            f'  Result:   ✗ REJECTED',
            f'  Reason:   {result.reason}',
            f'  Depth:    {result.proof_depth}',
            f'  Time:     {result.time_ms:.1f} ms',
        ])

    if result.assumptions:
        lines.append(f'  Assumptions: {", ".join(result.assumptions)}')

    lines.append('═' * 60)
    return '\n'.join(lines)
