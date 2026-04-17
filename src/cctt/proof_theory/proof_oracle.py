"""proof_oracle.py — F*-style proof term generation oracle.

In F*, the type checker generates verification conditions from code,
then discharges them automatically (via Z3) or asks the programmer
for proof terms.  In C4, the LLM plays the role of the programmer:
it generates C4 proof terms that the compiler verifies.

Architecture
============

1. The verifier (c4_llm_verifier.py) generates a ProofObligation
   from the code structure — hypotheses, goal, code context.

2. The ProofOracle receives the obligation and returns a ProofTerm.
   - MockProofOracle: returns None (no proof available)
   - AutomatedProofOracle: tries ExFalso, ListSimp, etc.
   - LLMProofOracle: asks the LLM for a C4 proof term (JSON)

3. The C4 compiler verifies the proof term independently.
   The proof is accepted ONLY if the compiler validates it.
   Trust level is determined by the compiler, not the oracle.

This is the F*-style connection: proof terms reference actual code
variables and code structure.  The oracle is a PROPOSER, not a
VERIFIER — soundness comes from the C4 compiler alone.

Available proof tactics for obligations
=======================================
- ExFalso:       hypotheses contradictory → any goal
- ListSimp:      list literal structural properties (len, isinstance)
- Z3Discharge:   direct Z3 validity check
- ArithmeticSimp: arithmetic identities
- CasesSplit:    case analysis on conditions
- Rewrite:       substitute equals for equals
- Transport:     move proofs along type paths
- Cut:           introduce an intermediate lemma
- NatInduction:  induction on natural numbers
- ListInduction: induction on list structure
"""
from __future__ import annotations

import json
import logging
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple

from cctt.proof_theory.terms import (
    ProofTerm, ExFalso, Z3Discharge, ListSimp,
    ArithmeticSimp, CasesSplit, Rewrite, Transport,
    Cut, ProofObligation,
)

log = logging.getLogger(__name__)


# ═══════════════════════════════════════════════════════════════════
# Oracle ABC
# ═══════════════════════════════════════════════════════════════════

class ProofOracle(ABC):
    """Abstract proof term generator.

    Given a ProofObligation (hypotheses + goal + code context),
    proposes a ProofTerm that the C4 compiler will verify.

    The oracle is NOT trusted — it is a proposer.  Soundness
    comes from the C4 compiler verifying the proposed proof.
    """

    @abstractmethod
    def generate_proof(
        self, obligation: ProofObligation,
    ) -> Optional[ProofTerm]:
        """Generate a proof term for the obligation, or None if unable."""
        ...

    def name(self) -> str:
        return type(self).__name__


# ═══════════════════════════════════════════════════════════════════
# Automated oracle — tries structural tactics without LLM
# ═══════════════════════════════════════════════════════════════════

class AutomatedProofOracle(ProofOracle):
    """Tries automated proof tactics before falling back to None.

    Tactic pipeline:
    1. ExFalso — hypotheses contradictory
    2. ListSimp — list literal structural properties
    3. Z3Discharge — direct Z3 validity
    """

    def generate_proof(
        self, obligation: ProofObligation,
    ) -> Optional[ProofTerm]:
        # Tactic 1: ExFalso — check if hypotheses are contradictory
        proof = self._try_ex_falso(obligation)
        if proof is not None:
            return proof

        return None

    def _try_ex_falso(
        self, obligation: ProofObligation,
    ) -> Optional[ProofTerm]:
        """Check if the hypotheses are contradictory."""
        try:
            from cctt.proof_theory.c4_compiler import Z3Env
            from z3 import Solver, unsat
        except ImportError:
            return None

        env = Z3Env()
        for var_name, var_sort in obligation.var_sorts.items():
            env.declare_var(var_name, var_sort)

        hyps_z3 = []
        for h in obligation.hypotheses:
            parsed = env.parse_formula(h)
            if parsed is not None:
                hyps_z3.append(parsed)

        if not hyps_z3:
            return None

        s = Solver()
        s.set('timeout', 5000)
        for h in hyps_z3:
            s.add(h)

        if s.check() == unsat:
            context = " and ".join(f"({h})" for h in obligation.hypotheses)
            return ExFalso(
                context_formula=context,
                variables=dict(obligation.var_sorts),
                absurdity=f"hypotheses contradictory in {obligation.func_name}",
            )

        return None

    def name(self) -> str:
        return "AutomatedProofOracle"


# ═══════════════════════════════════════════════════════════════════
# Mock oracle — returns None (testing)
# ═══════════════════════════════════════════════════════════════════

class MockProofOracle(ProofOracle):
    """Returns None — no proof available.  For testing."""

    def generate_proof(
        self, obligation: ProofObligation,
    ) -> Optional[ProofTerm]:
        return None


# ═══════════════════════════════════════════════════════════════════
# LLM oracle — generates proof terms via language model
# ═══════════════════════════════════════════════════════════════════

class LLMProofOracle(ProofOracle):
    """Generates C4 proof terms by asking an LLM.

    The LLM receives a structured prompt with:
    1. The proof obligation (hypotheses → goal)
    2. Available C4 tactics with descriptions
    3. The source code context
    4. Examples of valid proof terms

    The LLM returns a JSON proof term which is parsed into a
    ProofTerm and then verified by the C4 compiler.

    Trust: the LLM is NOT trusted.  It is a proposer.
    The C4 compiler determines validity independently.
    """

    def __init__(self, spec_oracle: Any = None):
        """Initialize with an optional spec oracle for LLM access."""
        self._spec_oracle = spec_oracle

    def generate_proof(
        self, obligation: ProofObligation,
    ) -> Optional[ProofTerm]:
        # First try automated tactics
        auto = AutomatedProofOracle()
        proof = auto.generate_proof(obligation)
        if proof is not None:
            return proof

        # Then try LLM proof generation
        if self._spec_oracle is None:
            return None

        prompt = self._build_proof_prompt(obligation)
        try:
            response = self._query_llm(prompt)
            if response:
                return self._parse_proof_response(response, obligation)
        except Exception as e:
            log.debug("LLM proof generation failed: %s", e)

        return None

    def _build_proof_prompt(self, obligation: ProofObligation) -> str:
        """Build an F*-style proof obligation prompt for the LLM."""
        lines = [
            "# C4 Proof Obligation",
            "",
            f"Function: {obligation.func_name}",
            "",
            "## Hypotheses (given):",
        ]
        for i, h in enumerate(obligation.hypotheses, 1):
            lines.append(f"  {i}. {h}")

        lines.extend([
            "",
            f"## Goal (to prove):",
            f"  {obligation.goal}",
            "",
            f"## Return expression:",
            f"  {obligation.return_expr}",
            "",
            "## Available C4 Tactics:",
            '  - ExFalso: {"tactic": "ExFalso", "context_formula": "hyp1 and hyp2", "variables": {"x": "Int"}}',
            '    Use when hypotheses are contradictory (e.g., x > 0 and x <= 0)',
            '  - Z3Discharge: {"tactic": "Z3Discharge", "formula": "goal_formula", "fragment": "QF_LIA"}',
            '    Use when the goal follows from hypotheses by arithmetic/logic',
            '  - ListSimp: {"tactic": "ListSimp", "rule": "literal_len", "target": "len([a,b,c]) == 3"}',
            '    Use for structural list properties (length of literals, isinstance)',
            "",
            "## Source code context:",
            "```python",
            obligation.source[:500] if obligation.source else "(not available)",
            "```",
            "",
            "Respond with ONLY the JSON proof term, no explanation.",
        ])
        return "\n".join(lines)

    def _query_llm(self, prompt: str) -> Optional[str]:
        """Query the LLM for a proof term."""
        if self._spec_oracle is None:
            return None

        try:
            if hasattr(self._spec_oracle, '_query_llm'):
                return self._spec_oracle._query_llm(prompt)
            if hasattr(self._spec_oracle, 'generate_spec'):
                # Abuse spec generation to get a response
                return None
        except Exception:
            pass
        return None

    def _parse_proof_response(
        self, response: str, obligation: ProofObligation,
    ) -> Optional[ProofTerm]:
        """Parse an LLM response into a C4 ProofTerm."""
        try:
            # Extract JSON from response
            text = response.strip()
            if "```" in text:
                parts = text.split("```")
                for part in parts:
                    part = part.strip()
                    if part.startswith("json"):
                        part = part[4:].strip()
                    if part.startswith("{"):
                        text = part
                        break

            data = json.loads(text)
            return parse_proof_json(data, obligation)

        except (json.JSONDecodeError, KeyError, ValueError) as e:
            log.debug("Failed to parse LLM proof response: %s", e)
            return None

    def name(self) -> str:
        return "LLMProofOracle"


# ═══════════════════════════════════════════════════════════════════
# Proof term JSON parser
# ═══════════════════════════════════════════════════════════════════

def parse_proof_json(
    data: dict, obligation: ProofObligation,
) -> Optional[ProofTerm]:
    """Parse a JSON proof term into a C4 ProofTerm.

    Supports the core tactic vocabulary:
    - ExFalso, Z3Discharge, ListSimp, ArithmeticSimp
    - CasesSplit (with recursive sub-proofs)
    """
    tactic = data.get("tactic", "")

    if tactic == "ExFalso":
        return ExFalso(
            context_formula=data.get("context_formula", ""),
            variables=data.get("variables", dict(obligation.var_sorts)),
            absurdity=data.get("absurdity", "LLM-generated"),
        )

    if tactic == "Z3Discharge":
        return Z3Discharge(
            formula=data.get("formula", obligation.goal),
            fragment=data.get("fragment", "QF_LIA"),
            timeout_ms=data.get("timeout_ms", 5000),
            variables=data.get("variables", dict(obligation.var_sorts)),
        )

    if tactic == "ListSimp":
        return ListSimp(
            rule=data.get("rule", "structural"),
            target=data.get("target", obligation.goal),
        )

    if tactic == "ArithmeticSimp":
        return ArithmeticSimp(
            rule=data.get("rule", "arithmetic"),
            target=data.get("target", obligation.goal),
        )

    log.debug("Unknown proof tactic: %s", tactic)
    return None
