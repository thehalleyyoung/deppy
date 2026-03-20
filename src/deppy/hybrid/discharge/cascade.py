"""
Pillar 5 – Z3 + LLM → Lean Discharge: 5-stage proof discharge cascade.

Obligations flow through stages: TRIVIAL → Z3 → LLM_PROVER → LEAN_CHECK → RESIDUAL.
Each stage either discharges the obligation (producing a Lean proof term) or passes
it to the next stage.  The cascade is configurable and reports statistics.
"""
from __future__ import annotations

import enum
import hashlib
import logging
import re
import time
import uuid
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
)

# ---------------------------------------------------------------------------
# Optional Z3 dependency
# ---------------------------------------------------------------------------
try:
    import z3  # type: ignore

    _HAS_Z3 = True
except ImportError:  # pragma: no cover
    z3 = None  # type: ignore
    _HAS_Z3 = False


# --- Integration with existing deppy codebase ---
try:
    from deppy.solver import FragmentDispatcher as _CoreDispatcher, Z3Backend, SolverObligation, SolverResult, SolverStatus
    from deppy.solver.proof_certificate import ProofCertificate as _CoreProofCertificate
    from deppy.proof._protocols import ProofObligation as _CoreProofObligation
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

logger = logging.getLogger(__name__)

# ═══════════════════════════════════════════════════════════════════════════
# DischargeStage enum
# ═══════════════════════════════════════════════════════════════════════════


class DischargeStage(enum.Enum):
    """The five stages a proof obligation may pass through."""

    TRIVIAL = "trivial"
    Z3 = "z3"
    LLM_PROVER = "llm_prover"
    LEAN_CHECK = "lean_check"
    RESIDUAL = "residual"


# ═══════════════════════════════════════════════════════════════════════════
# DischargeResult
# ═══════════════════════════════════════════════════════════════════════════


@dataclass
class DischargeResult:
    """Outcome of attempting to discharge a single proof obligation."""

    obligation_id: str
    stage: DischargeStage
    discharged: bool
    proof: Optional[str] = None
    trust_level: str = "UNVERIFIED"
    confidence: float = 0.0
    time_ms: float = 0.0
    error: Optional[str] = None
    attempts: int = 1

    # -- Provenance fields for audit trails --
    _z3_model: Optional[str] = field(default=None, repr=False)
    _llm_raw_response: Optional[str] = field(default=None, repr=False)

    # -- helpers ----------------------------------------------------------

    def to_dict(self) -> Dict[str, Any]:
        """Serialise the result to a plain dictionary."""
        return {
            "obligation_id": self.obligation_id,
            "stage": self.stage.value,
            "discharged": self.discharged,
            "proof": self.proof,
            "trust_level": self.trust_level,
            "confidence": self.confidence,
            "time_ms": round(self.time_ms, 3),
            "error": self.error,
            "attempts": self.attempts,
        }

    @staticmethod
    def trivial(obligation_id: str, proof: str, time_ms: float) -> DischargeResult:
        return DischargeResult(
            obligation_id=obligation_id,
            stage=DischargeStage.TRIVIAL,
            discharged=True,
            proof=proof,
            trust_level="TRIVIAL",
            confidence=1.0,
            time_ms=time_ms,
        )

    @staticmethod
    def residual(obligation_id: str, reason: str, time_ms: float) -> DischargeResult:
        return DischargeResult(
            obligation_id=obligation_id,
            stage=DischargeStage.RESIDUAL,
            discharged=False,
            proof="sorry /- RESIDUAL: undischarged -/",
            trust_level="ASSUMED",
            confidence=0.0,
            time_ms=time_ms,
            error=reason,
        )

    def __str__(self) -> str:
        status = "✓" if self.discharged else "✗"
        return (
            f"[{status}] {self.obligation_id} @ {self.stage.value} "
            f"({self.time_ms:.1f}ms, trust={self.trust_level})"
        )


# ═══════════════════════════════════════════════════════════════════════════
# ProofObligation
# ═══════════════════════════════════════════════════════════════════════════


@dataclass
class ProofObligation:
    """A single proof obligation that the cascade must discharge or flag."""

    id: str
    description: str
    lean_statement: str

    context: Dict[str, Any] = field(default_factory=dict)
    source: str = "unknown"
    priority: int = 0
    structural: bool = False

    # Optional hints that may help downstream stages
    hypotheses: List[str] = field(default_factory=list)
    available_lemmas: List[str] = field(default_factory=list)
    variables: Dict[str, str] = field(default_factory=dict)

    def fingerprint(self) -> str:
        """Stable hash for caching / deduplication."""
        blob = f"{self.lean_statement}|{sorted(self.context.items())}"
        return hashlib.sha256(blob.encode()).hexdigest()[:16]

    def to_dict(self) -> Dict[str, Any]:
        return {
            "id": self.id,
            "description": self.description,
            "lean_statement": self.lean_statement,
            "context": self.context,
            "source": self.source,
            "priority": self.priority,
            "structural": self.structural,
            "hypotheses": self.hypotheses,
            "available_lemmas": self.available_lemmas,
            "variables": self.variables,
        }

    @staticmethod
    def from_dict(d: Dict[str, Any]) -> ProofObligation:
        return ProofObligation(
            id=d.get("id", str(uuid.uuid4())),
            description=d.get("description", ""),
            lean_statement=d.get("lean_statement", ""),
            context=d.get("context", {}),
            source=d.get("source", "unknown"),
            priority=d.get("priority", 0),
            structural=d.get("structural", False),
            hypotheses=d.get("hypotheses", []),
            available_lemmas=d.get("available_lemmas", []),
            variables=d.get("variables", {}),
        )

    def __str__(self) -> str:
        tag = "[structural]" if self.structural else "[semantic]"
        return f"Obligation({self.id} {tag} prio={self.priority}): {self.lean_statement[:80]}"


# ═══════════════════════════════════════════════════════════════════════════
# DischargeCascadeConfig
# ═══════════════════════════════════════════════════════════════════════════


@dataclass
class DischargeCascadeConfig:
    """Knobs for tuning the discharge cascade."""

    z3_timeout_ms: int = 5000
    llm_max_attempts: int = 3
    llm_model: str = "gpt-4"
    lean_timeout_ms: int = 10000
    max_retries: int = 2

    # Parallelism
    max_workers: int = 4

    # Feature flags
    skip_z3: bool = False
    skip_llm: bool = False
    skip_lean_check: bool = False
    verbose: bool = False

    # Optional callbacks
    llm_call: Optional[Callable[..., str]] = field(default=None, repr=False)
    lean_check_call: Optional[Callable[..., Dict]] = field(default=None, repr=False)


# ═══════════════════════════════════════════════════════════════════════════
# TrivialDischarger
# ═══════════════════════════════════════════════════════════════════════════


class TrivialDischarger:
    """Pattern library for obligations that can be discharged without solvers.

    Every method returns either a Lean proof string or ``None``.
    """

    # ---- reflexivity patterns -------------------------------------------

    _REFLEXIVITY_OPS: Set[str] = {"=", "≤", "≥", "⊆", "⊇", "↔", "≡", "≃"}

    @classmethod
    def check_reflexivity(cls, stmt: str) -> Optional[str]:
        """Recognise ``x = x``, ``a ≤ a``, etc."""
        normalised = stmt.strip()
        for op in cls._REFLEXIVITY_OPS:
            if op in normalised:
                parts = normalised.split(op, 1)
                if len(parts) == 2 and parts[0].strip() == parts[1].strip():
                    if op in ("=", "≡", "≃"):
                        return "rfl"
                    if op in ("≤", "≥"):
                        return "le_refl _"
                    if op in ("⊆", "⊇"):
                        return "Subset.rfl"
                    if op == "↔":
                        return "Iff.rfl"
        return None

    # ---- tautology patterns ---------------------------------------------

    _TAUTOLOGY_LITERALS: Set[str] = {
        "True",
        "true",
        "trivial",
        "⊤",
    }

    _TAUTOLOGY_REGEX = re.compile(
        r"^(?:(?P<p>[A-Za-z_]\w*)\s*∨\s*¬\s*(?P=p)"
        r"|¬\s*(?P<q>[A-Za-z_]\w*)\s*∨\s*(?P=q))$"
    )

    @classmethod
    def check_tautology(cls, stmt: str) -> Optional[str]:
        """``True``, ``P ∨ ¬P``, etc."""
        normalised = stmt.strip()
        if normalised in cls._TAUTOLOGY_LITERALS:
            return "trivial"
        m = cls._TAUTOLOGY_REGEX.match(normalised)
        if m:
            return "exact Classical.em _"
        if normalised == "False → False":
            return "exact id"
        if re.match(r"^.*→\s*True$", normalised):
            return "exact fun _ => trivial"
        return None

    # ---- direct hypothesis match ----------------------------------------

    @classmethod
    def check_hypothesis(cls, stmt: str, hypotheses: Sequence[str]) -> Optional[str]:
        """If the statement is literally one of the hypotheses, use ``assumption``."""
        normalised = stmt.strip()
        for hyp in hypotheses:
            if hyp.strip() == normalised:
                return "assumption"
        return None

    # ---- type inhabitedness ---------------------------------------------

    _INHABITED_TYPES: Dict[str, str] = {
        "Nat": "exact 0",
        "ℕ": "exact 0",
        "Int": "exact 0",
        "ℤ": "exact 0",
        "Bool": "exact true",
        "String": 'exact ""',
        "Unit": "exact ()",
        "PUnit": "exact PUnit.unit",
        "Float": "exact 0.0",
        "Char": "exact 'a'",
    }

    _LIST_RE = re.compile(r"^(?:List|Array)\s+\w+$")

    @classmethod
    def check_inhabitedness(cls, stmt: str) -> Optional[str]:
        """``Nat`` is inhabited, ``List α`` is inhabited, etc."""
        normalised = stmt.strip()
        if normalised in cls._INHABITED_TYPES:
            return cls._INHABITED_TYPES[normalised]
        if cls._LIST_RE.match(normalised):
            return "exact []"
        if normalised.startswith("Option "):
            return "exact none"
        return None

    # ---- simple arithmetic truths ---------------------------------------

    _ARITH_PATTERNS: List[Tuple[re.Pattern, str]] = [
        (re.compile(r"^0\s*[≤<=]\s*\w+$"), "omega"),
        (re.compile(r"^(\w+)\s*<\s*\1\s*\+\s*1$"), "omega"),
        (re.compile(r"^(\w+)\s*≤\s*\1\s*\+\s*\d+$"), "omega"),
        (re.compile(r"^(\w+)\s*\+\s*0\s*=\s*\1$"), "omega"),
        (re.compile(r"^0\s*\+\s*(\w+)\s*=\s*\1$"), "omega"),
        (re.compile(r"^(\w+)\s*-\s*0\s*=\s*\1$"), "omega"),
        (re.compile(r"^(\d+)\s*[≤<]\s*(\d+)$"), "omega"),
        (re.compile(r"^(\w+)\s*<\s*\1\s*\+\s*\d+$"), "omega"),
        (re.compile(r"^Nat\.succ\s+(\w+)\s*>\s*0$"), "omega"),
        (re.compile(r"^(\w+)\s*≥\s*0$"), "omega"),
    ]

    @classmethod
    def check_arithmetic(cls, stmt: str) -> Optional[str]:
        """``0 ≤ n``, ``n < n + 1``, and similar."""
        normalised = stmt.strip()
        for pattern, tactic in cls._ARITH_PATTERNS:
            if pattern.match(normalised):
                return tactic
        return None

    # ---- absurdity / contradiction --------------------------------------

    @classmethod
    def check_contradiction(cls, stmt: str, hypotheses: Sequence[str]) -> Optional[str]:
        """If ``False`` or ``⊥`` is among the hypotheses, anything follows."""
        for hyp in hypotheses:
            h = hyp.strip()
            if h in ("False", "⊥"):
                return "contradiction"
        return None

    # ---- top-level dispatch ---------------------------------------------

    @classmethod
    def try_discharge(
        cls,
        obligation: ProofObligation,
    ) -> Optional[str]:
        """Run every trivial-discharger pattern and return first success."""
        stmt = obligation.lean_statement
        hyps = obligation.hypotheses

        for checker in (
            lambda: cls.check_reflexivity(stmt),
            lambda: cls.check_tautology(stmt),
            lambda: cls.check_hypothesis(stmt, hyps),
            lambda: cls.check_inhabitedness(stmt),
            lambda: cls.check_arithmetic(stmt),
            lambda: cls.check_contradiction(stmt, hyps),
        ):
            proof = checker()
            if proof is not None:
                return proof
        return None


# ═══════════════════════════════════════════════════════════════════════════
# Z3 helper (stage 2)
# ═══════════════════════════════════════════════════════════════════════════


class _Z3Stage:
    """Encode an obligation as a Z3 formula and attempt to prove it."""

    def __init__(self, timeout_ms: int = 5000) -> None:
        self._timeout_ms = timeout_ms

    # -----------------------------------------------------------------
    # Public interface
    # -----------------------------------------------------------------

    def attempt(self, obligation: ProofObligation) -> Optional[DischargeResult]:
        """Try to discharge *obligation* via Z3.  Returns ``None`` on failure."""
        if not _HAS_Z3:
            logger.debug("Z3 not available – skipping stage 2")
            return None

        t0 = time.perf_counter()
        try:
            formula = self._encode(obligation)
            if formula is None:
                return None

            solver = z3.Solver()
            solver.set("timeout", self._timeout_ms)
            # We try to prove ``obligation`` by showing its negation is UNSAT.
            solver.add(z3.Not(formula))

            result = solver.check()
            elapsed = (time.perf_counter() - t0) * 1000

            if result == z3.unsat:
                lean_proof = self._extract_and_translate(solver, obligation)
                return DischargeResult(
                    obligation_id=obligation.id,
                    stage=DischargeStage.Z3,
                    discharged=True,
                    proof=lean_proof,
                    trust_level="Z3_VERIFIED",
                    confidence=0.95,
                    time_ms=elapsed,
                )
            if result == z3.sat:
                logger.debug("Z3 found counter-model for %s", obligation.id)
                return None
            # unknown / timeout
            logger.debug("Z3 returned unknown for %s", obligation.id)
            return None
        except Exception as exc:  # noqa: BLE001
            elapsed = (time.perf_counter() - t0) * 1000
            logger.warning("Z3 stage error for %s: %s", obligation.id, exc)
            return None

    # -----------------------------------------------------------------
    # Encoding helpers
    # -----------------------------------------------------------------

    def _encode(self, obligation: ProofObligation) -> Optional[Any]:
        """Best-effort encoding of *lean_statement* into Z3."""
        stmt = obligation.lean_statement.strip()

        # Very simple pattern-based encoding for common shapes.
        encoded = self._try_arithmetic_encoding(stmt, obligation.variables)
        if encoded is not None:
            return encoded

        encoded = self._try_boolean_encoding(stmt)
        if encoded is not None:
            return encoded

        encoded = self._try_equality_encoding(stmt, obligation.variables)
        if encoded is not None:
            return encoded

        return None

    def _try_arithmetic_encoding(
        self, stmt: str, variables: Dict[str, str]
    ) -> Optional[Any]:
        """Encode simple linear-arithmetic statements."""
        if not _HAS_Z3:
            return None

        arith_ops = {"≤", "≥", "<", ">", "=", "+", "-", "*"}
        if not any(op in stmt for op in arith_ops):
            return None

        z3_vars: Dict[str, Any] = {}
        for name, sort in variables.items():
            if sort in ("Nat", "ℕ", "Int", "ℤ"):
                z3_vars[name] = z3.Int(name)
            elif sort in ("Float", "Real", "ℝ"):
                z3_vars[name] = z3.Real(name)

        if not z3_vars:
            # Attempt to extract variable names from the statement
            tokens = re.findall(r"\b([a-z_]\w*)\b", stmt)
            for tok in tokens:
                if tok not in z3_vars and tok not in ("Nat", "Int", "True", "False"):
                    z3_vars[tok] = z3.Int(tok)

        if not z3_vars:
            return None

        try:
            formula = self._parse_arith_formula(stmt, z3_vars)
            return formula
        except Exception:  # noqa: BLE001
            return None

    def _parse_arith_formula(self, stmt: str, z3_vars: Dict[str, Any]) -> Optional[Any]:
        """Parse a simple arithmetic relation into a Z3 formula."""
        if not _HAS_Z3:
            return None

        # Normalise unicode
        stmt = (
            stmt.replace("≤", "<=")
            .replace("≥", ">=")
            .replace("∧", " and ")
            .replace("∨", " or ")
            .replace("¬", " not ")
        )

        # Handle conjunction / disjunction at the top level
        if " and " in stmt:
            parts = stmt.split(" and ")
            subs = [self._parse_arith_formula(p.strip(), z3_vars) for p in parts]
            if all(s is not None for s in subs):
                return z3.And(*subs)
            return None
        if " or " in stmt:
            parts = stmt.split(" or ")
            subs = [self._parse_arith_formula(p.strip(), z3_vars) for p in parts]
            if all(s is not None for s in subs):
                return z3.Or(*subs)
            return None

        for op, builder in [
            ("<=", lambda a, b: a <= b),
            (">=", lambda a, b: a >= b),
            ("<", lambda a, b: a < b),
            (">", lambda a, b: a > b),
            ("=", lambda a, b: a == b),
        ]:
            if op in stmt:
                lhs_s, rhs_s = stmt.split(op, 1)
                lhs = self._arith_expr(lhs_s.strip(), z3_vars)
                rhs = self._arith_expr(rhs_s.strip(), z3_vars)
                if lhs is not None and rhs is not None:
                    return builder(lhs, rhs)

        return None

    def _arith_expr(self, s: str, z3_vars: Dict[str, Any]) -> Optional[Any]:
        """Parse a simple arithmetic expression into a Z3 ArithRef."""
        s = s.strip()
        if not s:
            return None

        # Integer literal
        try:
            return z3.IntVal(int(s))
        except (ValueError, TypeError):
            pass

        # Variable
        if s in z3_vars:
            return z3_vars[s]

        # a + b
        if "+" in s:
            parts = s.rsplit("+", 1)
            a = self._arith_expr(parts[0], z3_vars)
            b = self._arith_expr(parts[1], z3_vars)
            if a is not None and b is not None:
                return a + b

        # a - b
        if "-" in s and not s.startswith("-"):
            parts = s.rsplit("-", 1)
            a = self._arith_expr(parts[0], z3_vars)
            b = self._arith_expr(parts[1], z3_vars)
            if a is not None and b is not None:
                return a - b

        # a * b
        if "*" in s:
            parts = s.rsplit("*", 1)
            a = self._arith_expr(parts[0], z3_vars)
            b = self._arith_expr(parts[1], z3_vars)
            if a is not None and b is not None:
                return a * b

        return None

    def _try_boolean_encoding(self, stmt: str) -> Optional[Any]:
        """Encode simple propositional logic statements."""
        if not _HAS_Z3:
            return None

        if stmt.strip() in ("True", "⊤"):
            return z3.BoolVal(True)
        if stmt.strip() in ("False", "⊥"):
            return z3.BoolVal(False)

        # P ∨ ¬P
        m = re.match(
            r"^([A-Za-z_]\w*)\s*∨\s*¬\s*\1$|^¬\s*([A-Za-z_]\w*)\s*∨\s*\2$", stmt
        )
        if m:
            name = m.group(1) or m.group(2)
            p = z3.Bool(name)
            return z3.Or(p, z3.Not(p))

        return None

    def _try_equality_encoding(
        self, stmt: str, variables: Dict[str, str]
    ) -> Optional[Any]:
        """Encode simple equality / inequality statements."""
        if not _HAS_Z3:
            return None

        if "=" in stmt and "≤" not in stmt and "≥" not in stmt:
            parts = stmt.split("=", 1)
            lhs, rhs = parts[0].strip(), parts[1].strip()
            if lhs == rhs:
                v = z3.Int(lhs) if lhs in variables else z3.Int(lhs)
                return v == v
        return None

    # -----------------------------------------------------------------
    # Proof extraction + translation
    # -----------------------------------------------------------------

    def _extract_and_translate(
        self, solver: Any, obligation: ProofObligation
    ) -> str:
        """Best-effort extraction of Z3 proof into a Lean tactic string."""
        stmt = obligation.lean_statement.strip()

        # If the obligation looks arithmetic, omega/linarith are good bets.
        arith_indicators = {"≤", "≥", "<", ">", "+", "-", "*", "0", "1"}
        if any(c in stmt for c in arith_indicators):
            return "omega"

        # Boolean / propositional
        if any(kw in stmt for kw in ("∨", "∧", "¬", "→", "↔")):
            return "decide"

        # Equality
        if "=" in stmt:
            return "rfl"

        return "sorry /- Z3 proved UNSAT but translation failed -/"


# ═══════════════════════════════════════════════════════════════════════════
# LLM Prover helper (stage 3) – thin adapter; heavy lifting in llm_prover.py
# ═══════════════════════════════════════════════════════════════════════════


class _LLMStage:
    """Adapter between the cascade and the full LLM prover module."""

    def __init__(
        self,
        *,
        max_attempts: int = 3,
        model: str = "gpt-4",
        llm_call: Optional[Callable[..., str]] = None,
        lean_check_call: Optional[Callable[..., Dict]] = None,
    ) -> None:
        self._max_attempts = max_attempts
        self._model = model
        self._llm_call = llm_call
        self._lean_check_call = lean_check_call

    def attempt(self, obligation: ProofObligation) -> Optional[DischargeResult]:
        if self._llm_call is None:
            logger.debug("No LLM callback configured – skipping stage 3")
            return None

        t0 = time.perf_counter()
        errors: List[str] = []

        for attempt_idx in range(1, self._max_attempts + 1):
            prompt = self._build_prompt(obligation, attempt_idx, errors)
            try:
                raw_response = self._llm_call(prompt, model=self._model)
            except Exception as exc:  # noqa: BLE001
                errors.append(f"LLM call error: {exc}")
                continue

            proof = self._extract_proof(raw_response)
            if proof is None:
                errors.append("Could not parse proof from LLM response")
                continue

            # Optional Lean check
            if self._lean_check_call is not None:
                check = self._lean_check_call(obligation.lean_statement, proof)
                if check.get("ok"):
                    elapsed = (time.perf_counter() - t0) * 1000
                    return DischargeResult(
                        obligation_id=obligation.id,
                        stage=DischargeStage.LLM_PROVER,
                        discharged=True,
                        proof=proof,
                        trust_level="LLM_LEAN_VERIFIED",
                        confidence=0.85,
                        time_ms=elapsed,
                        attempts=attempt_idx,
                        _llm_raw_response=raw_response,
                    )
                errors.append(check.get("error", "Lean check failed"))
            else:
                # No Lean check available – accept with lower trust
                elapsed = (time.perf_counter() - t0) * 1000
                return DischargeResult(
                    obligation_id=obligation.id,
                    stage=DischargeStage.LLM_PROVER,
                    discharged=True,
                    proof=proof,
                    trust_level="LLM_UNVERIFIED",
                    confidence=0.5,
                    time_ms=elapsed,
                    attempts=attempt_idx,
                    _llm_raw_response=raw_response,
                )

        return None

    # -----------------------------------------------------------------

    def _build_prompt(
        self,
        obligation: ProofObligation,
        attempt: int,
        prev_errors: List[str],
    ) -> str:
        parts: List[str] = [
            "You are a Lean 4 theorem prover.  Produce ONLY a tactic proof.",
            "",
            f"-- Theorem statement:\n{obligation.lean_statement}",
            "",
        ]
        if obligation.hypotheses:
            parts.append("-- Available hypotheses:")
            for h in obligation.hypotheses:
                parts.append(f"  {h}")
            parts.append("")
        if obligation.available_lemmas:
            parts.append("-- Potentially useful lemmas:")
            for lem in obligation.available_lemmas:
                parts.append(f"  {lem}")
            parts.append("")
        if obligation.variables:
            parts.append("-- Variables and types:")
            for v, t in obligation.variables.items():
                parts.append(f"  {v} : {t}")
            parts.append("")
        if prev_errors:
            parts.append(f"-- This is attempt {attempt}.  Previous errors:")
            for err in prev_errors[-3:]:
                parts.append(f"  {err}")
            parts.append("")
        parts.append("Respond with ONLY the tactic proof (inside `by ... `).")
        return "\n".join(parts)

    @staticmethod
    def _extract_proof(response: str) -> Optional[str]:
        """Extract a Lean proof from an LLM response."""
        # Try fenced code block first
        m = re.search(r"```(?:lean4?|proof)?\s*\n(.*?)```", response, re.DOTALL)
        if m:
            return m.group(1).strip()

        # Try "by ..." block
        m = re.search(r"(by\b.*)", response, re.DOTALL)
        if m:
            return m.group(1).strip()

        # Try bare tactic (single line)
        lines = [ln.strip() for ln in response.splitlines() if ln.strip()]
        if len(lines) == 1:
            return lines[0]

        return None


# ═══════════════════════════════════════════════════════════════════════════
# Lean Check helper (stage 4)
# ═══════════════════════════════════════════════════════════════════════════


class _LeanCheckStage:
    """Submit a proof to the Lean kernel (or try automated tactics)."""

    _AUTO_TACTICS: List[str] = ["decide", "omega", "simp", "aesop"]

    def __init__(
        self,
        timeout_ms: int = 10000,
        lean_check_call: Optional[Callable[..., Dict]] = None,
    ) -> None:
        self._timeout_ms = timeout_ms
        self._lean_check_call = lean_check_call

    def attempt(
        self, obligation: ProofObligation, prior_proof: Optional[str] = None
    ) -> Optional[DischargeResult]:
        if self._lean_check_call is None:
            logger.debug("No Lean check callback – skipping stage 4")
            return None

        t0 = time.perf_counter()

        # If we have a proof from a previous stage, try it first.
        if prior_proof is not None:
            check = self._lean_check_call(obligation.lean_statement, prior_proof)
            if check.get("ok"):
                elapsed = (time.perf_counter() - t0) * 1000
                return DischargeResult(
                    obligation_id=obligation.id,
                    stage=DischargeStage.LEAN_CHECK,
                    discharged=True,
                    proof=prior_proof,
                    trust_level="LEAN_KERNEL_VERIFIED",
                    confidence=1.0,
                    time_ms=elapsed,
                )

        # Otherwise try automated tactics.
        for tactic in self._AUTO_TACTICS:
            proof = f"by {tactic}"
            check = self._lean_check_call(obligation.lean_statement, proof)
            if check.get("ok"):
                elapsed = (time.perf_counter() - t0) * 1000
                return DischargeResult(
                    obligation_id=obligation.id,
                    stage=DischargeStage.LEAN_CHECK,
                    discharged=True,
                    proof=proof,
                    trust_level="LEAN_KERNEL_VERIFIED",
                    confidence=1.0,
                    time_ms=elapsed,
                )

        return None


# ═══════════════════════════════════════════════════════════════════════════
# CascadeReport
# ═══════════════════════════════════════════════════════════════════════════


@dataclass
class CascadeReport:
    """Aggregate statistics after discharging a batch of obligations."""

    obligations: int = 0
    discharged: int = 0
    trivial: int = 0
    z3: int = 0
    llm: int = 0
    lean: int = 0
    residual: int = 0
    total_time_ms: float = 0.0
    llm_tokens_used: int = 0

    results: List[DischargeResult] = field(default_factory=list, repr=False)

    def record(self, result: DischargeResult) -> None:
        self.results.append(result)
        self.obligations += 1
        self.total_time_ms += result.time_ms
        if result.discharged:
            self.discharged += 1
        stage_counter = {
            DischargeStage.TRIVIAL: "trivial",
            DischargeStage.Z3: "z3",
            DischargeStage.LLM_PROVER: "llm",
            DischargeStage.LEAN_CHECK: "lean",
            DischargeStage.RESIDUAL: "residual",
        }
        attr = stage_counter.get(result.stage)
        if attr:
            setattr(self, attr, getattr(self, attr) + 1)

    @property
    def discharge_rate(self) -> float:
        return self.discharged / self.obligations if self.obligations else 0.0

    def summary(self) -> str:
        lines = [
            "╔═══════════════════════════════════════════╗",
            "║       Discharge Cascade Report            ║",
            "╠═══════════════════════════════════════════╣",
            f"║  Obligations     : {self.obligations:<22d}║",
            f"║  Discharged      : {self.discharged:<22d}║",
            f"║  Rate            : {self.discharge_rate:>6.1%}{'':<15}║",
            "╠═══════════════════════════════════════════╣",
            f"║  Trivial         : {self.trivial:<22d}║",
            f"║  Z3              : {self.z3:<22d}║",
            f"║  LLM prover      : {self.llm:<22d}║",
            f"║  Lean check      : {self.lean:<22d}║",
            f"║  Residual (sorry): {self.residual:<22d}║",
            "╠═══════════════════════════════════════════╣",
            f"║  Total time      : {self.total_time_ms:>10.1f} ms{'':<8}║",
            f"║  LLM tokens      : {self.llm_tokens_used:<22d}║",
            "╚═══════════════════════════════════════════╝",
        ]
        return "\n".join(lines)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "obligations": self.obligations,
            "discharged": self.discharged,
            "trivial": self.trivial,
            "z3": self.z3,
            "llm": self.llm,
            "lean": self.lean,
            "residual": self.residual,
            "total_time_ms": round(self.total_time_ms, 3),
            "llm_tokens_used": self.llm_tokens_used,
            "discharge_rate": round(self.discharge_rate, 4),
            "results": [r.to_dict() for r in self.results],
        }

    def __str__(self) -> str:
        return self.summary()


# ═══════════════════════════════════════════════════════════════════════════
# DischargeCascade — main orchestrator
# ═══════════════════════════════════════════════════════════════════════════


class DischargeCascade:
    """Five-stage proof discharge cascade.

    Stage 1 – **Trivial** : pattern-match against known trivialities.
    Stage 2 – **Z3**      : encode as Z3 formula, check UNSAT of negation.
    Stage 3 – **LLM**     : prompt an LLM to generate a Lean proof (CEGAR loop).
    Stage 4 – **Lean**    : submit to the Lean kernel / try automated tactics.
    Stage 5 – **Residual**: mark as ``sorry`` with ``trust_level = ASSUMED``.
    """

    def __init__(self, config: Optional[DischargeCascadeConfig] = None) -> None:
        self._cfg = config or DischargeCascadeConfig()
        self._trivial = TrivialDischarger()
        self._z3 = _Z3Stage(timeout_ms=self._cfg.z3_timeout_ms)
        self._llm = _LLMStage(
            max_attempts=self._cfg.llm_max_attempts,
            model=self._cfg.llm_model,
            llm_call=self._cfg.llm_call,
            lean_check_call=self._cfg.lean_check_call,
        )
        self._lean = _LeanCheckStage(
            timeout_ms=self._cfg.lean_timeout_ms,
            lean_check_call=self._cfg.lean_check_call,
        )
        self._cache: Dict[str, DischargeResult] = {}

    # -----------------------------------------------------------------
    # Single obligation
    # -----------------------------------------------------------------

    def discharge(self, obligation: ProofObligation) -> DischargeResult:
        """Run *obligation* through the 5-stage cascade, returning the first
        stage that successfully discharges it (or a residual result)."""
        fp = obligation.fingerprint()
        if fp in self._cache:
            logger.debug("Cache hit for %s", obligation.id)
            cached = self._cache[fp]
            return DischargeResult(
                obligation_id=obligation.id,
                stage=cached.stage,
                discharged=cached.discharged,
                proof=cached.proof,
                trust_level=cached.trust_level,
                confidence=cached.confidence,
                time_ms=0.0,
                attempts=0,
            )

        t0 = time.perf_counter()
        result = self._run_stages(obligation)
        result.time_ms = (time.perf_counter() - t0) * 1000

        self._cache[fp] = result
        return result

    def _run_stages(self, obligation: ProofObligation) -> DischargeResult:
        """Execute stages sequentially, stopping at first success."""

        # ── Stage 1: Trivial ──────────────────────────────────────────
        t0 = time.perf_counter()
        proof = TrivialDischarger.try_discharge(obligation)
        if proof is not None:
            return DischargeResult.trivial(
                obligation.id, proof, (time.perf_counter() - t0) * 1000
            )

        # ── Stage 2: Z3 ──────────────────────────────────────────────
        if not self._cfg.skip_z3:
            z3_result = self._z3.attempt(obligation)
            if z3_result is not None and z3_result.discharged:
                return z3_result

        # ── Stage 3: LLM prover ──────────────────────────────────────
        prior_proof: Optional[str] = None
        if not self._cfg.skip_llm:
            llm_result = self._llm.attempt(obligation)
            if llm_result is not None and llm_result.discharged:
                # If trust is high enough, accept immediately
                if llm_result.trust_level == "LLM_LEAN_VERIFIED":
                    return llm_result
                # Otherwise hold the proof for Lean checking
                prior_proof = llm_result.proof

        # ── Stage 4: Lean check ──────────────────────────────────────
        if not self._cfg.skip_lean_check:
            lean_result = self._lean.attempt(obligation, prior_proof=prior_proof)
            if lean_result is not None and lean_result.discharged:
                return lean_result

        # ── Stage 5: Residual ────────────────────────────────────────
        elapsed = 0.0  # time_ms is set by caller
        explanation = self._explain_residual(obligation)
        return DischargeResult.residual(obligation.id, explanation, elapsed)

    # -----------------------------------------------------------------
    # Batch discharge
    # -----------------------------------------------------------------

    def discharge_batch(
        self, obligations: List[ProofObligation]
    ) -> List[DischargeResult]:
        """Discharge a list of obligations.

        Structural obligations are attempted first (they are usually cheap).
        Within each group, obligations are sorted by descending priority.
        """
        if not obligations:
            return []

        structural = sorted(
            [o for o in obligations if o.structural],
            key=lambda o: -o.priority,
        )
        semantic = sorted(
            [o for o in obligations if not o.structural],
            key=lambda o: -o.priority,
        )

        ordered = structural + semantic
        results: List[DischargeResult] = []

        # Parallel discharge where possible
        if self._cfg.max_workers > 1 and len(ordered) > 1:
            with ThreadPoolExecutor(max_workers=self._cfg.max_workers) as pool:
                future_to_obl = {
                    pool.submit(self.discharge, obl): obl for obl in ordered
                }
                for future in as_completed(future_to_obl):
                    obl = future_to_obl[future]
                    try:
                        results.append(future.result())
                    except Exception as exc:  # noqa: BLE001
                        results.append(
                            DischargeResult.residual(
                                obl.id, f"Exception: {exc}", 0.0
                            )
                        )
        else:
            for obl in ordered:
                results.append(self.discharge(obl))

        # Re-order results to match original input order
        id_to_result = {r.obligation_id: r for r in results}
        return [id_to_result[o.id] for o in obligations if o.id in id_to_result]

    # -----------------------------------------------------------------
    # Reporting
    # -----------------------------------------------------------------

    def report(self, results: List[DischargeResult]) -> CascadeReport:
        rpt = CascadeReport()
        for r in results:
            rpt.record(r)
        return rpt

    # -----------------------------------------------------------------
    # Helpers
    # -----------------------------------------------------------------

    @staticmethod
    def _explain_residual(obligation: ProofObligation) -> str:
        """Human-readable explanation of what remains to prove."""
        parts: List[str] = [
            f"Obligation '{obligation.id}' could not be automatically discharged.",
            f"Statement: {obligation.lean_statement}",
        ]
        if obligation.hypotheses:
            parts.append(f"Available hypotheses: {', '.join(obligation.hypotheses)}")
        if obligation.source:
            parts.append(f"Origin: {obligation.source}")
        parts.append(
            "Manual proof required.  Consider using interactive Lean mode, "
            "or provide additional lemmas / hypotheses."
        )
        return "\n".join(parts)

    def clear_cache(self) -> None:
        self._cache.clear()

    @property
    def config(self) -> DischargeCascadeConfig:
        return self._cfg


# ═══════════════════════════════════════════════════════════════════════════
# Convenience factory
# ═══════════════════════════════════════════════════════════════════════════


def make_cascade(
    *,
    z3_timeout_ms: int = 5000,
    llm_max_attempts: int = 3,
    llm_model: str = "gpt-4",
    lean_timeout_ms: int = 10000,
    llm_call: Optional[Callable[..., str]] = None,
    lean_check_call: Optional[Callable[..., Dict]] = None,
) -> DischargeCascade:
    """Create a :class:`DischargeCascade` with common defaults."""
    cfg = DischargeCascadeConfig(
        z3_timeout_ms=z3_timeout_ms,
        llm_max_attempts=llm_max_attempts,
        llm_model=llm_model,
        lean_timeout_ms=lean_timeout_ms,
        llm_call=llm_call,
        lean_check_call=lean_check_call,
    )
    return DischargeCascade(cfg)
