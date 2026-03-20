"""
Pillar 5 – LLM-as-theorem-prover with iterative CEGAR-style repair.

The LLM generates candidate Lean 4 proofs.  When a proof fails kernel
checking, the error is fed back to the LLM for refinement (counter-example
guided abstraction refinement loop).
"""
from __future__ import annotations


# --- Integration with existing deppy codebase ---
try:
    from deppy.solver import SolverObligation, SolverResult, SolverStatus
    from deppy.proof._protocols import ProofObligation as _CoreProofObligation
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

import enum
import logging
import re
import time
from dataclasses import dataclass, field
from typing import (

    Any,
    Callable,
    Dict,
    List,
    Optional,
    Sequence,
    Tuple,
)

logger = logging.getLogger(__name__)

# ═══════════════════════════════════════════════════════════════════════════
# ProverResult
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class ProverResult:
    """Outcome of an LLM proving attempt."""

    success: bool
    proof: Optional[str] = None
    attempts: int = 0
    errors: List[str] = field(default_factory=list)
    time_ms: float = 0.0
    tokens_used: int = 0
    trust_level: str = "LLM_UNVERIFIED"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "success": self.success,
            "proof": self.proof,
            "attempts": self.attempts,
            "errors": self.errors,
            "time_ms": round(self.time_ms, 3),
            "tokens_used": self.tokens_used,
            "trust_level": self.trust_level,
        }

    def __str__(self) -> str:
        status = "✓" if self.success else "✗"
        return (
            f"ProverResult({status}, attempts={self.attempts}, "
            f"{self.time_ms:.0f}ms, trust={self.trust_level})"
        )

# ═══════════════════════════════════════════════════════════════════════════
# ProofErrorKind
# ═══════════════════════════════════════════════════════════════════════════

class ProofErrorKind(enum.Enum):
    """Classified Lean error types for targeted repair."""

    TACTIC_FAILED = "tactic_failed"
    TYPE_MISMATCH = "type_mismatch"
    UNKNOWN_IDENTIFIER = "unknown_identifier"
    TIMEOUT = "timeout"
    SYNTAX_ERROR = "syntax_error"
    DECLARATION_ERROR = "declaration_error"
    KERNEL_ERROR = "kernel_error"
    UNKNOWN = "unknown"

# ═══════════════════════════════════════════════════════════════════════════
# ProofParser
# ═══════════════════════════════════════════════════════════════════════════

class ProofParser:
    """Parse and validate Lean proof text from LLM responses."""

    # Regex patterns for extracting proofs from LLM responses
    _CODE_BLOCK_RE = re.compile(
        r"```(?:lean4?|proof|text)?\s*\n(.*?)```", re.DOTALL
    )
    _BY_BLOCK_RE = re.compile(r"(by\s*\n(?:[ \t]+.+\n?)+)", re.MULTILINE)
    _INLINE_BY_RE = re.compile(r"(by\s+\S.*)", re.DOTALL)
    _EXACT_RE = re.compile(r"^(exact\s+.+)$", re.MULTILINE)

    # Common Lean error patterns
    _ERROR_PATTERNS: List[Tuple[re.Pattern, ProofErrorKind]] = [
        (re.compile(r"tactic .+ failed", re.IGNORECASE), ProofErrorKind.TACTIC_FAILED),
        (re.compile(r"unsolved goals", re.IGNORECASE), ProofErrorKind.TACTIC_FAILED),
        (
            re.compile(r"type mismatch", re.IGNORECASE),
            ProofErrorKind.TYPE_MISMATCH,
        ),
        (
            re.compile(r"has type.*but is expected to have type", re.IGNORECASE | re.DOTALL),
            ProofErrorKind.TYPE_MISMATCH,
        ),
        (
            re.compile(r"unknown (?:identifier|constant|declaration)", re.IGNORECASE),
            ProofErrorKind.UNKNOWN_IDENTIFIER,
        ),
        (
            re.compile(r"unknown tactic", re.IGNORECASE),
            ProofErrorKind.UNKNOWN_IDENTIFIER,
        ),
        (
            re.compile(r"(?:deterministic )?timeout", re.IGNORECASE),
            ProofErrorKind.TIMEOUT,
        ),
        (
            re.compile(r"maximum recursion depth", re.IGNORECASE),
            ProofErrorKind.TIMEOUT,
        ),
        (
            re.compile(r"expected .+ at .+", re.IGNORECASE),
            ProofErrorKind.SYNTAX_ERROR,
        ),
        (
            re.compile(r"unexpected token", re.IGNORECASE),
            ProofErrorKind.SYNTAX_ERROR,
        ),
        (
            re.compile(r"declaration .+ has already been declared", re.IGNORECASE),
            ProofErrorKind.DECLARATION_ERROR,
        ),
        (
            re.compile(r"kernel .+ error", re.IGNORECASE),
            ProofErrorKind.KERNEL_ERROR,
        ),
    ]

    # ------------------------------------------------------------------
    # Proof extraction
    # ------------------------------------------------------------------

    @classmethod
    def parse_proof_response(cls, response: str) -> Optional[str]:
        """Extract a Lean proof from an LLM response.

        The LLM may wrap the proof in markdown code fences, include
        explanatory text, or provide multiple variants.  We extract the
        most likely candidate.
        """
        if not response or not response.strip():
            return None

        # Strategy 1: fenced code block
        m = cls._CODE_BLOCK_RE.search(response)
        if m:
            proof = cls._clean_proof(m.group(1))
            if proof:
                return proof

        # Strategy 2: "by" block (multi-line, indented)
        m = cls._BY_BLOCK_RE.search(response)
        if m:
            proof = cls._clean_proof(m.group(1))
            if proof:
                return proof

        # Strategy 3: inline "by ..."
        m = cls._INLINE_BY_RE.search(response)
        if m:
            proof = cls._clean_proof(m.group(1))
            if proof:
                return proof

        # Strategy 4: exact ...
        m = cls._EXACT_RE.search(response)
        if m:
            return m.group(1).strip()

        # Strategy 5: single-line tactic
        lines = [
            ln.strip()
            for ln in response.strip().splitlines()
            if ln.strip() and not ln.strip().startswith("--")
        ]
        if len(lines) == 1:
            candidate = lines[0].strip()
            if cls._looks_like_tactic(candidate):
                return candidate

        # Strategy 6: look for "rfl", "trivial", "assumption" etc. anywhere
        for keyword in ("rfl", "trivial", "assumption", "omega", "simp", "decide"):
            if keyword in response.split():
                return keyword

        return None

    @classmethod
    def classify_error(cls, lean_error: str) -> ProofErrorKind:
        """Classify a Lean error message into a :class:`ProofErrorKind`."""
        for pattern, kind in cls._ERROR_PATTERNS:
            if pattern.search(lean_error):
                return kind
        return ProofErrorKind.UNKNOWN

    @classmethod
    def is_unfixable(cls, error_kind: ProofErrorKind) -> bool:
        """Heuristic: is the error likely unfixable by the LLM?"""
        return error_kind in (
            ProofErrorKind.DECLARATION_ERROR,
            ProofErrorKind.KERNEL_ERROR,
        )

    # ------------------------------------------------------------------
    # Helpers
    # ------------------------------------------------------------------

    @staticmethod
    def _clean_proof(raw: str) -> Optional[str]:
        """Strip boilerplate from a proof candidate."""
        lines: List[str] = []
        for line in raw.strip().splitlines():
            stripped = line.rstrip()
            # Skip comment-only lines at the start/end
            if not lines and stripped.startswith("--"):
                continue
            # Skip "theorem ..." header
            if stripped.startswith("theorem ") or stripped.startswith("lemma "):
                continue
            # Skip "import" / "open"
            if stripped.startswith("import ") or stripped.startswith("open "):
                continue
            lines.append(stripped)
        # Remove trailing comment lines
        while lines and lines[-1].strip().startswith("--"):
            lines.pop()

        result = "\n".join(lines).strip()
        return result if result else None

    @staticmethod
    def _looks_like_tactic(s: str) -> bool:
        """Quick check: does *s* resemble a Lean tactic?"""
        TACTIC_STARTERS = {
            "by",
            "exact",
            "apply",
            "intro",
            "intros",
            "rfl",
            "trivial",
            "assumption",
            "omega",
            "linarith",
            "simp",
            "aesop",
            "decide",
            "ring",
            "norm_num",
            "push_neg",
            "contrapose",
            "contradiction",
            "constructor",
            "rcases",
            "obtain",
            "have",
            "let",
            "show",
            "calc",
            "induction",
            "cases",
            "match",
            "sorry",
            "rw",
            "conv",
            "ext",
            "funext",
            "congr",
            "trans",
            "symm",
            "use",
            "refine",
            "specialize",
            "revert",
            "clear",
            "rename_i",
            "subst",
            "unfold",
            "dsimp",
            "change",
            "suffices",
            "classical",
            "gcongr",
            "nlinarith",
            "field_simp",
            "norm_cast",
            "positivity",
            "polyrith",
            "mono",
        }
        first_word = s.split()[0] if s.split() else ""
        return first_word in TACTIC_STARTERS

# ═══════════════════════════════════════════════════════════════════════════
# PromptBuilder
# ═══════════════════════════════════════════════════════════════════════════

class PromptBuilder:
    """Build structured prompts for the LLM theorem prover."""

    _SYSTEM_PREAMBLE = (
        "You are an expert Lean 4 theorem prover.  Given a theorem statement, "
        "hypotheses, and context, produce a correct tactic proof.  Respond with "
        "ONLY the proof (tactic block starting with `by`).  Do NOT include "
        "theorem declarations, imports, or explanatory text."
    )

    _RETRY_ADDENDUM = (
        "\nYour previous proof attempt was REJECTED by the Lean kernel.  "
        "Carefully study the error message below and fix the proof.  "
        "Do NOT repeat the same mistake."
    )

    # ------------------------------------------------------------------
    # Proof prompt
    # ------------------------------------------------------------------

    @classmethod
    def build_proof_prompt(
        cls,
        obligation: str,
        context: Dict[str, Any],
        attempt: int = 1,
        prev_errors: Optional[List[str]] = None,
    ) -> str:
        """Build the full prompt for a proof attempt.

        Parameters
        ----------
        obligation : str
            The Lean theorem statement to prove.
        context : dict
            Keys may include ``hypotheses``, ``variables``, ``lemmas``,
            ``types``, ``hint``.
        attempt : int
            Which attempt this is (1-based).
        prev_errors : list[str] or None
            Error messages from previous (failed) attempts.
        """
        sections: List[str] = [cls._SYSTEM_PREAMBLE, ""]

        if attempt > 1 and prev_errors:
            sections.append(cls._RETRY_ADDENDUM)
            sections.append("")

        # Theorem statement
        sections.append("## Theorem to prove")
        sections.append(f"```lean4\n{obligation}\n```")
        sections.append("")

        # Hypotheses
        hypotheses = context.get("hypotheses", [])
        if hypotheses:
            sections.append("## Available hypotheses")
            for h in hypotheses:
                sections.append(f"- `{h}`")
            sections.append("")

        # Variables and types
        variables = context.get("variables", {})
        if variables:
            sections.append("## Variables")
            for name, ty in variables.items():
                sections.append(f"- `{name} : {ty}`")
            sections.append("")

        # Available lemmas
        lemmas = context.get("lemmas", [])
        if lemmas:
            sections.append("## Potentially useful lemmas")
            for lem in lemmas:
                sections.append(f"- `{lem}`")
            sections.append("")

        # Type context
        types = context.get("types", {})
        if types:
            sections.append("## Type definitions")
            for name, defn in types.items():
                sections.append(f"- `{name}`: {defn}")
            sections.append("")

        # Hint
        hint = context.get("hint")
        if hint:
            sections.append(f"**Hint:** {hint}")
            sections.append("")

        # Tactical hints based on obligation shape
        tactic_hint = cls._suggest_tactic_hint(obligation)
        if tactic_hint:
            sections.append(f"**Suggested approach:** {tactic_hint}")
            sections.append("")

        # Previous errors (on retry)
        if prev_errors and attempt > 1:
            sections.append("## Previous errors (most recent first)")
            for i, err in enumerate(reversed(prev_errors[-3:]), 1):
                sections.append(f"### Error {i}")
                sections.append(f"```\n{err[:500]}\n```")
            sections.append("")

        sections.append(
            f"This is attempt {attempt}.  Produce ONLY the tactic proof "
            f"(a `by` block).  No explanations."
        )

        return "\n".join(sections)

    # ------------------------------------------------------------------
    # Lemma search prompt
    # ------------------------------------------------------------------

    @classmethod
    def build_lemma_search_prompt(cls, goal: str) -> str:
        """Build a prompt for suggesting useful Mathlib lemmas."""
        return (
            "You are an expert in Lean 4 and Mathlib.  Given the following "
            "proof goal, suggest up to 5 Mathlib lemmas (fully qualified names) "
            "that would be most useful for proving it.  Respond with ONLY the "
            "lemma names, one per line.\n\n"
            f"Goal: {goal}\n\n"
            "Suggested lemmas:"
        )

    # ------------------------------------------------------------------
    # Decomposition prompt
    # ------------------------------------------------------------------

    @classmethod
    def build_decomposition_prompt(cls, complex_goal: str) -> str:
        """Build a prompt for decomposing a complex goal into sub-goals."""
        return (
            "You are an expert Lean 4 theorem prover.  The following proof "
            "goal is complex.  Decompose it into simpler sub-goals that, "
            "if proved individually, would combine to prove the main goal.  "
            "Respond with each sub-goal on a separate line, in Lean 4 syntax.\n\n"
            f"Main goal:\n```lean4\n{complex_goal}\n```\n\n"
            "Sub-goals:"
        )

    # ------------------------------------------------------------------
    # Helpers
    # ------------------------------------------------------------------

    @staticmethod
    def _suggest_tactic_hint(obligation: str) -> Optional[str]:
        """Suggest a tactic based on the shape of the obligation."""
        stmt = obligation.strip()
        if "=" in stmt and "≤" not in stmt and "≥" not in stmt:
            if any(kw in stmt for kw in ("+", "-", "*", "Nat", "Int")):
                return "Try `omega`, `ring`, or `simp [Nat.add_comm]`."
            return "Try `rfl`, `simp`, or `ext`."
        if any(op in stmt for op in ("≤", "≥", "<", ">")):
            return "Try `omega`, `linarith`, or `Nat.le_of_lt`."
        if "∀" in stmt:
            return "Start with `intro` to introduce the universally quantified variable."
        if "∃" in stmt:
            return "Use `use <witness>` to provide the existential witness."
        if "∧" in stmt:
            return "Use `constructor` or `And.intro` to split the conjunction."
        if "∨" in stmt:
            return "Use `left` or `right` to pick a disjunct."
        if "¬" in stmt:
            return "Try `intro h` then derive a contradiction."
        if "↔" in stmt:
            return "Use `constructor` to prove both directions."
        if "List" in stmt or "Array" in stmt:
            return "Try `simp`, `induction`, or `cases`."
        return None

# ═══════════════════════════════════════════════════════════════════════════
# CEGARLoop
# ═══════════════════════════════════════════════════════════════════════════

class CEGARLoop:
    """Counter-Example Guided Abstraction Refinement loop for proof repair.

    Iteratively asks the LLM for a proof, checks it, and feeds errors back
    until the proof is accepted or attempts are exhausted.
    """

    def __init__(
        self,
        max_attempts: int = 3,
        prover: Optional[LLMProver] = None,
    ) -> None:
        self._max_attempts = max_attempts
        self._prover = prover

    def run(
        self,
        obligation: Dict[str, Any],
        oracle_fn: Optional[Callable[[str, str], Dict[str, Any]]] = None,
    ) -> ProverResult:
        """Execute the CEGAR loop.

        Parameters
        ----------
        obligation : dict
            Must contain ``lean_statement`` and optionally ``context``.
        oracle_fn : callable or None
            ``oracle_fn(statement, proof) -> {"ok": bool, "error": str}``.
        """
        if self._prover is None:
            return ProverResult(
                success=False,
                errors=["No LLM prover configured for CEGAR loop"],
            )

        t0 = time.perf_counter()
        errors: List[str] = []
        best_proof: Optional[str] = None
        best_confidence = 0.0
        total_tokens = 0

        for attempt in range(1, self._max_attempts + 1):
            result = self._prover.prove(
                obligation=obligation,
                context=obligation.get("context", {}),
                oracle_fn=oracle_fn,
                _attempt_override=attempt,
                _prev_errors_override=errors,
            )
            total_tokens += result.tokens_used

            if result.success:
                result.time_ms = (time.perf_counter() - t0) * 1000
                result.tokens_used = total_tokens
                result.attempts = attempt
                return result

            # Collect the error
            if result.errors:
                last_err = result.errors[-1]
                errors.append(last_err)

                # Check if unfixable
                kind = ProofParser.classify_error(last_err)
                if ProofParser.is_unfixable(kind):
                    logger.info(
                        "CEGAR: unfixable error kind %s on attempt %d – stopping",
                        kind.value,
                        attempt,
                    )
                    break

            # Track best so far
            if result.proof and not best_proof:
                best_proof = result.proof

        elapsed = (time.perf_counter() - t0) * 1000
        return ProverResult(
            success=False,
            proof=best_proof,
            attempts=self._max_attempts,
            errors=errors,
            time_ms=elapsed,
            tokens_used=total_tokens,
            trust_level="LLM_FAILED",
        )

# ═══════════════════════════════════════════════════════════════════════════
# LLMProver — main class
# ═══════════════════════════════════════════════════════════════════════════

class LLMProver:
    """LLM-based theorem prover with CEGAR-style iterative repair.

    Requires an ``llm_call`` callback:
        ``llm_call(prompt: str, *, model: str) -> str``

    Optionally accepts an ``oracle_fn`` for Lean kernel checking:
        ``oracle_fn(statement: str, proof: str) -> {"ok": bool, "error": str}``
    """

    def __init__(
        self,
        *,
        llm_call: Optional[Callable[..., str]] = None,
        model: str = "gpt-4",
        max_attempts: int = 3,
        lean_check_fn: Optional[Callable[..., Dict[str, Any]]] = None,
    ) -> None:
        self._llm_call = llm_call
        self._model = model
        self._max_attempts = max_attempts
        self._lean_check_fn = lean_check_fn
        self._prompt_builder = PromptBuilder()
        self._parser = ProofParser()

    # ------------------------------------------------------------------
    # Single obligation
    # ------------------------------------------------------------------

    def prove(
        self,
        obligation: Dict[str, Any],
        context: Optional[Dict[str, Any]] = None,
        oracle_fn: Optional[Callable[[str, str], Dict[str, Any]]] = None,
        *,
        _attempt_override: Optional[int] = None,
        _prev_errors_override: Optional[List[str]] = None,
    ) -> ProverResult:
        """Attempt to prove *obligation* using the LLM.

        Parameters
        ----------
        obligation : dict
            Must have ``lean_statement``.  May have ``hypotheses``,
            ``variables``, ``available_lemmas``.
        context : dict or None
            Additional context (merged with obligation-level context).
        oracle_fn : callable or None
            If provided, used to Lean-check candidate proofs.
        """
        if self._llm_call is None:
            return ProverResult(
                success=False,
                errors=["No LLM callback configured"],
                trust_level="NO_LLM",
            )

        oracle = oracle_fn or self._lean_check_fn

        stmt = obligation.get("lean_statement", "")
        ctx = {**(context or {})}
        # Merge obligation-level context
        if "hypotheses" in obligation:
            ctx.setdefault("hypotheses", obligation["hypotheses"])
        if "variables" in obligation:
            ctx.setdefault("variables", obligation["variables"])
        if "available_lemmas" in obligation:
            ctx.setdefault("lemmas", obligation["available_lemmas"])

        t0 = time.perf_counter()
        errors: List[str] = _prev_errors_override if _prev_errors_override is not None else []
        attempt_start = _attempt_override if _attempt_override is not None else 1
        total_tokens = 0

        for attempt in range(attempt_start, attempt_start + 1):
            # Build prompt
            prompt = self._prompt_builder.build_proof_prompt(
                obligation=stmt,
                context=ctx,
                attempt=attempt,
                prev_errors=errors if errors else None,
            )

            # Call LLM
            try:
                raw_response = self._llm_call(prompt, model=self._model)
            except Exception as exc:  # noqa: BLE001
                errors.append(f"LLM call failed: {exc}")
                continue

            total_tokens += self._estimate_tokens(raw_response)

            # Parse proof
            proof = self._parser.parse_proof_response(raw_response)
            if proof is None:
                errors.append("Could not extract proof from LLM response")
                continue

            # Validate with oracle if available
            if oracle is not None:
                try:
                    check = oracle(stmt, proof)
                except Exception as exc:  # noqa: BLE001
                    errors.append(f"Oracle check error: {exc}")
                    continue

                if check.get("ok"):
                    elapsed = (time.perf_counter() - t0) * 1000
                    return ProverResult(
                        success=True,
                        proof=proof,
                        attempts=attempt,
                        errors=errors,
                        time_ms=elapsed,
                        tokens_used=total_tokens,
                        trust_level="LLM_LEAN_VERIFIED",
                    )
                else:
                    err = check.get("error", "Lean check failed (no details)")
                    errors.append(err)
                    continue
            else:
                # No oracle – accept with lower trust
                elapsed = (time.perf_counter() - t0) * 1000
                return ProverResult(
                    success=True,
                    proof=proof,
                    attempts=attempt,
                    errors=errors,
                    time_ms=elapsed,
                    tokens_used=total_tokens,
                    trust_level="LLM_UNVERIFIED",
                )

        elapsed = (time.perf_counter() - t0) * 1000
        return ProverResult(
            success=False,
            proof=None,
            attempts=attempt_start,
            errors=errors,
            time_ms=elapsed,
            tokens_used=total_tokens,
            trust_level="LLM_FAILED",
        )

    # ------------------------------------------------------------------
    # Batch
    # ------------------------------------------------------------------

    def prove_batch(
        self,
        obligations: List[Dict[str, Any]],
        oracle_fn: Optional[Callable[[str, str], Dict[str, Any]]] = None,
    ) -> List[ProverResult]:
        """Prove a list of obligations sequentially."""
        results: List[ProverResult] = []
        for obl in obligations:
            ctx = obl.get("context", {})
            results.append(self.prove(obl, context=ctx, oracle_fn=oracle_fn))
        return results

    # ------------------------------------------------------------------
    # Lemma suggestion
    # ------------------------------------------------------------------

    def suggest_lemmas(self, obligation: str) -> List[str]:
        """Ask the LLM to suggest useful Mathlib lemmas for *obligation*."""
        if self._llm_call is None:
            return []

        prompt = self._prompt_builder.build_lemma_search_prompt(obligation)
        try:
            response = self._llm_call(prompt, model=self._model)
        except Exception:  # noqa: BLE001
            return []

        lemmas: List[str] = []
        for line in response.strip().splitlines():
            line = line.strip().lstrip("- ").lstrip("* ").strip("`")
            if line and not line.startswith("#"):
                lemmas.append(line)
        return lemmas[:10]

    # ------------------------------------------------------------------
    # Goal decomposition
    # ------------------------------------------------------------------

    def decompose(self, obligation: str) -> List[str]:
        """Ask the LLM to decompose a complex goal into sub-goals."""
        if self._llm_call is None:
            return []

        prompt = self._prompt_builder.build_decomposition_prompt(obligation)
        try:
            response = self._llm_call(prompt, model=self._model)
        except Exception:  # noqa: BLE001
            return []

        subgoals: List[str] = []
        for line in response.strip().splitlines():
            line = line.strip().lstrip("- ").lstrip("* ").strip("`")
            if line and not line.startswith("#"):
                subgoals.append(line)
        return subgoals

    # ------------------------------------------------------------------
    # CEGAR convenience
    # ------------------------------------------------------------------

    def make_cegar_loop(self, max_attempts: Optional[int] = None) -> CEGARLoop:
        """Create a :class:`CEGARLoop` wired to this prover."""
        return CEGARLoop(
            max_attempts=max_attempts or self._max_attempts,
            prover=self,
        )

    # ------------------------------------------------------------------
    # Helpers
    # ------------------------------------------------------------------

    @staticmethod
    def _estimate_tokens(text: str) -> int:
        """Rough token count (4 chars per token heuristic)."""
        return max(1, len(text) // 4)

# ═══════════════════════════════════════════════════════════════════════════
# Convenience factories
# ═══════════════════════════════════════════════════════════════════════════

def make_llm_prover(
    *,
    llm_call: Optional[Callable[..., str]] = None,
    model: str = "gpt-4",
    max_attempts: int = 3,
    lean_check_fn: Optional[Callable[..., Dict[str, Any]]] = None,
) -> LLMProver:
    """Create an :class:`LLMProver` with common defaults."""
    return LLMProver(
        llm_call=llm_call,
        model=model,
        max_attempts=max_attempts,
        lean_check_fn=lean_check_fn,
    )

def prove_with_cegar(
    obligation: Dict[str, Any],
    *,
    llm_call: Callable[..., str],
    oracle_fn: Optional[Callable[[str, str], Dict[str, Any]]] = None,
    model: str = "gpt-4",
    max_attempts: int = 3,
) -> ProverResult:
    """One-shot convenience: prove *obligation* with a CEGAR loop."""
    prover = make_llm_prover(
        llm_call=llm_call,
        model=model,
        max_attempts=max_attempts,
    )
    loop = prover.make_cegar_loop(max_attempts=max_attempts)
    return loop.run(obligation, oracle_fn=oracle_fn)
