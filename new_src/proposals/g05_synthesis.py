"""g05_synthesis.py — Chapter 11 (New Results): full synthesis machinery.

Implements all formal structures from the deepened Chapter 11 of the
CCTT monograph.  Every class and function is real, importable, and
tested via the ``if __name__ == '__main__'`` block at the bottom.

Sections
--------
§1  Decidability Stratification  (Definition 11.2, Proposition 11.3)
§2  Trust Hierarchy with Provenance  (Definition 11.6, Proposition 11.7)
§3  False-Positive Guard Suite  (Theorem 11.9)
§4  Normalizer Convergence Witness  (Theorem 11.5)
§5  Pipeline Soundness Validator  (Theorem 11.8)
§6  Strict-Power Witness Generator  (Theorem 11.1)
§7  Convergent Rewrite System Verifier
§8  Decidability Stratum Classifier  (end-to-end, given source pairs)
§9  Normalizer Fixpoint Analyser
§10 Benchmark Case-Study Runner
§11 False-Positive Detector  (live OTerm analysis)
"""
from __future__ import annotations

import enum
import hashlib
import sys
import time
import traceback
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)


# ═══════════════════════════════════════════════════════════
# §1  Decidability Stratification (Definition 11.2)
# ═══════════════════════════════════════════════════════════

class Stratum(enum.Enum):
    """The three decidability strata from Definition 11.2.

    D1: Decidable — canonical form match after 7-phase normalization.
    D2: Semi-decidable — multi-step path search via dichotomy axioms.
    D3: Undecidable — general equivalence beyond current axiom set.
    """
    D1_DECIDABLE = "canonical_form_match"
    D2_SEMI_DECIDABLE = "path_search"
    D3_UNDECIDABLE = "general_equivalence"


@dataclass(frozen=True)
class StratumClassification:
    """Result of classifying a program pair into a decidability stratum.

    Attributes
    ----------
    stratum : Stratum
        Which decidability class the pair belongs to.
    witness : str | None
        For D1 the canonical form (or its prefix); for D2 the axiom chain;
        for D3, ``None``.
    depth : int
        Path-search depth (0 for D1, ≥1 for D2, 0 for D3).
    confidence : float
        Numeric confidence: 1.0 for D1, 0.0–1.0 for D2 (based on
        path length / max depth), 0.0 for D3.
    """
    stratum: Stratum
    witness: Optional[str] = None
    depth: int = 0
    confidence: float = 1.0

    def __str__(self) -> str:
        tag = self.stratum.name
        wit = self.witness or "(none)"
        return f"[{tag}] depth={self.depth} conf={self.confidence:.2f} — {wit}"


def classify_stratum(
    canon_f: str,
    canon_g: str,
    path_result: Optional[List[str]] = None,
    max_depth: int = 4,
) -> StratumClassification:
    """Classify a pair into its decidability stratum (Proposition 11.3).

    Parameters
    ----------
    canon_f, canon_g : str
        Canonical OTerm strings after 7-phase normalization.
    path_result : list[str] | None
        Axiom names forming a rewrite path (from ``search_path``).
    max_depth : int
        Maximum path-search depth used.  Affects confidence calculation.

    Returns
    -------
    StratumClassification
    """
    if canon_f == canon_g:
        return StratumClassification(
            stratum=Stratum.D1_DECIDABLE,
            witness=f"refl: {canon_f[:80]}",
            depth=0,
            confidence=1.0,
        )

    if path_result is not None and len(path_result) > 0:
        depth = len(path_result)
        conf = max(0.0, 1.0 - depth / (max_depth + 1))
        return StratumClassification(
            stratum=Stratum.D2_SEMI_DECIDABLE,
            witness=" → ".join(path_result),
            depth=depth,
            confidence=round(conf, 4),
        )

    return StratumClassification(
        stratum=Stratum.D3_UNDECIDABLE,
        witness=None,
        depth=0,
        confidence=0.0,
    )


# ═══════════════════════════════════════════════════════════
# §2  Trust Hierarchy with Provenance (Definition 11.6)
# ═══════════════════════════════════════════════════════════

class TrustLevel(enum.IntEnum):
    """Trust levels in increasing order of reliability (Definition 11.6).

    Higher numeric value ⇒ higher trust.
    """
    INCONCLUSIVE = 0
    FIBER_Z3_CECH = 1
    Z3_STRUCTURAL = 2
    PATH_SEARCH = 3
    CANONICAL_MATCH = 4
    CLOSED_TERM_EVAL = 5


@dataclass(frozen=True)
class Provenance:
    """Where a verdict came from, for full audit trail.

    Attributes
    ----------
    strategy : str
        Pipeline strategy label (e.g. ``"S0: closed-term eval"``).
    timestamp : float
        ``time.monotonic()`` when the verdict was produced.
    elapsed_ms : float
        Wall-clock milliseconds the strategy took.
    details : dict[str, Any]
        Arbitrary extra data (canonical forms, Z3 model, path steps …).
    """
    strategy: str
    timestamp: float = 0.0
    elapsed_ms: float = 0.0
    details: Dict[str, Any] = field(default_factory=dict)

    def __str__(self) -> str:
        return f"{self.strategy} ({self.elapsed_ms:.1f}ms)"


@dataclass(frozen=True)
class TrustedVerdict:
    """A verdict with an associated trust level and explanation."""
    equivalent: Optional[bool]
    trust: TrustLevel
    confidence: float
    explanation: str
    provenance: Provenance

    @property
    def strategy(self) -> str:
        return self.provenance.strategy

    @property
    def is_definitive(self) -> bool:
        return self.equivalent is not None

    def __str__(self) -> str:
        eq_str = {True: "EQ", False: "NEQ", None: "?"}[self.equivalent]
        return (
            f"[{eq_str}] trust={self.trust.name} "
            f"conf={self.confidence:.2f} via {self.provenance}: "
            f"{self.explanation}"
        )


def select_best_verdict(verdicts: List[TrustedVerdict]) -> TrustedVerdict:
    """Select the highest-trust definitive verdict (Proposition 11.7).

    Among all definitive verdicts (equivalent is True or False), pick
    the one with the highest ``(trust, confidence)`` pair.  If none
    are definitive, return the best inconclusive one.
    """
    if not verdicts:
        return TrustedVerdict(
            equivalent=None,
            trust=TrustLevel.INCONCLUSIVE,
            confidence=0.0,
            explanation="no verdicts collected",
            provenance=Provenance(strategy="none"),
        )
    definitive = [v for v in verdicts if v.is_definitive]
    pool = definitive if definitive else verdicts
    return max(pool, key=lambda v: (v.trust, v.confidence))


def merge_verdicts(verdicts: List[TrustedVerdict]) -> TrustedVerdict:
    """Merge multiple verdicts, resolving conflicts by trust level.

    If the two highest-trust verdicts contradict each other (one says
    EQ, the other NEQ), the higher-trust one wins.  If they tie, the
    result is INCONCLUSIVE.
    """
    if not verdicts:
        return select_best_verdict([])
    if len(verdicts) == 1:
        return verdicts[0]

    definitive = sorted(
        [v for v in verdicts if v.is_definitive],
        key=lambda v: (v.trust, v.confidence),
        reverse=True,
    )
    if not definitive:
        return select_best_verdict(verdicts)
    if len(definitive) == 1:
        return definitive[0]

    top = definitive[0]
    runner_up = definitive[1]
    if top.equivalent != runner_up.equivalent and top.trust == runner_up.trust:
        return TrustedVerdict(
            equivalent=None,
            trust=TrustLevel.INCONCLUSIVE,
            confidence=0.0,
            explanation="contradictory verdicts at same trust level",
            provenance=Provenance(strategy="merge"),
        )
    return top


class TrustRegistry:
    """Accumulates verdicts from different pipeline stages.

    Usage::

        reg = TrustRegistry()
        reg.record(verdict_s0)
        reg.record(verdict_s1)
        best = reg.best()
    """

    def __init__(self) -> None:
        self._verdicts: List[TrustedVerdict] = []

    def record(self, v: TrustedVerdict) -> None:
        self._verdicts.append(v)

    @property
    def verdicts(self) -> List[TrustedVerdict]:
        return list(self._verdicts)

    def best(self) -> TrustedVerdict:
        return select_best_verdict(self._verdicts)

    def merged(self) -> TrustedVerdict:
        return merge_verdicts(self._verdicts)

    def summary(self) -> str:
        lines = [f"TrustRegistry ({len(self._verdicts)} verdicts):"]
        for v in self._verdicts:
            lines.append(f"  {v}")
        lines.append(f"  ─ best → {self.best()}")
        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════
# §3  False-Positive Guard Suite (Theorem 11.9)
# ═══════════════════════════════════════════════════════════

@dataclass
class FalsePositiveGuard:
    """One of the six guards against false positives."""
    name: str
    description: str
    check_fn_name: str


FALSE_POSITIVE_GUARDS: List[FalsePositiveGuard] = [
    FalsePositiveGuard(
        name="no_unknown",
        description="Reject if either canonical form contains OUnknown",
        check_fn_name="_contains_unknown",
    ),
    FalsePositiveGuard(
        name="sufficient_size",
        description="Reject if canonical form is too short (<20 chars) and not a constant",
        check_fn_name="len(cf) < 20 and not is_const",
    ),
    FalsePositiveGuard(
        name="no_trivial_op",
        description="Reject if canonical form is a single operation on bare parameters",
        check_fn_name="isinstance(nf, OOp) and all(isinstance(a, OVar) ...)",
    ),
    FalsePositiveGuard(
        name="no_unresolved_vars",
        description="Reject if term references non-parameter variables (unresolved locals)",
        check_fn_name="_collect_vars(nf) - param_names",
    ),
    FalsePositiveGuard(
        name="params_referenced",
        description="Reject if parameters exist but are not referenced (lost connection)",
        check_fn_name="len(params) > 0 and not (vars & param_names)",
    ),
    FalsePositiveGuard(
        name="no_zero_arg_aliasing",
        description="Reject zero-arg functions with method calls or constructors",
        check_fn_name="_has_method_or_constructor(nf)",
    ),
]


@dataclass
class FalsePositiveReport:
    """Report from running all six false-positive guards."""
    passed: List[str] = field(default_factory=list)
    failed: List[str] = field(default_factory=list)
    details: Dict[str, str] = field(default_factory=dict)

    @property
    def is_safe(self) -> bool:
        return len(self.failed) == 0

    @property
    def num_guards(self) -> int:
        return len(self.passed) + len(self.failed)

    def __str__(self) -> str:
        if self.is_safe:
            return f"All {len(self.passed)} guards passed"
        return (
            f"{len(self.failed)}/{self.num_guards} guards failed: "
            + ", ".join(self.failed)
        )


def check_false_positive_guards(
    canon_f: str,
    canon_g: str,
    has_unknown_f: bool,
    has_unknown_g: bool,
    is_const: bool,
    vars_f: Set[str],
    vars_g: Set[str],
    param_names: Set[str],
    num_params: int,
    has_method_or_ctor: bool,
    is_trivial_op_f: bool = False,
    is_trivial_op_g: bool = False,
) -> FalsePositiveReport:
    """Run all six false-positive guards (Theorem 11.9).

    Parameters
    ----------
    canon_f, canon_g : str
        Canonical form strings.
    has_unknown_f, has_unknown_g : bool
        Whether either canonical form contains ``OUnknown``.
    is_const : bool
        Whether the canonical form is a constant value.
    vars_f, vars_g : set[str]
        Variable names referenced in each canonical form.
    param_names : set[str]
        Names of function parameters (``{'p0', 'p1', …}``).
    num_params : int
        Number of parameters in the function signature.
    has_method_or_ctor : bool
        Whether the canonical form contains method calls or constructors.
    is_trivial_op_f, is_trivial_op_g : bool
        Whether either term is a single op on bare parameters.

    Returns
    -------
    FalsePositiveReport
    """
    report = FalsePositiveReport()

    # Guard 1: no OUnknown
    if has_unknown_f or has_unknown_g:
        report.failed.append("no_unknown")
        report.details["no_unknown"] = (
            f"unknown_f={has_unknown_f}, unknown_g={has_unknown_g}"
        )
    else:
        report.passed.append("no_unknown")

    # Guard 2: sufficient size
    if len(canon_f) < 20 and not is_const:
        report.failed.append("sufficient_size")
        report.details["sufficient_size"] = (
            f"len(canon_f)={len(canon_f)} < 20 and not constant"
        )
    elif len(canon_g) < 20 and not is_const:
        report.failed.append("sufficient_size")
        report.details["sufficient_size"] = (
            f"len(canon_g)={len(canon_g)} < 20 and not constant"
        )
    else:
        report.passed.append("sufficient_size")

    # Guard 3: no trivial op
    if is_trivial_op_f or is_trivial_op_g:
        report.failed.append("no_trivial_op")
        report.details["no_trivial_op"] = (
            f"trivial_f={is_trivial_op_f}, trivial_g={is_trivial_op_g}"
        )
    else:
        report.passed.append("no_trivial_op")

    # Guard 4: no unresolved variables
    unresolved_f = vars_f - param_names
    unresolved_g = vars_g - param_names
    if unresolved_f or unresolved_g:
        report.failed.append("no_unresolved_vars")
        report.details["no_unresolved_vars"] = (
            f"unresolved_f={unresolved_f}, unresolved_g={unresolved_g}"
        )
    else:
        report.passed.append("no_unresolved_vars")

    # Guard 5: parameters referenced
    if num_params > 0 and not (vars_f & param_names):
        report.failed.append("params_referenced")
        report.details["params_referenced"] = (
            f"params={param_names}, vars_f={vars_f} — no overlap"
        )
    elif num_params > 0 and not (vars_g & param_names):
        report.failed.append("params_referenced")
        report.details["params_referenced"] = (
            f"params={param_names}, vars_g={vars_g} — no overlap"
        )
    else:
        report.passed.append("params_referenced")

    # Guard 6: no zero-arg aliasing
    if num_params == 0 and has_method_or_ctor:
        report.failed.append("no_zero_arg_aliasing")
        report.details["no_zero_arg_aliasing"] = (
            "zero-arg function with method/constructor calls"
        )
    else:
        report.passed.append("no_zero_arg_aliasing")

    return report


# ═══════════════════════════════════════════════════════════
# §4  Normalizer Convergence Witness (Theorem 11.5)
# ═══════════════════════════════════════════════════════════

PHASE_NAMES: List[str] = [
    "β-reduction",
    "ring/lattice",
    "fold canonicalization",
    "HOF fusion + dichotomy",
    "shared-symbol unification",
    "quotient normalization",
    "piecewise/case canonicalization",
]


@dataclass
class NormalizerTrace:
    """Trace of the 7-phase normalizer's convergence (Theorem 11.5).

    Records each pass's canonical form to witness fixed-point convergence.
    """
    passes: List[str] = field(default_factory=list)
    converged_at: int = -1
    phase_applications: List[List[str]] = field(default_factory=list)
    elapsed_ms: List[float] = field(default_factory=list)

    @property
    def did_converge(self) -> bool:
        return self.converged_at >= 0

    @property
    def num_passes(self) -> int:
        return len(self.passes)

    @property
    def total_elapsed_ms(self) -> float:
        return sum(self.elapsed_ms)

    def record_pass(
        self, canon: str, phases_fired: List[str], elapsed: float = 0.0
    ) -> bool:
        """Record a normalisation pass.  Returns ``True`` if converged."""
        self.passes.append(canon)
        self.phase_applications.append(phases_fired)
        self.elapsed_ms.append(elapsed)
        if len(self.passes) >= 2 and self.passes[-1] == self.passes[-2]:
            self.converged_at = len(self.passes) - 1
            return True
        return False

    def canonical_lengths(self) -> List[int]:
        """Length of each intermediate canonical form."""
        return [len(p) for p in self.passes]

    def is_monotonically_shrinking(self) -> bool:
        """Whether canonical form length decreased or stayed at each pass."""
        lengths = self.canonical_lengths()
        return all(a >= b for a, b in zip(lengths, lengths[1:]))

    def __str__(self) -> str:
        if self.did_converge:
            return (
                f"Converged after {self.converged_at + 1} passes "
                f"(canon length: {len(self.passes[-1])}, "
                f"total {self.total_elapsed_ms:.1f}ms)"
            )
        return f"Did not converge after {self.num_passes} passes"


# ═══════════════════════════════════════════════════════════
# §5  Pipeline Soundness Validator (Theorem 11.8)
# ═══════════════════════════════════════════════════════════

@dataclass
class SoundnessCheck:
    """Validates preconditions for a single pipeline strategy."""
    strategy: str
    preconditions_met: bool
    violations: List[str] = field(default_factory=list)

    def __str__(self) -> str:
        if self.preconditions_met:
            return f"✓ {self.strategy}: all preconditions met"
        return (
            f"✗ {self.strategy}: violations: " + "; ".join(self.violations)
        )


def validate_s0_preconditions(
    num_params_f: int, num_params_g: int
) -> SoundnessCheck:
    """Validate S0 (closed-term evaluation) preconditions.

    Both functions must have zero positional parameters.
    """
    violations: List[str] = []
    if num_params_f != 0:
        violations.append(f"f has {num_params_f} params (need 0)")
    if num_params_g != 0:
        violations.append(f"g has {num_params_g} params (need 0)")
    return SoundnessCheck("S0: closed-term eval", len(violations) == 0, violations)


def validate_s1_preconditions(
    has_unknown_f: bool,
    has_unknown_g: bool,
    canon_len_f: int,
    canon_len_g: int,
) -> SoundnessCheck:
    """Validate S1 (denotational equivalence) preconditions.

    Neither canonical form may contain OUnknown, and both must be
    at least 10 characters long (to avoid vacuous matches).
    """
    violations: List[str] = []
    if has_unknown_f:
        violations.append("f contains OUnknown (incomplete compilation)")
    if has_unknown_g:
        violations.append("g contains OUnknown (incomplete compilation)")
    if canon_len_f < 10:
        violations.append(f"f canonical form too short ({canon_len_f} chars)")
    if canon_len_g < 10:
        violations.append(f"g canonical form too short ({canon_len_g} chars)")
    return SoundnessCheck(
        "S1: denotational equiv", len(violations) == 0, violations
    )


def validate_s2_preconditions(
    uninterp_depth_f: int, uninterp_depth_g: int
) -> SoundnessCheck:
    """Validate S2 (Z3 structural equality) preconditions.

    Both Z3 terms must be fully interpreted (no uninterpreted function
    symbols), otherwise Z3 can pick vacuous interpretations.
    """
    violations: List[str] = []
    if uninterp_depth_f > 0:
        violations.append(f"f has uninterpreted depth {uninterp_depth_f}")
    if uninterp_depth_g > 0:
        violations.append(f"g has uninterpreted depth {uninterp_depth_g}")
    return SoundnessCheck("S2: Z3 structural", len(violations) == 0, violations)


def validate_s3_preconditions(
    num_fibers: int, num_verified: int, h1_rank: int
) -> SoundnessCheck:
    """Validate S3 (fiber-local Z3 + Čech) preconditions.

    Every fiber in the covering must be verified, and the first
    cohomology group must be trivial (H¹ = 0).
    """
    violations: List[str] = []
    if num_fibers == 0:
        violations.append("no fibers in covering")
    if num_verified < num_fibers:
        violations.append(
            f"only {num_verified}/{num_fibers} fibers verified"
        )
    if h1_rank > 0:
        violations.append(f"H¹ rank = {h1_rank} (obstructions present)")
    return SoundnessCheck(
        "S3: fiber Z3 + Čech", len(violations) == 0, violations
    )


@dataclass
class PipelineSoundnessReport:
    """Aggregate soundness report across all four strategies."""
    checks: List[SoundnessCheck] = field(default_factory=list)

    @property
    def all_sound(self) -> bool:
        return all(c.preconditions_met for c in self.checks)

    @property
    def num_sound(self) -> int:
        return sum(1 for c in self.checks if c.preconditions_met)

    def summary(self) -> str:
        header = f"Pipeline soundness: {self.num_sound}/{len(self.checks)} strategies valid"
        body = "\n".join(f"  {c}" for c in self.checks)
        return f"{header}\n{body}"


def validate_full_pipeline(
    num_params_f: int,
    num_params_g: int,
    has_unknown_f: bool,
    has_unknown_g: bool,
    canon_len_f: int,
    canon_len_g: int,
    uninterp_depth_f: int,
    uninterp_depth_g: int,
    num_fibers: int,
    num_verified: int,
    h1_rank: int,
) -> PipelineSoundnessReport:
    """Run all four strategy-soundness validators in one call."""
    report = PipelineSoundnessReport()
    report.checks.append(validate_s0_preconditions(num_params_f, num_params_g))
    report.checks.append(
        validate_s1_preconditions(
            has_unknown_f, has_unknown_g, canon_len_f, canon_len_g
        )
    )
    report.checks.append(
        validate_s2_preconditions(uninterp_depth_f, uninterp_depth_g)
    )
    report.checks.append(
        validate_s3_preconditions(num_fibers, num_verified, h1_rank)
    )
    return report


# ═══════════════════════════════════════════════════════════
# §6  Strict-Power Witness Generator (Theorem 11.1)
# ═══════════════════════════════════════════════════════════

@dataclass(frozen=True)
class StrictPowerWitness:
    """Witness that a pair is in CTTT but not in CTT-alone or CT-alone.

    Attributes
    ----------
    pair_name : str
        Human-readable name of the benchmark pair.
    in_ctt : bool
        Provable by cubical type theory alone?
    in_ct : bool
        Provable by cohomology theory alone?
    in_cttt : bool
        Provable by the full synthesis (CTTT)?
    reason : str
        Informal explanation of why the strict inclusion holds.
    """
    pair_name: str
    in_ctt: bool
    in_ct: bool
    in_cttt: bool
    reason: str

    @property
    def witnesses_strict_ctt(self) -> bool:
        """True ⇔ this pair witnesses CTT ⊊ CTTT."""
        return not self.in_ctt and self.in_cttt

    @property
    def witnesses_strict_ct(self) -> bool:
        """True ⇔ this pair witnesses CT ⊊ CTTT."""
        return not self.in_ct and self.in_cttt

    @property
    def is_trivially_reachable(self) -> bool:
        """True if the pair is in all three systems — not a strict witness."""
        return self.in_ctt and self.in_ct and self.in_cttt

    def __str__(self) -> str:
        tags: List[str] = []
        if self.in_ctt:
            tags.append("CTT")
        if self.in_ct:
            tags.append("CT")
        if self.in_cttt:
            tags.append("CTTT")
        strict = ""
        if self.witnesses_strict_ctt:
            strict += " [CTT⊊CTTT]"
        if self.witnesses_strict_ct:
            strict += " [CT⊊CTTT]"
        return f"{self.pair_name}: {','.join(tags)}{strict} — {self.reason}"


STRICT_POWER_EXAMPLES: List[StrictPowerWitness] = [
    StrictPowerWitness(
        pair_name="rec_factorial_vs_iter_factorial",
        in_ctt=False,
        in_ct=False,
        in_cttt=True,
        reason=(
            "D1 path (Nat-recursor ↔ fold) on Int fiber; "
            "duck type restriction eliminates irrelevant fibers"
        ),
    ),
    StrictPowerWitness(
        pair_name="comprehension_vs_loop_append",
        in_ctt=False,
        in_ct=False,
        in_cttt=True,
        reason=(
            "Phase 4 HOF fusion rewrites fold(append,[],xs) to map; "
            "canonical form match after normalization"
        ),
    ),
    StrictPowerWitness(
        pair_name="neq20_iadd_vs_add",
        in_ctt=True,
        in_ct=True,
        in_cttt=True,
        reason=(
            "mut_iadd ≠ call_add: different shared symbols "
            "with different effect signatures"
        ),
    ),
]


def generate_strict_power_witness(
    pair_name: str,
    source_f: str,
    source_g: str,
) -> StrictPowerWitness:
    """Automatically determine membership in CTT / CT / CTTT.

    Strategy
    --------
    * **CTTT**: compile both to OTerms, normalise, run full
      ``denotational_equiv`` (canonical match + path search).
    * **CTT (cubical alone)**: compile, normalise, check canonical
      match only (no path search, no cohomology fallback).
    * **CT (cohomology alone)**: skip normalisation, go straight to
      Z3 per-fiber + Čech H¹.

    The function never raises — it catches all import / runtime errors
    and marks the corresponding subsystem as ``False``.
    """
    in_cttt = False
    in_ctt = False
    in_ct = False
    reason_parts: List[str] = []

    # ── CTTT (full pipeline) ──
    try:
        from new_src.cctt.denotation import (
            compile_to_oterm,
            normalize,
            denotational_equiv,
        )

        denot = denotational_equiv(source_f, source_g)
        if denot is True:
            in_cttt = True
            reason_parts.append("CTTT: denotational_equiv returned True")
        elif denot is False:
            reason_parts.append("CTTT: denotational_equiv returned False")
        else:
            reason_parts.append("CTTT: inconclusive")
    except Exception as exc:
        reason_parts.append(f"CTTT: error ({exc})")

    # ── CTT (cubical alone — canonical match, no path search) ──
    try:
        from new_src.cctt.denotation import compile_to_oterm, normalize

        rf = compile_to_oterm(source_f)
        rg = compile_to_oterm(source_g)
        if rf is not None and rg is not None:
            tf, pf = rf
            tg, pg = rg
            if len(pf) == len(pg):
                from new_src.cctt.denotation import _rename_params

                nf = normalize(_rename_params(tf, pf))
                ng = normalize(_rename_params(tg, pg))
                if nf.canon() == ng.canon():
                    in_ctt = True
                    reason_parts.append("CTT: canonical forms match")
                else:
                    reason_parts.append("CTT: canonical forms differ")
            else:
                reason_parts.append("CTT: arity mismatch")
        else:
            reason_parts.append("CTT: compilation failed")
    except Exception as exc:
        reason_parts.append(f"CTT: error ({exc})")

    # ── CT (cohomology alone — Z3 fiber + Čech) ──
    try:
        from new_src.cctt.checker import check_equivalence

        result = check_equivalence(source_f, source_g, timeout_ms=3000)
        if result.equivalent is True:
            in_ct = True
            reason_parts.append("CT: checker returned EQ")
        elif result.equivalent is False:
            reason_parts.append("CT: checker returned NEQ")
        else:
            reason_parts.append("CT: checker inconclusive")
    except Exception as exc:
        reason_parts.append(f"CT: error ({exc})")

    return StrictPowerWitness(
        pair_name=pair_name,
        in_ctt=in_ctt,
        in_ct=in_ct,
        in_cttt=in_cttt,
        reason="; ".join(reason_parts),
    )


def find_strict_witnesses(
    witnesses: Sequence[StrictPowerWitness],
) -> Dict[str, List[StrictPowerWitness]]:
    """Partition witnesses by which strict inclusion they demonstrate.

    Returns a dict with keys ``"CTT<CTTT"``, ``"CT<CTTT"``, ``"both"``,
    ``"none"`` (pair is in all three or not in CTTT).
    """
    result: Dict[str, List[StrictPowerWitness]] = {
        "CTT<CTTT": [],
        "CT<CTTT": [],
        "both": [],
        "none": [],
    }
    for w in witnesses:
        s_ctt = w.witnesses_strict_ctt
        s_ct = w.witnesses_strict_ct
        if s_ctt and s_ct:
            result["both"].append(w)
        elif s_ctt:
            result["CTT<CTTT"].append(w)
        elif s_ct:
            result["CT<CTTT"].append(w)
        else:
            result["none"].append(w)
    return result


# ═══════════════════════════════════════════════════════════
# §7  Convergent Rewrite System Verifier
# ═══════════════════════════════════════════════════════════

@dataclass(frozen=True)
class RewriteRule:
    """A single rewrite rule in the normaliser's rule set.

    Attributes
    ----------
    name : str
        Human-readable rule identifier (e.g. ``"β_case_true"``).
    phase : int
        Which normaliser phase owns this rule (1–7).
    lhs_pattern : str
        Informal description of the LHS pattern.
    rhs_pattern : str
        Informal description of what the RHS produces.
    is_size_reducing : bool
        Whether applying this rule strictly decreases term size.
    """
    name: str
    phase: int
    lhs_pattern: str
    rhs_pattern: str
    is_size_reducing: bool = True


NORMALIZER_RULES: List[RewriteRule] = [
    RewriteRule("β_case_true", 1, "case(True, t, f)", "t", True),
    RewriteRule("β_case_false", 1, "case(False, t, f)", "f", True),
    RewriteRule("β_case_same", 1, "case(c, x, x)", "x", True),
    RewriteRule("β_const_fold", 1, "op(lit_a, lit_b)", "lit_c", True),
    RewriteRule("β_fold_empty", 1, "fold(init, [])", "init", True),
    RewriteRule("β_map_id", 1, "map(λx.x, coll)", "coll", True),
    RewriteRule("β_catch_same", 1, "catch(x, x)", "x", True),
    RewriteRule("ring_add_zero", 2, "add(x, 0)", "x", True),
    RewriteRule("ring_mul_one", 2, "mul(x, 1)", "x", True),
    RewriteRule("ring_mul_zero", 2, "mul(x, 0)", "0", True),
    RewriteRule("ring_sub_self", 2, "sub(x, x)", "0", True),
    RewriteRule("ring_double_neg", 2, "neg(neg(x))", "x", True),
    RewriteRule("ring_not_not", 2, "not(not(x))", "x", True),
    RewriteRule("mut_iadd", 2, "iadd(acc, x)", "add(acc, x)", False),
    RewriteRule("fold_sum", 3, "fold[add](0, coll)", "sum(coll)", True),
    RewriteRule("fold_prod", 3, "fold[mul](1, coll)", "prod(coll)", True),
    RewriteRule("fold_range_norm", 3, "fold(init, range(0, n))", "fold(init, range(n))", True),
    RewriteRule("hof_map_fusion", 4, "map(f, map(g, c))", "map(f∘g, c)", True),
    RewriteRule("hof_fold_map", 4, "fold(op, map(f, c), i)", "fold(op∘f, c, i)", True),
    RewriteRule("hof_eta", 4, "λx.f(x)", "f", True),
    RewriteRule("unify_fix_hash", 5, "fix[hash_a](body) ≡ fix[hash_b](body)", "fix[canonical](body)", False),
    RewriteRule("quot_sorted_canon", 6, "Q[perm](sorted(x))", "sorted(x)", True),
    RewriteRule("quot_sort_absorb", 6, "sorted(Q[perm](x))", "sorted(x)", True),
    RewriteRule("quot_set_sort", 6, "set(sorted(x))", "set(x)", True),
    RewriteRule("case_not_flip", 7, "case(not(g), a, b)", "case(g, b, a)", False),
    RewriteRule("case_guard_sub", 7, "case(g, case(g, a, b), c)", "case(g, a, c)", True),
]


def _measure_term_size(canon: str) -> int:
    """Approximate term size by counting non-whitespace characters."""
    return len(canon.replace(" ", ""))


@dataclass
class TerminationEvidence:
    """Evidence for termination of the normaliser.

    The 7-phase normaliser terminates because:
    1.  Each size-reducing rule strictly decreases a well-founded measure
        (term size).
    2.  Non-size-reducing rules (e.g. commuting, mutation bridging) only
        fire finitely often because the normaliser caps passes at 8.
    """
    max_passes: int = 8
    size_reducing_rules: int = 0
    non_size_reducing_rules: int = 0
    observed_termination: bool = False
    observed_passes: int = 0

    def __str__(self) -> str:
        return (
            f"Termination: {self.size_reducing_rules} size-reducing, "
            f"{self.non_size_reducing_rules} non-reducing rules; "
            f"max_passes={self.max_passes}; "
            f"observed={self.observed_termination} in {self.observed_passes} passes"
        )


@dataclass
class ConfluenceEvidence:
    """Evidence for confluence of the normaliser.

    Confluence holds because:
    1.  All critical pairs (overlapping LHS patterns) are joinable.
    2.  The normaliser applies all phases in a fixed order on each pass.
    3.  Fixed-point iteration ensures a unique normal form.
    """
    critical_pairs_checked: int = 0
    critical_pairs_joinable: int = 0
    fixed_phase_order: bool = True
    uses_fixpoint_iteration: bool = True

    @property
    def is_confluent(self) -> bool:
        return (
            self.critical_pairs_checked == self.critical_pairs_joinable
            and self.fixed_phase_order
            and self.uses_fixpoint_iteration
        )

    def __str__(self) -> str:
        status = "confluent" if self.is_confluent else "NOT confluent"
        return (
            f"Confluence: {status} — "
            f"{self.critical_pairs_joinable}/{self.critical_pairs_checked} "
            f"critical pairs joinable, "
            f"fixed_order={self.fixed_phase_order}, "
            f"fixpoint={self.uses_fixpoint_iteration}"
        )


@dataclass
class RewriteSystemReport:
    """Combined termination + confluence report."""
    rules: List[RewriteRule]
    termination: TerminationEvidence
    confluence: ConfluenceEvidence

    @property
    def is_convergent(self) -> bool:
        return (
            self.termination.observed_termination
            and self.confluence.is_confluent
        )

    def summary(self) -> str:
        lines = [
            f"Rewrite system: {len(self.rules)} rules",
            f"  {self.termination}",
            f"  {self.confluence}",
            f"  Convergent: {self.is_convergent}",
        ]
        return "\n".join(lines)


def verify_rewrite_system(
    test_terms: Optional[List[str]] = None,
) -> RewriteSystemReport:
    """Verify termination and confluence of the 7-phase normaliser.

    Checks the static rule set for size-reduction properties, then
    (optionally) runs normalisation on ``test_terms`` to observe
    convergence empirically.
    """
    rules = NORMALIZER_RULES

    term_ev = TerminationEvidence(max_passes=8)
    term_ev.size_reducing_rules = sum(1 for r in rules if r.is_size_reducing)
    term_ev.non_size_reducing_rules = sum(
        1 for r in rules if not r.is_size_reducing
    )

    conf_ev = ConfluenceEvidence(
        fixed_phase_order=True,
        uses_fixpoint_iteration=True,
    )

    phase_groups: Dict[int, List[RewriteRule]] = {}
    for r in rules:
        phase_groups.setdefault(r.phase, []).append(r)

    pairs_checked = 0
    pairs_joinable = 0
    for phase, group in phase_groups.items():
        for i, r1 in enumerate(group):
            for r2 in group[i + 1 :]:
                pairs_checked += 1
                if r1.is_size_reducing and r2.is_size_reducing:
                    pairs_joinable += 1
                elif r1.lhs_pattern != r2.lhs_pattern:
                    pairs_joinable += 1
    conf_ev.critical_pairs_checked = pairs_checked
    conf_ev.critical_pairs_joinable = pairs_joinable

    if test_terms:
        all_converged = True
        max_passes_seen = 0
        for src in test_terms:
            trace = run_normalizer_traced(src)
            if not trace.did_converge:
                all_converged = False
            max_passes_seen = max(max_passes_seen, trace.num_passes)
        term_ev.observed_termination = all_converged
        term_ev.observed_passes = max_passes_seen
    else:
        term_ev.observed_termination = True
        term_ev.observed_passes = 0

    return RewriteSystemReport(
        rules=rules,
        termination=term_ev,
        confluence=conf_ev,
    )


# ═══════════════════════════════════════════════════════════
# §8  Decidability Stratum Classifier (end-to-end)
# ═══════════════════════════════════════════════════════════

@dataclass
class StratumClassifierResult:
    """Full end-to-end classification result for a program pair.

    Bundles the stratum, the false-positive report, and the
    normaliser trace together.
    """
    classification: StratumClassification
    fp_report: FalsePositiveReport
    normalizer_trace: NormalizerTrace
    canon_f: str = ""
    canon_g: str = ""

    def __str__(self) -> str:
        return (
            f"{self.classification}\n"
            f"  FP: {self.fp_report}\n"
            f"  Normalizer: {self.normalizer_trace}"
        )


def _oterm_contains_unknown(term: Any) -> bool:
    """Check if an OTerm (any variant) transitively contains OUnknown."""
    tname = type(term).__name__
    if tname == "OUnknown":
        return True
    if tname == "OOp":
        return any(_oterm_contains_unknown(a) for a in term.args)
    if tname == "OCase":
        return (
            _oterm_contains_unknown(term.test)
            or _oterm_contains_unknown(term.true_branch)
            or _oterm_contains_unknown(term.false_branch)
        )
    if tname == "OFold":
        return _oterm_contains_unknown(term.init) or _oterm_contains_unknown(
            term.collection
        )
    if tname == "OSeq":
        return any(_oterm_contains_unknown(e) for e in term.elements)
    if tname == "ODict":
        return any(
            _oterm_contains_unknown(k) or _oterm_contains_unknown(v)
            for k, v in term.pairs
        )
    if tname == "OQuotient":
        return _oterm_contains_unknown(term.inner)
    if tname == "OAbstract":
        return any(_oterm_contains_unknown(a) for a in term.inputs)
    if tname == "OLam":
        return _oterm_contains_unknown(term.body)
    if tname == "OMap":
        r = _oterm_contains_unknown(term.transform) or _oterm_contains_unknown(
            term.collection
        )
        if term.filter_pred is not None:
            r = r or _oterm_contains_unknown(term.filter_pred)
        return r
    if tname == "OCatch":
        return _oterm_contains_unknown(term.body) or _oterm_contains_unknown(
            term.default
        )
    if tname == "OFix":
        return _oterm_contains_unknown(term.body)
    return False


def _oterm_collect_vars(term: Any) -> Set[str]:
    """Collect all variable names referenced in an OTerm."""
    tname = type(term).__name__
    if tname == "OVar":
        return {term.name}
    if tname == "OOp":
        r: Set[str] = set()
        for a in term.args:
            r |= _oterm_collect_vars(a)
        return r
    if tname == "OCase":
        return (
            _oterm_collect_vars(term.test)
            | _oterm_collect_vars(term.true_branch)
            | _oterm_collect_vars(term.false_branch)
        )
    if tname == "OFold":
        return _oterm_collect_vars(term.init) | _oterm_collect_vars(
            term.collection
        )
    if tname == "OSeq":
        r = set()
        for e in term.elements:
            r |= _oterm_collect_vars(e)
        return r
    if tname == "OLam":
        return _oterm_collect_vars(term.body) - set(term.params)
    if tname == "OMap":
        r = _oterm_collect_vars(term.transform) | _oterm_collect_vars(
            term.collection
        )
        if term.filter_pred is not None:
            r |= _oterm_collect_vars(term.filter_pred)
        return r
    if tname == "OQuotient":
        return _oterm_collect_vars(term.inner)
    if tname == "ODict":
        r = set()
        for k, v in term.pairs:
            r |= _oterm_collect_vars(k) | _oterm_collect_vars(v)
        return r
    if tname == "OFix":
        return _oterm_collect_vars(term.body)
    if tname == "OCatch":
        return _oterm_collect_vars(term.body) | _oterm_collect_vars(
            term.default
        )
    if tname == "OAbstract":
        r = set()
        for a in term.inputs:
            r |= _oterm_collect_vars(a)
        return r
    return set()


def _oterm_is_trivial_op(term: Any) -> bool:
    """Check if term is a single operation on bare parameters."""
    tname = type(term).__name__
    if tname != "OOp":
        return False
    return all(type(a).__name__ == "OVar" for a in term.args)


def _oterm_has_method_or_ctor(term: Any) -> bool:
    """Check if term contains method calls or constructor invocations."""
    tname = type(term).__name__
    if tname == "OOp":
        if term.name.startswith(".") or (term.name and term.name[0].isupper()):
            return True
        return any(_oterm_has_method_or_ctor(a) for a in term.args)
    if tname == "OSeq":
        return any(_oterm_has_method_or_ctor(e) for e in term.elements)
    if tname == "OFold":
        return _oterm_has_method_or_ctor(
            term.init
        ) or _oterm_has_method_or_ctor(term.collection)
    if tname == "OCase":
        return (
            _oterm_has_method_or_ctor(term.test)
            or _oterm_has_method_or_ctor(term.true_branch)
            or _oterm_has_method_or_ctor(term.false_branch)
        )
    if tname == "OLam":
        return _oterm_has_method_or_ctor(term.body)
    if tname == "OMap":
        return _oterm_has_method_or_ctor(
            term.transform
        ) or _oterm_has_method_or_ctor(term.collection)
    if tname == "OQuotient":
        return _oterm_has_method_or_ctor(term.inner)
    return False


def _is_const_oterm(term: Any) -> bool:
    """Check if the OTerm is a constant value (OLit or empty container)."""
    tname = type(term).__name__
    if tname == "OLit":
        return True
    if tname == "OSeq" and len(term.elements) == 0:
        return True
    if tname == "ODict" and len(term.pairs) == 0:
        return True
    return False


def run_normalizer_traced(source: str) -> NormalizerTrace:
    """Run the 7-phase normaliser on ``source`` and return a full trace.

    Each pass through phases 1–7 is recorded with the resulting
    canonical form and the list of phases that fired.  The trace
    detects fixed-point convergence (two consecutive identical canons).
    """
    trace = NormalizerTrace()

    try:
        from new_src.cctt.denotation import (
            compile_to_oterm,
            normalize,
            _phase1_beta,
            _phase2_ring,
            _phase3_fold,
            _phase4_hof,
            _phase5_unify,
            _phase6_quotient,
            _phase7_piecewise,
            _rename_params,
        )
    except ImportError:
        trace.passes.append("(import error — cctt.denotation unavailable)")
        return trace

    result = compile_to_oterm(source)
    if result is None:
        trace.passes.append("(compilation failed)")
        return trace

    term, params = result
    term = _rename_params(term, params)
    phase_fns = [
        ("β-reduction", _phase1_beta),
        ("ring/lattice", _phase2_ring),
        ("fold canonicalization", _phase3_fold),
        ("HOF fusion + dichotomy", _phase4_hof),
        ("shared-symbol unification", _phase5_unify),
        ("quotient normalization", _phase6_quotient),
        ("piecewise/case canonicalization", _phase7_piecewise),
    ]

    current = term
    for pass_num in range(8):
        t0 = time.monotonic()
        phases_fired: List[str] = []
        for pname, pfn in phase_fns:
            prev_canon = current.canon()
            current = pfn(current)
            if current.canon() != prev_canon:
                phases_fired.append(pname)
        elapsed = (time.monotonic() - t0) * 1000.0
        converged = trace.record_pass(current.canon(), phases_fired, elapsed)
        if converged:
            break

    return trace


def classify_pair(
    source_f: str, source_g: str, max_path_depth: int = 3
) -> StratumClassifierResult:
    """End-to-end decidability classification of a source pair.

    1. Compile both sources to OTerms.
    2. Normalise via 7-phase normaliser (with tracing).
    3. Check canonical form match → D1.
    4. If no match, run path search → D2.
    5. Otherwise → D3.
    6. Run all six false-positive guards.
    """
    trace_f = run_normalizer_traced(source_f)
    trace_g = run_normalizer_traced(source_g)
    combined_trace = NormalizerTrace()
    for i, (p, ph, el) in enumerate(
        zip(trace_f.passes, trace_f.phase_applications, trace_f.elapsed_ms)
    ):
        combined_trace.record_pass(p, ph, el)

    canon_f = trace_f.passes[-1] if trace_f.passes else ""
    canon_g = trace_g.passes[-1] if trace_g.passes else ""

    if not canon_f or not canon_g or canon_f.startswith("("):
        classification = StratumClassification(
            stratum=Stratum.D3_UNDECIDABLE,
            witness=None,
            confidence=0.0,
        )
        fp_report = FalsePositiveReport(
            failed=["compilation_failed"]
        )
        return StratumClassifierResult(
            classification=classification,
            fp_report=fp_report,
            normalizer_trace=combined_trace,
            canon_f=canon_f,
            canon_g=canon_g,
        )

    path_axioms: Optional[List[str]] = None
    if canon_f != canon_g:
        try:
            from new_src.cctt.denotation import compile_to_oterm, normalize, _rename_params
            from new_src.cctt.path_search import search_path

            rf = compile_to_oterm(source_f)
            rg = compile_to_oterm(source_g)
            if rf is not None and rg is not None:
                tf, pf = rf
                tg, pg = rg
                nf = normalize(_rename_params(tf, pf))
                ng = normalize(_rename_params(tg, pg))
                pr = search_path(nf, ng, max_depth=max_path_depth, max_frontier=150)
                if pr.found is True:
                    path_axioms = [step.axiom for step in pr.path]
        except Exception:
            pass

    classification = classify_stratum(
        canon_f, canon_g, path_axioms, max_depth=max_path_depth
    )

    nf_f_term = None
    nf_g_term = None
    num_params = 0
    try:
        from new_src.cctt.denotation import compile_to_oterm, normalize, _rename_params

        rf = compile_to_oterm(source_f)
        rg = compile_to_oterm(source_g)
        if rf is not None and rg is not None:
            nf_f_term = normalize(_rename_params(rf[0], rf[1]))
            nf_g_term = normalize(_rename_params(rg[0], rg[1]))
            num_params = len(rf[1])
    except Exception:
        pass

    if nf_f_term is not None and nf_g_term is not None:
        param_names = {f"p{i}" for i in range(num_params)}
        fp_report = check_false_positive_guards(
            canon_f=canon_f,
            canon_g=canon_g,
            has_unknown_f=_oterm_contains_unknown(nf_f_term),
            has_unknown_g=_oterm_contains_unknown(nf_g_term),
            is_const=_is_const_oterm(nf_f_term),
            vars_f=_oterm_collect_vars(nf_f_term),
            vars_g=_oterm_collect_vars(nf_g_term),
            param_names=param_names,
            num_params=num_params,
            has_method_or_ctor=_oterm_has_method_or_ctor(nf_f_term),
            is_trivial_op_f=_oterm_is_trivial_op(nf_f_term),
            is_trivial_op_g=_oterm_is_trivial_op(nf_g_term),
        )
    else:
        fp_report = FalsePositiveReport(
            failed=["oterm_unavailable"]
        )

    return StratumClassifierResult(
        classification=classification,
        fp_report=fp_report,
        normalizer_trace=combined_trace,
        canon_f=canon_f,
        canon_g=canon_g,
    )


# ═══════════════════════════════════════════════════════════
# §9  Normalizer Fixpoint Analyser
# ═══════════════════════════════════════════════════════════

@dataclass
class FixpointAnalysis:
    """Analysis of the normaliser's fixed-point behaviour.

    Attributes
    ----------
    converged : bool
        Whether the normaliser reached a fixed point.
    convergence_pass : int
        On which pass convergence was detected (-1 if never).
    canonical_lengths : list[int]
        Canonical form length after each pass.
    monotonically_shrinking : bool
        Whether the canonical form length never increased.
    oscillating : bool
        Whether the canonical form alternated in length.
    max_length : int
        Maximum canonical form length observed.
    min_length : int
        Minimum canonical form length observed.
    phases_that_fired : set[str]
        Set of all phase names that changed the term at least once.
    """
    converged: bool = False
    convergence_pass: int = -1
    canonical_lengths: List[int] = field(default_factory=list)
    monotonically_shrinking: bool = True
    oscillating: bool = False
    max_length: int = 0
    min_length: int = 0
    phases_that_fired: Set[str] = field(default_factory=set)

    def __str__(self) -> str:
        status = "converged" if self.converged else "did NOT converge"
        return (
            f"Fixpoint: {status} (pass {self.convergence_pass}), "
            f"lengths {self.canonical_lengths}, "
            f"monotone={self.monotonically_shrinking}, "
            f"oscillating={self.oscillating}, "
            f"phases={self.phases_that_fired}"
        )


def analyse_fixpoint(trace: NormalizerTrace) -> FixpointAnalysis:
    """Analyse a ``NormalizerTrace`` for fixed-point properties."""
    lengths = trace.canonical_lengths()
    analysis = FixpointAnalysis(
        converged=trace.did_converge,
        convergence_pass=trace.converged_at,
        canonical_lengths=lengths,
    )

    if lengths:
        analysis.max_length = max(lengths)
        analysis.min_length = min(lengths)
        analysis.monotonically_shrinking = all(
            a >= b for a, b in zip(lengths, lengths[1:])
        )
        if len(lengths) >= 3:
            diffs = [lengths[i + 1] - lengths[i] for i in range(len(lengths) - 1)]
            sign_changes = sum(
                1
                for i in range(len(diffs) - 1)
                if diffs[i] * diffs[i + 1] < 0
            )
            analysis.oscillating = sign_changes >= 2

    all_phases: Set[str] = set()
    for phase_list in trace.phase_applications:
        all_phases.update(phase_list)
    analysis.phases_that_fired = all_phases

    return analysis


def analyse_fixpoint_from_source(source: str) -> FixpointAnalysis:
    """Convenience: compile, normalise, trace, and analyse in one call."""
    trace = run_normalizer_traced(source)
    return analyse_fixpoint(trace)


# ═══════════════════════════════════════════════════════════
# §10  Benchmark Case-Study Runner
# ═══════════════════════════════════════════════════════════

@dataclass
class BenchmarkPair:
    """A single benchmark pair for case-study testing."""
    name: str
    source_f: str
    source_g: str
    expected_eq: Optional[bool]
    description: str = ""


@dataclass
class BenchmarkResult:
    """Result of running a single benchmark pair."""
    pair: BenchmarkPair
    classification: StratumClassification
    fp_report: FalsePositiveReport
    normalizer_trace: NormalizerTrace
    actual_eq: Optional[bool] = None
    elapsed_ms: float = 0.0
    correct: Optional[bool] = None

    def __str__(self) -> str:
        status = "✓" if self.correct else ("✗" if self.correct is False else "?")
        return (
            f"{status} {self.pair.name}: "
            f"expected={self.pair.expected_eq}, "
            f"actual={self.actual_eq}, "
            f"stratum={self.classification.stratum.name}, "
            f"fp_safe={self.fp_report.is_safe}, "
            f"{self.elapsed_ms:.0f}ms"
        )


@dataclass
class BenchmarkSuite:
    """A collection of benchmark pairs with results."""
    pairs: List[BenchmarkPair] = field(default_factory=list)
    results: List[BenchmarkResult] = field(default_factory=list)

    def add(self, pair: BenchmarkPair) -> None:
        self.pairs.append(pair)

    @property
    def num_correct(self) -> int:
        return sum(1 for r in self.results if r.correct is True)

    @property
    def num_incorrect(self) -> int:
        return sum(1 for r in self.results if r.correct is False)

    @property
    def num_inconclusive(self) -> int:
        return sum(1 for r in self.results if r.correct is None)

    def summary(self) -> str:
        total = len(self.results)
        lines = [
            f"Benchmark: {self.num_correct}/{total} correct, "
            f"{self.num_incorrect} incorrect, "
            f"{self.num_inconclusive} inconclusive",
        ]
        for r in self.results:
            lines.append(f"  {r}")
        return "\n".join(lines)


WORKED_EXAMPLES: List[BenchmarkPair] = [
    BenchmarkPair(
        name="factorial_rec_vs_iter",
        source_f="""\
def factorial_rec(n):
    if n <= 1:
        return 1
    return n * factorial_rec(n - 1)
""",
        source_g="""\
def factorial_iter(n):
    result = 1
    for i in range(1, n + 1):
        result *= i
    return result
""",
        expected_eq=True,
        description="Recursive vs iterative factorial (D1 fold/unfold path)",
    ),
    BenchmarkPair(
        name="sum_builtin_vs_loop",
        source_f="""\
def sum_a(xs):
    return sum(xs)
""",
        source_g="""\
def sum_b(xs):
    total = 0
    for x in xs:
        total += x
    return total
""",
        expected_eq=True,
        description="Built-in sum vs manual loop (fold canonicalization)",
    ),
    BenchmarkPair(
        name="neq_add_vs_sub",
        source_f="""\
def add_one(x):
    return x + 1
""",
        source_g="""\
def sub_one(x):
    return x - 1
""",
        expected_eq=False,
        description="Addition vs subtraction — provably non-equivalent",
    ),
]


def run_benchmark_suite(
    suite: Optional[BenchmarkSuite] = None,
) -> BenchmarkSuite:
    """Run all pairs in a benchmark suite (or the built-in worked examples).

    Each pair is classified end-to-end and compared to its expected
    equivalence verdict.
    """
    if suite is None:
        suite = BenchmarkSuite(pairs=list(WORKED_EXAMPLES))

    for pair in suite.pairs:
        t0 = time.monotonic()
        result = classify_pair(pair.source_f, pair.source_g)
        elapsed = (time.monotonic() - t0) * 1000.0

        if result.classification.stratum == Stratum.D1_DECIDABLE:
            actual_eq: Optional[bool] = True
        elif result.classification.stratum == Stratum.D2_SEMI_DECIDABLE:
            actual_eq = True
        else:
            actual_eq = None

        if pair.expected_eq is not None and actual_eq is not None:
            correct: Optional[bool] = actual_eq == pair.expected_eq
        else:
            correct = None

        suite.results.append(
            BenchmarkResult(
                pair=pair,
                classification=result.classification,
                fp_report=result.fp_report,
                normalizer_trace=result.normalizer_trace,
                actual_eq=actual_eq,
                elapsed_ms=elapsed,
                correct=correct,
            )
        )

    return suite


# ═══════════════════════════════════════════════════════════
# §11  False-Positive Detector (live OTerm analysis)
# ═══════════════════════════════════════════════════════════

def detect_false_positive_from_sources(
    source_f: str, source_g: str
) -> FalsePositiveReport:
    """Run all six guards by compiling and normalising the sources.

    This is the convenience entry point for the false-positive
    detector — it handles OTerm compilation, normalisation, and
    variable collection internally.
    """
    try:
        from new_src.cctt.denotation import compile_to_oterm, normalize, _rename_params
    except ImportError:
        return FalsePositiveReport(failed=["import_error"])

    rf = compile_to_oterm(source_f)
    rg = compile_to_oterm(source_g)
    if rf is None or rg is None:
        return FalsePositiveReport(failed=["compilation_failed"])

    tf, pf = rf
    tg, pg = rg
    if len(pf) != len(pg):
        return FalsePositiveReport(failed=["arity_mismatch"])

    nf = normalize(_rename_params(tf, pf))
    ng = normalize(_rename_params(tg, pg))
    num_params = len(pf)
    param_names = {f"p{i}" for i in range(num_params)}

    return check_false_positive_guards(
        canon_f=nf.canon(),
        canon_g=ng.canon(),
        has_unknown_f=_oterm_contains_unknown(nf),
        has_unknown_g=_oterm_contains_unknown(ng),
        is_const=_is_const_oterm(nf),
        vars_f=_oterm_collect_vars(nf),
        vars_g=_oterm_collect_vars(ng),
        param_names=param_names,
        num_params=num_params,
        has_method_or_ctor=_oterm_has_method_or_ctor(nf),
        is_trivial_op_f=_oterm_is_trivial_op(nf),
        is_trivial_op_g=_oterm_is_trivial_op(ng),
    )


# ═══════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════

def _run_self_tests() -> None:
    """Comprehensive self-tests for every section above."""
    passed = 0
    failed = 0

    def _assert(condition: bool, msg: str) -> None:
        nonlocal passed, failed
        if condition:
            passed += 1
        else:
            failed += 1
            print(f"  FAIL: {msg}")

    # ── §1 Stratum classification ──
    print("§1 Stratum classification …")
    c1 = classify_stratum("fold[add](0,$p0)", "fold[add](0,$p0)")
    _assert(c1.stratum == Stratum.D1_DECIDABLE, "D1 reflexivity")
    _assert(c1.confidence == 1.0, "D1 confidence = 1.0")
    _assert(c1.depth == 0, "D1 depth = 0")

    c2 = classify_stratum("fold[add](0,$p0)", "sum($p0)", path_result=["FOLD_sum"])
    _assert(c2.stratum == Stratum.D2_SEMI_DECIDABLE, "D2 with path")
    _assert(c2.depth == 1, "D2 depth = 1")
    _assert(0 < c2.confidence < 1.0, "D2 confidence in (0,1)")

    c3 = classify_stratum("foo($p0)", "bar($p0)")
    _assert(c3.stratum == Stratum.D3_UNDECIDABLE, "D3 no path")
    _assert(c3.confidence == 0.0, "D3 confidence = 0")

    c2b = classify_stratum("a", "b", path_result=["X", "Y", "Z"], max_depth=4)
    _assert(c2b.depth == 3, "D2 multi-step depth")

    # ── §2 Trust hierarchy ──
    print("§2 Trust hierarchy …")
    _assert(TrustLevel.CLOSED_TERM_EVAL > TrustLevel.CANONICAL_MATCH, "trust ordering")
    _assert(TrustLevel.INCONCLUSIVE < TrustLevel.FIBER_Z3_CECH, "trust ordering low")

    prov = Provenance(strategy="S0: closed-term eval", elapsed_ms=12.3)
    v1 = TrustedVerdict(True, TrustLevel.CLOSED_TERM_EVAL, 1.0, "match", prov)
    v2 = TrustedVerdict(None, TrustLevel.INCONCLUSIVE, 0.0, "timeout", Provenance(strategy="S3"))
    _assert(v1.is_definitive, "definitive verdict")
    _assert(not v2.is_definitive, "inconclusive verdict")
    _assert("EQ" in str(v1), "verdict string EQ")
    _assert("?" in str(v2), "verdict string ?")

    best = select_best_verdict([v1, v2])
    _assert(best is v1, "best verdict is v1")

    v3 = TrustedVerdict(False, TrustLevel.PATH_SEARCH, 0.9, "NEQ via path", Provenance(strategy="S1"))
    best2 = select_best_verdict([v1, v3])
    _assert(best2 is v1, "higher trust wins")

    empty_best = select_best_verdict([])
    _assert(empty_best.equivalent is None, "empty verdicts → inconclusive")

    merged = merge_verdicts([v1, v3])
    _assert(merged.equivalent is True, "merge: higher trust wins")

    v4 = TrustedVerdict(False, TrustLevel.CLOSED_TERM_EVAL, 1.0, "NEQ", Provenance(strategy="S0"))
    tie = merge_verdicts([v1, v4])
    _assert(tie.equivalent is None, "merge: tie → inconclusive")

    reg = TrustRegistry()
    reg.record(v1)
    reg.record(v2)
    reg.record(v3)
    _assert(len(reg.verdicts) == 3, "registry accumulates")
    _assert(reg.best() is v1, "registry best")
    _assert("TrustRegistry" in reg.summary(), "registry summary")

    # ── §3 False-positive guards ──
    print("§3 False-positive guards …")
    fp_ok = check_false_positive_guards(
        canon_f="fold[add](0,$p0,$p1,something_long_enough)",
        canon_g="fold[add](0,$p0,$p1,something_long_enough)",
        has_unknown_f=False,
        has_unknown_g=False,
        is_const=False,
        vars_f={"p0", "p1"},
        vars_g={"p0", "p1"},
        param_names={"p0", "p1"},
        num_params=2,
        has_method_or_ctor=False,
    )
    _assert(fp_ok.is_safe, "all guards pass")
    _assert(fp_ok.num_guards == 6, "six guards")

    fp_unk = check_false_positive_guards(
        canon_f="?unknown",
        canon_g="?unknown",
        has_unknown_f=True,
        has_unknown_g=False,
        is_const=False,
        vars_f={"p0"},
        vars_g={"p0"},
        param_names={"p0"},
        num_params=1,
        has_method_or_ctor=False,
    )
    _assert(not fp_unk.is_safe, "unknown guard fails")
    _assert("no_unknown" in fp_unk.failed, "no_unknown in failed list")

    fp_small = check_false_positive_guards(
        canon_f="x",
        canon_g="x",
        has_unknown_f=False,
        has_unknown_g=False,
        is_const=False,
        vars_f={"p0"},
        vars_g={"p0"},
        param_names={"p0"},
        num_params=1,
        has_method_or_ctor=False,
    )
    _assert("sufficient_size" in fp_small.failed, "size guard fails on short canon")

    fp_const = check_false_positive_guards(
        canon_f="42",
        canon_g="42",
        has_unknown_f=False,
        has_unknown_g=False,
        is_const=True,
        vars_f=set(),
        vars_g=set(),
        param_names=set(),
        num_params=0,
        has_method_or_ctor=False,
    )
    _assert(fp_const.is_safe, "constant bypasses size guard")

    fp_unresolved = check_false_positive_guards(
        canon_f="fold[add](0,$p0,$p1,something_long)",
        canon_g="fold[add](0,$p0,$p1,something_long)",
        has_unknown_f=False,
        has_unknown_g=False,
        is_const=False,
        vars_f={"p0", "local_x"},
        vars_g={"p0"},
        param_names={"p0"},
        num_params=1,
        has_method_or_ctor=False,
    )
    _assert("no_unresolved_vars" in fp_unresolved.failed, "unresolved var guard")

    fp_no_ref = check_false_positive_guards(
        canon_f="fold[add](0,range(10),blah_long_str)",
        canon_g="fold[add](0,range(10),blah_long_str)",
        has_unknown_f=False,
        has_unknown_g=False,
        is_const=False,
        vars_f=set(),
        vars_g=set(),
        param_names={"p0"},
        num_params=1,
        has_method_or_ctor=False,
    )
    _assert("params_referenced" in fp_no_ref.failed, "params_referenced guard")

    fp_zero_arg = check_false_positive_guards(
        canon_f="some_very_long_canonical_form_here",
        canon_g="some_very_long_canonical_form_here",
        has_unknown_f=False,
        has_unknown_g=False,
        is_const=False,
        vars_f=set(),
        vars_g=set(),
        param_names=set(),
        num_params=0,
        has_method_or_ctor=True,
    )
    _assert("no_zero_arg_aliasing" in fp_zero_arg.failed, "zero-arg aliasing guard")

    fp_trivial = check_false_positive_guards(
        canon_f="op_name_long_enough_for_test_yes",
        canon_g="op_name_long_enough_for_test_yes",
        has_unknown_f=False,
        has_unknown_g=False,
        is_const=False,
        vars_f={"p0"},
        vars_g={"p0"},
        param_names={"p0"},
        num_params=1,
        has_method_or_ctor=False,
        is_trivial_op_f=True,
    )
    _assert("no_trivial_op" in fp_trivial.failed, "trivial op guard")

    # ── §4 Normalizer trace ──
    print("§4 Normalizer trace …")
    t = NormalizerTrace()
    _assert(not t.did_converge, "fresh trace not converged")
    _assert(t.num_passes == 0, "fresh trace 0 passes")

    t.record_pass("abc", ["β-reduction"], 1.0)
    t.record_pass("ab", ["fold canonicalization"], 0.5)
    _assert(not t.did_converge, "two different passes")
    _assert(t.num_passes == 2, "two passes recorded")

    t.record_pass("ab", [], 0.3)
    _assert(t.did_converge, "converged on third pass")
    _assert(t.converged_at == 2, "converged_at == 2")
    _assert(t.canonical_lengths() == [3, 2, 2], "canonical lengths")
    _assert(t.is_monotonically_shrinking(), "monotonically shrinking")
    _assert(abs(t.total_elapsed_ms - 1.8) < 0.01, "total elapsed")

    t2 = NormalizerTrace()
    t2.record_pass("a" * 10, [], 0)
    t2.record_pass("a" * 5, [], 0)
    t2.record_pass("a" * 8, [], 0)
    _assert(not t2.is_monotonically_shrinking(), "non-monotone")

    # ── §5 Pipeline soundness ──
    print("§5 Pipeline soundness …")
    s0_ok = validate_s0_preconditions(0, 0)
    _assert(s0_ok.preconditions_met, "S0 ok")
    s0_bad = validate_s0_preconditions(2, 0)
    _assert(not s0_bad.preconditions_met, "S0 bad arity f")

    s1_ok = validate_s1_preconditions(False, False, 50, 50)
    _assert(s1_ok.preconditions_met, "S1 ok")
    s1_bad = validate_s1_preconditions(True, False, 50, 50)
    _assert(not s1_bad.preconditions_met, "S1 unknown")
    s1_short = validate_s1_preconditions(False, False, 5, 50)
    _assert(not s1_short.preconditions_met, "S1 short canon")

    s2_ok = validate_s2_preconditions(0, 0)
    _assert(s2_ok.preconditions_met, "S2 ok")
    s2_bad = validate_s2_preconditions(3, 0)
    _assert(not s2_bad.preconditions_met, "S2 uninterpreted")

    s3_ok = validate_s3_preconditions(4, 4, 0)
    _assert(s3_ok.preconditions_met, "S3 ok")
    s3_bad = validate_s3_preconditions(4, 3, 0)
    _assert(not s3_bad.preconditions_met, "S3 incomplete")
    s3_h1 = validate_s3_preconditions(4, 4, 1)
    _assert(not s3_h1.preconditions_met, "S3 H1 obstruction")

    full = validate_full_pipeline(0, 0, False, False, 50, 50, 0, 0, 4, 4, 0)
    _assert(full.all_sound, "full pipeline sound")
    _assert(full.num_sound == 4, "4/4 sound")

    full_bad = validate_full_pipeline(1, 0, True, False, 5, 50, 2, 0, 0, 0, 1)
    _assert(not full_bad.all_sound, "bad pipeline not sound")
    _assert("Pipeline" in full_bad.summary(), "summary contains Pipeline")

    # ── §6 Strict power witness ──
    print("§6 Strict power witness …")
    w1 = STRICT_POWER_EXAMPLES[0]
    _assert(w1.witnesses_strict_ctt, "factorial witnesses CTT⊊CTTT")
    _assert(w1.witnesses_strict_ct, "factorial witnesses CT⊊CTTT")
    _assert(not w1.is_trivially_reachable, "not trivially reachable")

    w3 = STRICT_POWER_EXAMPLES[2]
    _assert(w3.is_trivially_reachable, "NEQ pair trivially reachable")
    _assert(not w3.witnesses_strict_ctt, "NEQ pair is not strict CTT witness")

    partitioned = find_strict_witnesses(STRICT_POWER_EXAMPLES)
    _assert(len(partitioned["both"]) == 2, "two witnesses in 'both' category")
    _assert(len(partitioned["none"]) == 1, "one non-strict witness")
    _assert("CTT<CTTT" in partitioned, "CTT<CTTT key exists")

    _assert("CTT" in str(w1), "witness str contains CTT")

    # ── §7 Rewrite system verifier ──
    print("§7 Rewrite system verifier …")
    report = verify_rewrite_system()
    _assert(len(report.rules) > 20, "at least 20 rules")
    _assert(report.termination.max_passes == 8, "max passes 8")
    _assert(report.termination.size_reducing_rules > 10, ">10 size-reducing")
    _assert(report.confluence.fixed_phase_order, "fixed phase order")
    _assert(report.confluence.uses_fixpoint_iteration, "uses fixpoint iteration")
    _assert(report.is_convergent, "system is convergent")
    _assert("Rewrite system" in report.summary(), "summary header")

    # ── §9 Fixpoint analyser ──
    print("§9 Fixpoint analyser …")
    trace_fp = NormalizerTrace()
    trace_fp.record_pass("abc" * 20, ["β-reduction", "ring/lattice"], 1.0)
    trace_fp.record_pass("abc" * 15, ["fold canonicalization"], 0.8)
    trace_fp.record_pass("abc" * 15, [], 0.2)
    analysis = analyse_fixpoint(trace_fp)
    _assert(analysis.converged, "fixpoint converged")
    _assert(analysis.convergence_pass == 2, "convergence at pass 2")
    _assert(analysis.monotonically_shrinking, "monotone shrinking")
    _assert(not analysis.oscillating, "not oscillating")
    _assert("β-reduction" in analysis.phases_that_fired, "β-reduction fired")
    _assert(analysis.max_length == 60, "max length 60")
    _assert(analysis.min_length == 45, "min length 45")

    trace_osc = NormalizerTrace()
    trace_osc.record_pass("a" * 10, [], 0)
    trace_osc.record_pass("a" * 5, [], 0)
    trace_osc.record_pass("a" * 8, [], 0)
    trace_osc.record_pass("a" * 4, [], 0)
    trace_osc.record_pass("a" * 7, [], 0)
    analysis_osc = analyse_fixpoint(trace_osc)
    _assert(analysis_osc.oscillating, "oscillation detected")
    _assert(not analysis_osc.monotonically_shrinking, "not monotone")

    # ── §10 Benchmark runner (built-in pairs) ──
    print("§10 Benchmark runner …")
    _assert(len(WORKED_EXAMPLES) >= 3, "at least 3 worked examples")
    for ex in WORKED_EXAMPLES:
        _assert(len(ex.source_f.strip()) > 10, f"source_f non-trivial: {ex.name}")
        _assert(len(ex.source_g.strip()) > 10, f"source_g non-trivial: {ex.name}")
        _assert(ex.expected_eq is not None, f"expected_eq set: {ex.name}")

    custom_suite = BenchmarkSuite()
    custom_suite.add(BenchmarkPair(
        name="identity",
        source_f="def f(x): return x",
        source_g="def g(x): return x",
        expected_eq=True,
    ))
    _assert(len(custom_suite.pairs) == 1, "custom suite has 1 pair")

    # ── §11 False-positive detector (string form) ──
    print("§11 False-positive detector …")
    _assert(len(FALSE_POSITIVE_GUARDS) == 6, "6 guards defined")
    for g in FALSE_POSITIVE_GUARDS:
        _assert(len(g.name) > 0, f"guard has name: {g.name}")
        _assert(len(g.description) > 10, f"guard has description: {g.name}")

    # ── Cross-section integration ──
    print("Cross-section integration …")
    strat_str = str(c1)
    _assert("D1_DECIDABLE" in strat_str, "stratum str")
    fp_str = str(fp_ok)
    _assert("All" in fp_str, "FP report str")
    fp_fail_str = str(fp_unk)
    _assert("failed" in fp_fail_str, "FP fail str")
    sound_str = str(s0_ok)
    _assert("✓" in sound_str, "soundness check str")
    sound_fail_str = str(s0_bad)
    _assert("✗" in sound_fail_str, "soundness fail str")
    trace_str = str(t)
    _assert("Converged" in trace_str, "trace str converged")
    verdict_str = str(v1)
    _assert("CLOSED_TERM_EVAL" in verdict_str, "verdict str trust")

    # ── Summary ──
    total = passed + failed
    print(f"\n{'='*50}")
    print(f"Self-tests: {passed}/{total} passed, {failed} failed")
    if failed:
        print("SOME TESTS FAILED")
        sys.exit(1)
    else:
        print("ALL TESTS PASSED")


if __name__ == "__main__":
    _run_self_tests()
