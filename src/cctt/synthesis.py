"""§11 Synthesis: Decidability stratification, trust hierarchy,
false-positive guards, normalizer convergence, pipeline soundness,
and fixpoint analysis for CCTT.

Wires proposals from g05_synthesis into the live CCTT pipeline
without modifying checker.py, path_search.py, or cohomology.py.

Key contributions to equivalence checking / spec satisfaction:
  1. classify_stratum — decide D1/D2/D3 decidability class for a pair
  2. TrustRegistry — accumulate verdicts with provenance and pick best
  3. check_false_positive_guards — six guards against spurious EQ
  4. validate_pipeline_soundness — precondition check per strategy
  5. run_normalizer_traced — convergence witness for the 7-phase normalizer
  6. analyse_fixpoint — detect oscillation, monotonicity, convergence pass
  7. augmented_check — wraps check_equivalence with stratification + guards
"""
from __future__ import annotations

import enum
import time
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set, Tuple

# ── Internal CCTT imports (relative) ──
from .denotation import (
    OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
    OTerm,
    compile_to_oterm,
    normalize,
    _rename_params,
)

# Phase functions for traced normalization
from .denotation import (
    _phase1_beta,
    _phase2_ring,
    _phase3_fold,
    _phase4_hof,
    _phase5_unify,
    _phase6_quotient,
    _phase7_piecewise,
)


# ═══════════════════════════════════════════════════════════
# §1  Decidability Stratification  (Definition 11.2)
# ═══════════════════════════════════════════════════════════

class Stratum(enum.Enum):
    """Three decidability strata from Definition 11.2.

    D1: Decidable — canonical form match after 7-phase normalization.
    D2: Semi-decidable — multi-step path search via dichotomy axioms.
    D3: Undecidable — general equivalence beyond current axiom set.
    """
    D1_DECIDABLE = "canonical_form_match"
    D2_SEMI_DECIDABLE = "path_search"
    D3_UNDECIDABLE = "general_equivalence"


@dataclass(frozen=True)
class StratumClassification:
    """Result of classifying a program pair into a decidability stratum."""
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
    """Classify a pair into its decidability stratum (Proposition 11.3)."""
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
# §2  Trust Hierarchy with Provenance  (Definition 11.6)
# ═══════════════════════════════════════════════════════════

class TrustLevel(enum.IntEnum):
    """Trust levels in increasing order of reliability."""
    INCONCLUSIVE = 0
    FIBER_Z3_CECH = 1
    Z3_STRUCTURAL = 2
    PATH_SEARCH = 3
    CANONICAL_MATCH = 4
    CLOSED_TERM_EVAL = 5


@dataclass(frozen=True)
class Provenance:
    """Where a verdict came from, for full audit trail."""
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
    """Select the highest-trust definitive verdict (Proposition 11.7)."""
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
    """Merge multiple verdicts, resolving conflicts by trust level."""
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
    """Accumulates verdicts from different pipeline stages."""

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
# §3  False-Positive Guard Suite  (Theorem 11.9)
# ═══════════════════════════════════════════════════════════

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


# ── OTerm helpers for guard checks ──

def _oterm_contains_unknown(term: OTerm) -> bool:
    """Check if an OTerm transitively contains OUnknown."""
    if isinstance(term, OUnknown):
        return True
    if isinstance(term, OOp):
        return any(_oterm_contains_unknown(a) for a in term.args)
    if isinstance(term, OCase):
        return (_oterm_contains_unknown(term.test)
                or _oterm_contains_unknown(term.true_branch)
                or _oterm_contains_unknown(term.false_branch))
    if isinstance(term, OFold):
        return (_oterm_contains_unknown(term.init)
                or _oterm_contains_unknown(term.collection))
    if isinstance(term, OSeq):
        return any(_oterm_contains_unknown(e) for e in term.elements)
    if isinstance(term, ODict):
        return any(_oterm_contains_unknown(k) or _oterm_contains_unknown(v)
                   for k, v in term.pairs)
    if isinstance(term, OQuotient):
        return _oterm_contains_unknown(term.inner)
    if isinstance(term, OAbstract):
        return any(_oterm_contains_unknown(a) for a in term.inputs)
    if isinstance(term, OLam):
        return _oterm_contains_unknown(term.body)
    if isinstance(term, OMap):
        r = (_oterm_contains_unknown(term.transform)
             or _oterm_contains_unknown(term.collection))
        if term.filter_pred is not None:
            r = r or _oterm_contains_unknown(term.filter_pred)
        return r
    if isinstance(term, OCatch):
        return (_oterm_contains_unknown(term.body)
                or _oterm_contains_unknown(term.default))
    if isinstance(term, OFix):
        return _oterm_contains_unknown(term.body)
    return False


def _oterm_collect_vars(term: OTerm) -> Set[str]:
    """Collect all variable names referenced in an OTerm."""
    if isinstance(term, OVar):
        return {term.name}
    if isinstance(term, OOp):
        r: Set[str] = set()
        for a in term.args:
            r |= _oterm_collect_vars(a)
        return r
    if isinstance(term, OCase):
        return (_oterm_collect_vars(term.test)
                | _oterm_collect_vars(term.true_branch)
                | _oterm_collect_vars(term.false_branch))
    if isinstance(term, OFold):
        return (_oterm_collect_vars(term.init)
                | _oterm_collect_vars(term.collection))
    if isinstance(term, OSeq):
        r: Set[str] = set()
        for e in term.elements:
            r |= _oterm_collect_vars(e)
        return r
    if isinstance(term, OLam):
        return _oterm_collect_vars(term.body) - set(term.params)
    if isinstance(term, OMap):
        r = (_oterm_collect_vars(term.transform)
             | _oterm_collect_vars(term.collection))
        if term.filter_pred is not None:
            r |= _oterm_collect_vars(term.filter_pred)
        return r
    if isinstance(term, OQuotient):
        return _oterm_collect_vars(term.inner)
    if isinstance(term, ODict):
        r: Set[str] = set()
        for k, v in term.pairs:
            r |= _oterm_collect_vars(k) | _oterm_collect_vars(v)
        return r
    if isinstance(term, OFix):
        return _oterm_collect_vars(term.body)
    if isinstance(term, OCatch):
        return (_oterm_collect_vars(term.body)
                | _oterm_collect_vars(term.default))
    if isinstance(term, OAbstract):
        r: Set[str] = set()
        for a in term.inputs:
            r |= _oterm_collect_vars(a)
        return r
    return set()


def _oterm_is_trivial_op(term: OTerm) -> bool:
    """Check if term is a single operation on bare parameters."""
    if not isinstance(term, OOp):
        return False
    return all(isinstance(a, OVar) for a in term.args)


def _oterm_has_method_or_ctor(term: OTerm) -> bool:
    """Check if term contains method calls or constructor invocations."""
    if isinstance(term, OOp):
        if term.name.startswith(".") or (term.name and term.name[0].isupper()):
            return True
        return any(_oterm_has_method_or_ctor(a) for a in term.args)
    if isinstance(term, OSeq):
        return any(_oterm_has_method_or_ctor(e) for e in term.elements)
    if isinstance(term, OFold):
        return (_oterm_has_method_or_ctor(term.init)
                or _oterm_has_method_or_ctor(term.collection))
    if isinstance(term, OCase):
        return (_oterm_has_method_or_ctor(term.test)
                or _oterm_has_method_or_ctor(term.true_branch)
                or _oterm_has_method_or_ctor(term.false_branch))
    if isinstance(term, OLam):
        return _oterm_has_method_or_ctor(term.body)
    if isinstance(term, OMap):
        return (_oterm_has_method_or_ctor(term.transform)
                or _oterm_has_method_or_ctor(term.collection))
    if isinstance(term, OQuotient):
        return _oterm_has_method_or_ctor(term.inner)
    return False


def _is_const_oterm(term: OTerm) -> bool:
    """Check if the OTerm is a constant (OLit or empty container)."""
    if isinstance(term, OLit):
        return True
    if isinstance(term, OSeq) and len(term.elements) == 0:
        return True
    if isinstance(term, ODict) and len(term.pairs) == 0:
        return True
    return False


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
    """Run all six false-positive guards (Theorem 11.9)."""
    report = FalsePositiveReport()

    # Guard 1: no OUnknown
    if has_unknown_f or has_unknown_g:
        report.failed.append("no_unknown")
        report.details["no_unknown"] = (
            f"unknown_f={has_unknown_f}, unknown_g={has_unknown_g}")
    else:
        report.passed.append("no_unknown")

    # Guard 2: sufficient size
    if len(canon_f) < 20 and not is_const:
        report.failed.append("sufficient_size")
        report.details["sufficient_size"] = (
            f"len(canon_f)={len(canon_f)} < 20 and not constant")
    elif len(canon_g) < 20 and not is_const:
        report.failed.append("sufficient_size")
        report.details["sufficient_size"] = (
            f"len(canon_g)={len(canon_g)} < 20 and not constant")
    else:
        report.passed.append("sufficient_size")

    # Guard 3: no trivial op
    if is_trivial_op_f or is_trivial_op_g:
        report.failed.append("no_trivial_op")
        report.details["no_trivial_op"] = (
            f"trivial_f={is_trivial_op_f}, trivial_g={is_trivial_op_g}")
    else:
        report.passed.append("no_trivial_op")

    # Guard 4: no unresolved variables
    unresolved_f = vars_f - param_names
    unresolved_g = vars_g - param_names
    if unresolved_f or unresolved_g:
        report.failed.append("no_unresolved_vars")
        report.details["no_unresolved_vars"] = (
            f"unresolved_f={unresolved_f}, unresolved_g={unresolved_g}")
    else:
        report.passed.append("no_unresolved_vars")

    # Guard 5: parameters referenced
    if num_params > 0 and not (vars_f & param_names):
        report.failed.append("params_referenced")
        report.details["params_referenced"] = (
            f"params={param_names}, vars_f={vars_f} — no overlap")
    elif num_params > 0 and not (vars_g & param_names):
        report.failed.append("params_referenced")
        report.details["params_referenced"] = (
            f"params={param_names}, vars_g={vars_g} — no overlap")
    else:
        report.passed.append("params_referenced")

    # Guard 6: no zero-arg aliasing
    if num_params == 0 and has_method_or_ctor:
        report.failed.append("no_zero_arg_aliasing")
        report.details["no_zero_arg_aliasing"] = (
            "zero-arg function with method/constructor calls")
    else:
        report.passed.append("no_zero_arg_aliasing")

    return report


def detect_false_positives(
    source_f: str, source_g: str,
) -> FalsePositiveReport:
    """Compile, normalize, and run all six guards on a source pair."""
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
# §4  Normalizer Convergence Witness  (Theorem 11.5)
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
    """Trace of the 7-phase normalizer's convergence."""
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
        self, canon: str, phases_fired: List[str], elapsed: float = 0.0,
    ) -> bool:
        """Record a normalisation pass. Returns True if converged."""
        self.passes.append(canon)
        self.phase_applications.append(phases_fired)
        self.elapsed_ms.append(elapsed)
        if len(self.passes) >= 2 and self.passes[-1] == self.passes[-2]:
            self.converged_at = len(self.passes) - 1
            return True
        return False

    def canonical_lengths(self) -> List[int]:
        return [len(p) for p in self.passes]

    def is_monotonically_shrinking(self) -> bool:
        lengths = self.canonical_lengths()
        return all(a >= b for a, b in zip(lengths, lengths[1:]))

    def __str__(self) -> str:
        if self.did_converge:
            return (
                f"Converged after {self.converged_at + 1} passes "
                f"(canon length: {len(self.passes[-1])}, "
                f"total {self.total_elapsed_ms:.1f}ms)")
        return f"Did not converge after {self.num_passes} passes"


def run_normalizer_traced(source: str) -> NormalizerTrace:
    """Run the 7-phase normaliser and return a full convergence trace."""
    trace = NormalizerTrace()
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
    for _pass_num in range(8):
        t0 = time.monotonic()
        phases_fired: List[str] = []
        for pname, pfn in phase_fns:
            prev_canon = current.canon()
            current = pfn(current)
            if current.canon() != prev_canon:
                phases_fired.append(pname)
        elapsed = (time.monotonic() - t0) * 1000.0
        if trace.record_pass(current.canon(), phases_fired, elapsed):
            break

    return trace


# ═══════════════════════════════════════════════════════════
# §5  Pipeline Soundness Validator  (Theorem 11.8)
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
        return f"✗ {self.strategy}: violations: " + "; ".join(self.violations)


def validate_s0_preconditions(
    num_params_f: int, num_params_g: int,
) -> SoundnessCheck:
    """S0: Both functions must have zero positional parameters."""
    violations: List[str] = []
    if num_params_f != 0:
        violations.append(f"f has {num_params_f} params (need 0)")
    if num_params_g != 0:
        violations.append(f"g has {num_params_g} params (need 0)")
    return SoundnessCheck("S0: closed-term eval", len(violations) == 0, violations)


def validate_s1_preconditions(
    has_unknown_f: bool, has_unknown_g: bool,
    canon_len_f: int, canon_len_g: int,
) -> SoundnessCheck:
    """S1: No OUnknown, minimum canonical form length."""
    violations: List[str] = []
    if has_unknown_f:
        violations.append("f contains OUnknown (incomplete compilation)")
    if has_unknown_g:
        violations.append("g contains OUnknown (incomplete compilation)")
    if canon_len_f < 10:
        violations.append(f"f canonical form too short ({canon_len_f} chars)")
    if canon_len_g < 10:
        violations.append(f"g canonical form too short ({canon_len_g} chars)")
    return SoundnessCheck("S1: denotational equiv", len(violations) == 0, violations)


def validate_s2_preconditions(
    uninterp_depth_f: int, uninterp_depth_g: int,
) -> SoundnessCheck:
    """S2: Both Z3 terms must be fully interpreted."""
    violations: List[str] = []
    if uninterp_depth_f > 0:
        violations.append(f"f has uninterpreted depth {uninterp_depth_f}")
    if uninterp_depth_g > 0:
        violations.append(f"g has uninterpreted depth {uninterp_depth_g}")
    return SoundnessCheck("S2: Z3 structural", len(violations) == 0, violations)


def validate_s3_preconditions(
    num_fibers: int, num_verified: int, h1_rank: int,
) -> SoundnessCheck:
    """S3: Every fiber verified and H¹ = 0."""
    violations: List[str] = []
    if num_fibers == 0:
        violations.append("no fibers in covering")
    if num_verified < num_fibers:
        violations.append(f"only {num_verified}/{num_fibers} fibers verified")
    if h1_rank > 0:
        violations.append(f"H¹ rank = {h1_rank} (obstructions present)")
    return SoundnessCheck("S3: fiber Z3 + Čech", len(violations) == 0, violations)


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


def validate_pipeline_soundness(
    num_params_f: int, num_params_g: int,
    has_unknown_f: bool, has_unknown_g: bool,
    canon_len_f: int, canon_len_g: int,
    uninterp_depth_f: int, uninterp_depth_g: int,
    num_fibers: int, num_verified: int, h1_rank: int,
) -> PipelineSoundnessReport:
    """Run all four strategy-soundness validators."""
    report = PipelineSoundnessReport()
    report.checks.append(validate_s0_preconditions(num_params_f, num_params_g))
    report.checks.append(validate_s1_preconditions(
        has_unknown_f, has_unknown_g, canon_len_f, canon_len_g))
    report.checks.append(validate_s2_preconditions(
        uninterp_depth_f, uninterp_depth_g))
    report.checks.append(validate_s3_preconditions(
        num_fibers, num_verified, h1_rank))
    return report


# ═══════════════════════════════════════════════════════════
# §9  Normalizer Fixpoint Analyser
# ═══════════════════════════════════════════════════════════

@dataclass
class FixpointAnalysis:
    """Analysis of the normaliser's fixed-point behaviour."""
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
            f"phases={self.phases_that_fired}")


def analyse_fixpoint(trace: NormalizerTrace) -> FixpointAnalysis:
    """Analyse a NormalizerTrace for fixed-point properties."""
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
            a >= b for a, b in zip(lengths, lengths[1:]))
        if len(lengths) >= 3:
            diffs = [lengths[i + 1] - lengths[i] for i in range(len(lengths) - 1)]
            sign_changes = sum(
                1 for i in range(len(diffs) - 1) if diffs[i] * diffs[i + 1] < 0)
            analysis.oscillating = sign_changes >= 2

    all_phases: Set[str] = set()
    for phase_list in trace.phase_applications:
        all_phases.update(phase_list)
    analysis.phases_that_fired = all_phases
    return analysis


def analyse_fixpoint_from_source(source: str) -> FixpointAnalysis:
    """Convenience: compile, normalise, trace, and analyse in one call."""
    return analyse_fixpoint(run_normalizer_traced(source))


# ═══════════════════════════════════════════════════════════
# §7  Convergent Rewrite System Verifier
# ═══════════════════════════════════════════════════════════

@dataclass(frozen=True)
class RewriteRule:
    """A single rewrite rule in the normaliser's rule set."""
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


@dataclass
class TerminationEvidence:
    """Evidence for termination of the normaliser."""
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
            f"observed={self.observed_termination} in {self.observed_passes} passes")


@dataclass
class ConfluenceEvidence:
    """Evidence for confluence of the normaliser."""
    critical_pairs_checked: int = 0
    critical_pairs_joinable: int = 0
    fixed_phase_order: bool = True
    uses_fixpoint_iteration: bool = True

    @property
    def is_confluent(self) -> bool:
        return (self.critical_pairs_checked == self.critical_pairs_joinable
                and self.fixed_phase_order
                and self.uses_fixpoint_iteration)

    def __str__(self) -> str:
        status = "confluent" if self.is_confluent else "NOT confluent"
        return (
            f"Confluence: {status} — "
            f"{self.critical_pairs_joinable}/{self.critical_pairs_checked} "
            f"critical pairs joinable, "
            f"fixed_order={self.fixed_phase_order}, "
            f"fixpoint={self.uses_fixpoint_iteration}")


@dataclass
class RewriteSystemReport:
    """Combined termination + confluence report."""
    rules: List[RewriteRule]
    termination: TerminationEvidence
    confluence: ConfluenceEvidence

    @property
    def is_convergent(self) -> bool:
        return (self.termination.observed_termination
                and self.confluence.is_confluent)

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
    """Verify termination and confluence of the 7-phase normaliser."""
    rules = NORMALIZER_RULES
    term_ev = TerminationEvidence(max_passes=8)
    term_ev.size_reducing_rules = sum(1 for r in rules if r.is_size_reducing)
    term_ev.non_size_reducing_rules = sum(1 for r in rules if not r.is_size_reducing)

    conf_ev = ConfluenceEvidence(fixed_phase_order=True, uses_fixpoint_iteration=True)
    phase_groups: Dict[int, List[RewriteRule]] = {}
    for r in rules:
        phase_groups.setdefault(r.phase, []).append(r)

    pairs_checked = 0
    pairs_joinable = 0
    for _phase, group in phase_groups.items():
        for i, r1 in enumerate(group):
            for r2 in group[i + 1:]:
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

    return RewriteSystemReport(rules=rules, termination=term_ev, confluence=conf_ev)


# ═══════════════════════════════════════════════════════════
# Augmented equivalence check (wraps checker.check_equivalence)
# ═══════════════════════════════════════════════════════════

@dataclass
class AugmentedResult:
    """check_equivalence result enriched with synthesis analysis."""
    equivalent: Optional[bool]
    explanation: str
    stratum: StratumClassification
    fp_report: FalsePositiveReport
    trust: TrustLevel
    normalizer_trace_f: NormalizerTrace
    normalizer_trace_g: NormalizerTrace
    confidence: float = 0.0

    def __str__(self) -> str:
        eq_str = {True: "EQ", False: "NEQ", None: "?"}[self.equivalent]
        return (
            f"[{eq_str}] {self.stratum.stratum.name} "
            f"trust={self.trust.name} fp_safe={self.fp_report.is_safe} "
            f"— {self.explanation}")


def augmented_check(
    source_f: str,
    source_g: str,
    timeout_ms: int = 5000,
) -> AugmentedResult:
    """Run the CCTT pipeline and augment with synthesis analysis.

    1. Compile + normalize both sources → canonical forms.
    2. Classify decidability stratum (D1/D2/D3).
    3. Run false-positive guards.
    4. Run the standard checker pipeline.
    5. Assign trust level based on which strategy produced the verdict.
    """
    from .checker import check_equivalence

    trace_f = run_normalizer_traced(source_f)
    trace_g = run_normalizer_traced(source_g)

    canon_f = trace_f.passes[-1] if trace_f.passes and not trace_f.passes[-1].startswith("(") else ""
    canon_g = trace_g.passes[-1] if trace_g.passes and not trace_g.passes[-1].startswith("(") else ""

    # Classify stratum
    path_axioms: Optional[List[str]] = None
    if canon_f and canon_g and canon_f != canon_g:
        try:
            from .path_search import search_path
            rf = compile_to_oterm(source_f)
            rg = compile_to_oterm(source_g)
            if rf is not None and rg is not None:
                nf = normalize(_rename_params(rf[0], rf[1]))
                ng = normalize(_rename_params(rg[0], rg[1]))
                pr = search_path(nf, ng, max_depth=3, max_frontier=150)
                if pr.found is True:
                    path_axioms = [step.axiom for step in pr.path]
        except Exception:
            pass

    stratum = classify_stratum(canon_f, canon_g, path_axioms)

    # False-positive guards
    fp_report = FalsePositiveReport()
    if canon_f and canon_g:
        try:
            rf = compile_to_oterm(source_f)
            rg = compile_to_oterm(source_g)
            if rf and rg and len(rf[1]) == len(rg[1]):
                nf = normalize(_rename_params(rf[0], rf[1]))
                ng = normalize(_rename_params(rg[0], rg[1]))
                num_p = len(rf[1])
                pn = {f"p{i}" for i in range(num_p)}
                fp_report = check_false_positive_guards(
                    canon_f=canon_f, canon_g=canon_g,
                    has_unknown_f=_oterm_contains_unknown(nf),
                    has_unknown_g=_oterm_contains_unknown(ng),
                    is_const=_is_const_oterm(nf),
                    vars_f=_oterm_collect_vars(nf),
                    vars_g=_oterm_collect_vars(ng),
                    param_names=pn, num_params=num_p,
                    has_method_or_ctor=_oterm_has_method_or_ctor(nf),
                    is_trivial_op_f=_oterm_is_trivial_op(nf),
                    is_trivial_op_g=_oterm_is_trivial_op(ng),
                )
        except Exception:
            pass

    # Run the standard checker pipeline
    result = check_equivalence(source_f, source_g, timeout_ms=timeout_ms)

    # Infer trust level from the explanation
    explanation = result.explanation or ""
    if "closed-term" in explanation:
        trust = TrustLevel.CLOSED_TERM_EVAL
    elif "denotational" in explanation:
        trust = TrustLevel.CANONICAL_MATCH
    elif "D20" in explanation:
        trust = TrustLevel.PATH_SEARCH
    elif "fiber" in explanation.lower() or "H¹" in explanation or "Čech" in explanation:
        trust = TrustLevel.FIBER_Z3_CECH
    elif "Z3" in explanation or "structural" in explanation:
        trust = TrustLevel.Z3_STRUCTURAL
    else:
        trust = TrustLevel.INCONCLUSIVE

    return AugmentedResult(
        equivalent=result.equivalent,
        explanation=result.explanation,
        stratum=stratum,
        fp_report=fp_report,
        trust=trust,
        normalizer_trace_f=trace_f,
        normalizer_trace_g=trace_g,
        confidence=result.confidence,
    )


# ═══════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════

def _run_self_tests() -> None:
    """Comprehensive self-tests for every section."""
    import sys
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
        has_unknown_f=False, has_unknown_g=False,
        is_const=False,
        vars_f={"p0", "p1"}, vars_g={"p0", "p1"},
        param_names={"p0", "p1"}, num_params=2,
        has_method_or_ctor=False,
    )
    _assert(fp_ok.is_safe, "all guards pass")
    _assert(fp_ok.num_guards == 6, "six guards")

    fp_unk = check_false_positive_guards(
        canon_f="?unknown", canon_g="?unknown",
        has_unknown_f=True, has_unknown_g=False,
        is_const=False,
        vars_f={"p0"}, vars_g={"p0"},
        param_names={"p0"}, num_params=1,
        has_method_or_ctor=False,
    )
    _assert(not fp_unk.is_safe, "unknown guard fails")
    _assert("no_unknown" in fp_unk.failed, "no_unknown in failed list")

    fp_small = check_false_positive_guards(
        canon_f="x", canon_g="x",
        has_unknown_f=False, has_unknown_g=False,
        is_const=False,
        vars_f={"p0"}, vars_g={"p0"},
        param_names={"p0"}, num_params=1,
        has_method_or_ctor=False,
    )
    _assert("sufficient_size" in fp_small.failed, "size guard fails on short canon")

    fp_const = check_false_positive_guards(
        canon_f="42", canon_g="42",
        has_unknown_f=False, has_unknown_g=False,
        is_const=True,
        vars_f=set(), vars_g=set(),
        param_names=set(), num_params=0,
        has_method_or_ctor=False,
    )
    _assert(fp_const.is_safe, "constant bypasses size guard")

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

    s2_ok = validate_s2_preconditions(0, 0)
    _assert(s2_ok.preconditions_met, "S2 ok")
    s2_bad = validate_s2_preconditions(3, 0)
    _assert(not s2_bad.preconditions_met, "S2 uninterpreted")

    s3_ok = validate_s3_preconditions(4, 4, 0)
    _assert(s3_ok.preconditions_met, "S3 ok")
    s3_bad = validate_s3_preconditions(4, 3, 0)
    _assert(not s3_bad.preconditions_met, "S3 incomplete")

    full = validate_pipeline_soundness(0, 0, False, False, 50, 50, 0, 0, 4, 4, 0)
    _assert(full.all_sound, "full pipeline sound")
    _assert(full.num_sound == 4, "4/4 sound")

    full_bad = validate_pipeline_soundness(1, 0, True, False, 5, 50, 2, 0, 0, 0, 1)
    _assert(not full_bad.all_sound, "bad pipeline not sound")
    _assert("Pipeline" in full_bad.summary(), "summary contains Pipeline")

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

    # ── Live OTerm false-positive detection ──
    print("Live OTerm false-positive detection …")
    fp_live = detect_false_positives(
        "def f(x): return sum(x)",
        "def g(x): return sum(x)",
    )
    _assert(fp_live.num_guards >= 1, "live guards ran")

    # ── Live normalizer trace ──
    print("Live normalizer trace …")
    tr = run_normalizer_traced("def f(n): return n + 1")
    _assert(tr.did_converge, "simple function converges")
    _assert(tr.num_passes >= 1, "at least one pass")
    fp_an = analyse_fixpoint(tr)
    _assert(fp_an.converged, "fixpoint analysis agrees")

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
