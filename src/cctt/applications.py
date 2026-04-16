"""Applications of the CCTT pipeline to real-world verification scenarios.

Implements the proposals from g14_applications.py on top of checker.py:
  1. VerificationInstance — explicit (f, T, U) triple with serialisation
  2. GradedVerdict — κ-confidence with Wilson intervals + provenance
  3. verify() — unified dispatcher across equivalence/spec/bug modes
  4. StrategyPipeline — composable S0–S4 with short-circuiting
  5. H¹ bug localisation — BugWitness + pytest generation
  6. BayesianConfidence — Beta-posterior updating per fiber
  7. Confidence monotonicity check (Proposition confidence-monotonicity)
  8. PipelineProfiler — per-stage timing instrumentation
  9. VerificationCache — LRU memoisation keyed by source hashes
 10. BatchRunner — parallel verification with ThreadPoolExecutor
 11. RegressionDetector — cross-version regression / fix detection
 12. Helpers — verdict_from_cech, verdict_from_result
"""
from __future__ import annotations

import hashlib
import json
import math
import time
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from enum import Enum
from typing import (
    Any,
    Callable,
    Dict,
    List,
    Optional,
    Sequence,
    Tuple,
)

try:
    from .checker import Result, check_equivalence, check_spec, find_bugs
    from .cohomology import CechResult, LocalJudgment
    _HAS_CCTT = True
except Exception:
    _HAS_CCTT = False

    @dataclass
    class Result:                            # type: ignore[no-redef]
        """Fallback Result when cctt is not importable."""
        equivalent: Optional[bool]
        explanation: str
        h0: int = 0
        h1: int = 0
        confidence: float = 0.0

    @dataclass
    class LocalJudgment:                     # type: ignore[no-redef]
        """Fallback LocalJudgment."""
        fiber: Tuple[str, ...]
        is_equivalent: Optional[bool]
        counterexample: Optional[str] = None
        explanation: str = ""
        concrete_obstruction: bool = False

    @dataclass
    class CechResult:                        # type: ignore[no-redef]
        """Fallback CechResult."""
        h0: int
        h1_rank: int
        total_fibers: int
        unknown_fibers: int
        obstructions: List[Tuple[str, ...]]

    def check_equivalence(src_f: str, src_g: str, timeout_ms: int = 5000) -> Result:
        return Result(None, "cctt not available")

    def check_spec(src: str, spec_src: str, timeout_ms: int = 5000) -> Result:
        return check_equivalence(src, spec_src, timeout_ms)

    def find_bugs(src: str, spec_src: str, timeout_ms: int = 5000) -> Result:
        r = check_equivalence(src, spec_src, timeout_ms)
        if r.equivalent is False:
            r.explanation = f"BUG: {r.explanation}"
        return r


# ═══════════════════════════════════════════════════════════════════════
#  §1  VerificationInstance — explicit (f, T, U) with serialisation
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class VerificationInstance:
    """A verification instance (f, T, U).

    Attributes
    ----------
    subject_source : str
        Python source of the program under test.
    target_source : str
        Python source of the reference / spec implementation.
    cover : list of str-tuples, optional
        Type-fiber cover U = {U_1, …, U_n}.
    mode : str
        One of ``'equivalence'``, ``'spec'``, ``'bug'``.
    metadata : dict
        Arbitrary key/value pairs for provenance tracking.
    """

    subject_source: str
    target_source: str
    cover: Optional[List[Tuple[str, ...]]] = None
    mode: str = "equivalence"
    metadata: Dict[str, Any] = field(default_factory=dict)

    def __post_init__(self) -> None:
        if self.mode not in ("equivalence", "spec", "bug"):
            raise ValueError(
                f"mode must be 'equivalence', 'spec', or 'bug'; got {self.mode!r}"
            )
        if self.cover is not None:
            for fiber in self.cover:
                if not isinstance(fiber, tuple) or not all(isinstance(t, str) for t in fiber):
                    raise TypeError(f"each cover element must be tuple[str, ...]; got {fiber!r}")

    @property
    def source_hash(self) -> str:
        """Deterministic hash of (subject, target, mode) for caching."""
        blob = json.dumps(
            [self.subject_source, self.target_source, self.mode],
            sort_keys=True,
        ).encode()
        return hashlib.sha256(blob).hexdigest()[:16]

    def to_dict(self) -> Dict[str, Any]:
        return {
            "subject_source": self.subject_source,
            "target_source": self.target_source,
            "cover": [list(f) for f in self.cover] if self.cover else None,
            "mode": self.mode,
            "metadata": self.metadata,
        }

    def to_json(self) -> str:
        return json.dumps(self.to_dict(), indent=2)

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> "VerificationInstance":
        cover_raw = d.get("cover")
        cover = [tuple(f) for f in cover_raw] if cover_raw is not None else None
        return cls(
            subject_source=d["subject_source"],
            target_source=d["target_source"],
            cover=cover,
            mode=d.get("mode", "equivalence"),
            metadata=d.get("metadata", {}),
        )

    @classmethod
    def from_json(cls, s: str) -> "VerificationInstance":
        return cls.from_dict(json.loads(s))


# ═══════════════════════════════════════════════════════════════════════
#  §2  GradedVerdict — κ-confidence with intervals + provenance
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class GradedVerdict:
    """Graded verification verdict.

    κ = h0 / (h0 + h1 + unknown) with Wilson-score 95% CI.
    """

    h0: int = 0
    h1: int = 0
    unknown: int = 0
    obstructions: List[Tuple[Tuple[str, ...], str]] = field(default_factory=list)
    provenance: List[str] = field(default_factory=list)
    elapsed_ms: float = 0.0

    @property
    def total(self) -> int:
        return self.h0 + self.h1 + self.unknown

    @property
    def confidence(self) -> float:
        t = self.total
        return self.h0 / t if t > 0 else 0.0

    @property
    def confidence_interval(self) -> Tuple[float, float]:
        """Wilson score 95% confidence interval for the true pass rate."""
        n = self.total
        if n == 0:
            return (0.0, 0.0)
        p_hat = self.h0 / n
        z = 1.96
        denom = 1 + z * z / n
        centre = (p_hat + z * z / (2 * n)) / denom
        spread = z * math.sqrt((p_hat * (1 - p_hat) + z * z / (4 * n)) / n) / denom
        lo = max(0.0, centre - spread)
        hi = min(1.0, centre + spread)
        return (lo, hi)

    @property
    def is_verified(self) -> bool:
        return self.h1 == 0 and self.unknown == 0 and self.h0 > 0

    @property
    def has_bugs(self) -> bool:
        return self.h1 > 0

    def merge(self, other: "GradedVerdict") -> "GradedVerdict":
        return GradedVerdict(
            h0=self.h0 + other.h0,
            h1=self.h1 + other.h1,
            unknown=self.unknown + other.unknown,
            obstructions=self.obstructions + other.obstructions,
            provenance=self.provenance + other.provenance,
            elapsed_ms=self.elapsed_ms + other.elapsed_ms,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "h0": self.h0,
            "h1": self.h1,
            "unknown": self.unknown,
            "confidence": round(self.confidence, 6),
            "confidence_interval": [round(v, 6) for v in self.confidence_interval],
            "is_verified": self.is_verified,
            "has_bugs": self.has_bugs,
            "obstructions": [(list(f), cx) for f, cx in self.obstructions],
            "provenance": self.provenance,
            "elapsed_ms": round(self.elapsed_ms, 2),
        }

    def to_json(self) -> str:
        return json.dumps(self.to_dict(), indent=2)


# ═══════════════════════════════════════════════════════════════════════
#  §3  Strategy enum + pipeline builder
# ═══════════════════════════════════════════════════════════════════════

class Strategy(Enum):
    """Pipeline strategy label (S0–S4 from the monograph)."""
    S0_CLOSED_TERM = "closed-term evaluation"
    S1_DENOTATIONAL = "denotational OTerm equivalence"
    S2_STRUCTURAL = "Z3 structural equality"
    S3_FINGERPRINT = "semantic fingerprint matching"
    S4_CECH = "per-fiber Z3 + Čech H¹"


@dataclass
class EnrichedResult:
    """Result with strategy provenance and graded verdict."""

    equivalent: Optional[bool]
    explanation: str
    strategy: Strategy = Strategy.S4_CECH
    verdict: GradedVerdict = field(default_factory=GradedVerdict)

    @property
    def confidence(self) -> float:
        return self.verdict.confidence

    @classmethod
    def from_result(cls, r: Result, strategy: Strategy) -> "EnrichedResult":
        verdict = GradedVerdict(
            h0=r.h0,
            h1=r.h1,
            provenance=[strategy.value],
        )
        return cls(
            equivalent=r.equivalent,
            explanation=r.explanation,
            strategy=strategy,
            verdict=verdict,
        )


StrategyFn = Callable[[VerificationInstance, int], Optional[EnrichedResult]]


def _make_strategy_fn(strategy: Strategy) -> StrategyFn:
    """Return a callable that runs a single strategy stage."""

    def _run(inst: VerificationInstance, timeout_ms: int) -> Optional[EnrichedResult]:
        r = check_equivalence(inst.subject_source, inst.target_source, timeout_ms)
        if r.equivalent is not None:
            return EnrichedResult.from_result(r, strategy)
        return None

    return _run


class StrategyPipeline:
    """Compose strategy stages with short-circuit semantics.

    Usage::

        pipe = (StrategyPipeline()
                .add(Strategy.S0_CLOSED_TERM)
                .add(Strategy.S1_DENOTATIONAL)
                .add(Strategy.S4_CECH))
        result = pipe.run(instance)
    """

    def __init__(self) -> None:
        self._stages: List[Tuple[Strategy, StrategyFn]] = []

    def add(
        self,
        strategy: Strategy,
        fn: Optional[StrategyFn] = None,
    ) -> "StrategyPipeline":
        self._stages.append((strategy, fn or _make_strategy_fn(strategy)))
        return self

    def run(
        self,
        instance: VerificationInstance,
        timeout_ms: int = 5000,
    ) -> EnrichedResult:
        remaining_ms = timeout_ms
        for strategy, fn in self._stages:
            t0 = time.monotonic()
            result = fn(instance, remaining_ms)
            elapsed = (time.monotonic() - t0) * 1000
            remaining_ms = max(100, remaining_ms - int(elapsed))
            if result is not None:
                result.verdict.elapsed_ms = elapsed
                return result
        return EnrichedResult(
            equivalent=None,
            explanation="all strategies inconclusive",
            strategy=Strategy.S4_CECH,
            verdict=GradedVerdict(elapsed_ms=timeout_ms - remaining_ms),
        )

    @classmethod
    def default(cls) -> "StrategyPipeline":
        """The standard S0→S1→S4 pipeline matching ``checker._check``."""
        return (
            cls()
            .add(Strategy.S0_CLOSED_TERM)
            .add(Strategy.S1_DENOTATIONAL)
            .add(Strategy.S4_CECH)
        )


# ═══════════════════════════════════════════════════════════════════════
#  §4  Unified verify() dispatcher
# ═══════════════════════════════════════════════════════════════════════

def verify(
    instance: VerificationInstance,
    timeout_ms: int = 5000,
    pipeline: Optional[StrategyPipeline] = None,
) -> EnrichedResult:
    """Universal verification entry point (Theorem universal-reduction).

    All three modes invoke the same cohomological pipeline; they
    differ only in how the result is reported.
    """
    pipe = pipeline or StrategyPipeline.default()
    result = pipe.run(instance, timeout_ms)

    if instance.mode == "bug" and result.equivalent is False:
        result.explanation = f"BUG: {result.explanation}"
    elif instance.mode == "spec":
        if result.equivalent is True:
            result.explanation = f"SPEC SATISFIED: {result.explanation}"
        elif result.equivalent is False:
            result.explanation = f"SPEC VIOLATION: {result.explanation}"

    return result


# ═══════════════════════════════════════════════════════════════════════
#  §5  H¹ bug localisation — identify fiber, construct witness
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class BugWitness:
    """Concrete witness for an H¹ ≠ 0 obstruction."""

    fiber: Tuple[str, ...]
    counterexample: str
    explanation: str
    concrete: bool = False


def validate_h1_bug_theorem(verdict: GradedVerdict) -> bool:
    """Check the invariant from Theorem h1-bug.

    h1 > 0 ⟹ at least one obstruction; h1 == 0 ⟹ no obstructions.
    """
    if verdict.h1 > 0:
        if not verdict.obstructions:
            return False
        return all(len(fiber) > 0 for fiber, _ in verdict.obstructions)
    return len(verdict.obstructions) == 0


def localize_bugs(verdict: GradedVerdict) -> List[BugWitness]:
    """Given H¹ ≠ 0, extract structured ``BugWitness`` objects."""
    witnesses: List[BugWitness] = []
    for fiber, cx in verdict.obstructions:
        witnesses.append(
            BugWitness(
                fiber=fiber,
                counterexample=cx,
                explanation=f"obstruction on fiber {fiber}: {cx}",
                concrete=bool(cx and "EXC:" not in cx),
            )
        )
    return witnesses


def construct_witness_test(
    witness: BugWitness,
    subject_name: str = "f",
    target_name: str = "g",
) -> str:
    """Generate a pytest test case from a ``BugWitness``."""
    args = witness.counterexample
    return (
        f"def test_bug_fiber_{'_'.join(witness.fiber)}():\n"
        f"    # Auto-generated from H¹ obstruction on fiber {witness.fiber}\n"
        f"    # Counterexample args: {args}\n"
        f"    assert {subject_name}({args}) == {target_name}({args}), "
        f"'H1 obstruction witness'\n"
    )


# ═══════════════════════════════════════════════════════════════════════
#  §6  Bayesian confidence scoring
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class BayesianConfidence:
    """Bayesian updating of the equivalence probability.

    Uses a Beta(α, β) prior.  Each passing fiber increments α;
    each failing fiber increments β.
    """

    alpha: float = 1.0
    beta: float = 1.0
    history: List[Tuple[Tuple[str, ...], bool]] = field(default_factory=list)

    @property
    def mean(self) -> float:
        return self.alpha / (self.alpha + self.beta)

    @property
    def variance(self) -> float:
        ab = self.alpha + self.beta
        return (self.alpha * self.beta) / (ab * ab * (ab + 1))

    @property
    def interval_95(self) -> Tuple[float, float]:
        """Approximate 95% credible interval (Normal approx)."""
        sd = math.sqrt(self.variance)
        lo = max(0.0, self.mean - 1.96 * sd)
        hi = min(1.0, self.mean + 1.96 * sd)
        return (lo, hi)

    def update(self, fiber: Tuple[str, ...], passed: bool) -> None:
        self.history.append((fiber, passed))
        if passed:
            self.alpha += 1
        else:
            self.beta += 1

    def update_batch(self, results: List[Tuple[Tuple[str, ...], bool]]) -> None:
        for fiber, passed in results:
            self.update(fiber, passed)

    def update_from_verdict(self, verdict: GradedVerdict) -> None:
        for _ in range(verdict.h0):
            self.alpha += 1
        for _ in range(verdict.h1):
            self.beta += 1

    def reset(self, alpha: float = 1.0, beta: float = 1.0) -> None:
        self.alpha = alpha
        self.beta = beta
        self.history.clear()

    def to_dict(self) -> Dict[str, Any]:
        return {
            "alpha": self.alpha,
            "beta": self.beta,
            "mean": round(self.mean, 6),
            "variance": round(self.variance, 8),
            "interval_95": [round(v, 6) for v in self.interval_95],
            "n_observations": len(self.history),
        }


# ═══════════════════════════════════════════════════════════════════════
#  §7  Confidence monotonicity check
# ═══════════════════════════════════════════════════════════════════════

def check_confidence_monotonicity(
    base: GradedVerdict,
    refined: GradedVerdict,
    new_fibers_all_pass: bool,
) -> bool:
    """Verify Proposition confidence-monotonicity.

    If ``refined ⊇ base`` and every new fiber passes, then
    ``refined.confidence ≥ base.confidence``.
    """
    if new_fibers_all_pass:
        return refined.confidence >= base.confidence - 1e-12
    return True


# ═══════════════════════════════════════════════════════════════════════
#  §8  Pipeline profiler
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class StageProfile:
    """Timing data for one pipeline stage."""
    strategy: Strategy
    elapsed_ms: float
    conclusive: bool
    result_equivalent: Optional[bool] = None


@dataclass
class PipelineProfile:
    """Aggregated profiling data for a full pipeline run."""
    stages: List[StageProfile] = field(default_factory=list)
    total_ms: float = 0.0

    @property
    def bottleneck(self) -> Optional[StageProfile]:
        if not self.stages:
            return None
        return max(self.stages, key=lambda s: s.elapsed_ms)

    @property
    def conclusive_stage(self) -> Optional[StageProfile]:
        for s in self.stages:
            if s.conclusive:
                return s
        return None

    def summary(self) -> str:
        parts = [f"{s.strategy.name}={s.elapsed_ms:.1f}ms" for s in self.stages]
        return f"total={self.total_ms:.1f}ms [{', '.join(parts)}]"


class PipelineProfiler:
    """Instrument a ``StrategyPipeline`` to collect timing data.

    Usage::

        profiler = PipelineProfiler()
        result = profiler.run(instance)
        print(profiler.profile.summary())
    """

    def __init__(self, pipeline: Optional[StrategyPipeline] = None) -> None:
        self._pipeline = pipeline or StrategyPipeline.default()
        self.profile = PipelineProfile()

    def run(
        self,
        instance: VerificationInstance,
        timeout_ms: int = 5000,
    ) -> EnrichedResult:
        self.profile = PipelineProfile()
        remaining = timeout_ms
        last_result: Optional[EnrichedResult] = None

        for strategy, fn in self._pipeline._stages:
            t0 = time.monotonic()
            result = fn(instance, remaining)
            elapsed = (time.monotonic() - t0) * 1000
            remaining = max(100, remaining - int(elapsed))

            conclusive = result is not None
            sp = StageProfile(
                strategy=strategy,
                elapsed_ms=elapsed,
                conclusive=conclusive,
                result_equivalent=result.equivalent if result else None,
            )
            self.profile.stages.append(sp)

            if conclusive:
                last_result = result
                last_result.verdict.elapsed_ms = elapsed
                break

        self.profile.total_ms = timeout_ms - remaining
        if last_result is not None:
            return last_result
        return EnrichedResult(
            equivalent=None,
            explanation="all strategies inconclusive",
            verdict=GradedVerdict(elapsed_ms=self.profile.total_ms),
        )


# ═══════════════════════════════════════════════════════════════════════
#  §9  Verification result cache
# ═══════════════════════════════════════════════════════════════════════

class VerificationCache:
    """LRU cache of verification results keyed by source hashes."""

    def __init__(self, max_size: int = 256) -> None:
        self._max_size = max_size
        self._store: OrderedDict[str, EnrichedResult] = OrderedDict()
        self.hits: int = 0
        self.misses: int = 0

    def _key(self, instance: VerificationInstance) -> str:
        return instance.source_hash

    def get(self, instance: VerificationInstance) -> Optional[EnrichedResult]:
        key = self._key(instance)
        if key in self._store:
            self.hits += 1
            self._store.move_to_end(key)
            return self._store[key]
        self.misses += 1
        return None

    def put(self, instance: VerificationInstance, result: EnrichedResult) -> None:
        key = self._key(instance)
        self._store[key] = result
        self._store.move_to_end(key)
        while len(self._store) > self._max_size:
            self._store.popitem(last=False)

    def invalidate(self, instance: VerificationInstance) -> bool:
        key = self._key(instance)
        if key in self._store:
            del self._store[key]
            return True
        return False

    def clear(self) -> None:
        self._store.clear()
        self.hits = 0
        self.misses = 0

    @property
    def size(self) -> int:
        return len(self._store)

    @property
    def hit_rate(self) -> float:
        total = self.hits + self.misses
        return self.hits / total if total > 0 else 0.0

    def stats(self) -> Dict[str, Any]:
        return {
            "size": self.size,
            "max_size": self._max_size,
            "hits": self.hits,
            "misses": self.misses,
            "hit_rate": round(self.hit_rate, 4),
        }


def cached_verify(
    instance: VerificationInstance,
    cache: VerificationCache,
    timeout_ms: int = 5000,
    pipeline: Optional[StrategyPipeline] = None,
) -> EnrichedResult:
    """Verify with cache lookup / population."""
    hit = cache.get(instance)
    if hit is not None:
        return hit
    result = verify(instance, timeout_ms=timeout_ms, pipeline=pipeline)
    cache.put(instance, result)
    return result


# ═══════════════════════════════════════════════════════════════════════
# §10  Batch verification runner
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class BatchResult:
    """Aggregated result of verifying many instances."""
    results: List[Tuple[VerificationInstance, EnrichedResult]] = field(default_factory=list)

    @property
    def total(self) -> int:
        return len(self.results)

    @property
    def passed(self) -> int:
        return sum(1 for _, r in self.results if r.equivalent is True)

    @property
    def failed(self) -> int:
        return sum(1 for _, r in self.results if r.equivalent is False)

    @property
    def inconclusive(self) -> int:
        return sum(1 for _, r in self.results if r.equivalent is None)

    @property
    def pass_rate(self) -> float:
        return self.passed / self.total if self.total > 0 else 0.0

    def summary(self) -> str:
        return (
            f"batch: {self.total} instances — "
            f"{self.passed} passed, {self.failed} failed, "
            f"{self.inconclusive} inconclusive "
            f"(pass rate {self.pass_rate:.1%})"
        )

    def failures(self) -> List[Tuple[VerificationInstance, EnrichedResult]]:
        return [(i, r) for i, r in self.results if r.equivalent is False]


class BatchRunner:
    """Run verification across many instances, optionally in parallel.

    Parameters
    ----------
    max_workers : int
        Thread pool size for parallel fiber checking.
    cache : VerificationCache, optional
        Shared cache across instances.
    pipeline : StrategyPipeline, optional
        Custom pipeline; defaults to ``StrategyPipeline.default()``.
    """

    def __init__(
        self,
        max_workers: int = 1,
        cache: Optional[VerificationCache] = None,
        pipeline: Optional[StrategyPipeline] = None,
    ) -> None:
        self.max_workers = max(1, max_workers)
        self.cache = cache
        self.pipeline = pipeline

    def _run_one(
        self,
        instance: VerificationInstance,
        timeout_ms: int,
    ) -> EnrichedResult:
        if self.cache is not None:
            return cached_verify(instance, self.cache, timeout_ms, self.pipeline)
        return verify(instance, timeout_ms, self.pipeline)

    def run(
        self,
        instances: Sequence[VerificationInstance],
        timeout_ms: int = 5000,
    ) -> BatchResult:
        batch = BatchResult()

        if self.max_workers <= 1:
            for inst in instances:
                r = self._run_one(inst, timeout_ms)
                batch.results.append((inst, r))
        else:
            with ThreadPoolExecutor(max_workers=self.max_workers) as pool:
                futures = {
                    pool.submit(self._run_one, inst, timeout_ms): inst
                    for inst in instances
                }
                for fut in as_completed(futures):
                    inst = futures[fut]
                    try:
                        r = fut.result()
                    except Exception as exc:
                        r = EnrichedResult(
                            equivalent=None,
                            explanation=f"worker error: {exc}",
                        )
                    batch.results.append((inst, r))

        return batch


# ═══════════════════════════════════════════════════════════════════════
# §11  Regression detector
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class RegressionEntry:
    """Comparison of one instance across two code versions."""
    instance: VerificationInstance
    old_result: EnrichedResult
    new_result: EnrichedResult

    @property
    def regressed(self) -> bool:
        return self.old_result.equivalent is True and self.new_result.equivalent is not True

    @property
    def fixed(self) -> bool:
        return self.old_result.equivalent is False and self.new_result.equivalent is True

    @property
    def unchanged(self) -> bool:
        return self.old_result.equivalent == self.new_result.equivalent

    @property
    def confidence_delta(self) -> float:
        return self.new_result.confidence - self.old_result.confidence


@dataclass
class RegressionReport:
    """Aggregate regression report."""
    entries: List[RegressionEntry] = field(default_factory=list)

    @property
    def regressions(self) -> List[RegressionEntry]:
        return [e for e in self.entries if e.regressed]

    @property
    def fixes(self) -> List[RegressionEntry]:
        return [e for e in self.entries if e.fixed]

    @property
    def unchanged_count(self) -> int:
        return sum(1 for e in self.entries if e.unchanged)

    @property
    def has_regressions(self) -> bool:
        return len(self.regressions) > 0

    def summary(self) -> str:
        return (
            f"regression report: {len(self.entries)} instances — "
            f"{len(self.regressions)} regressions, "
            f"{len(self.fixes)} fixes, "
            f"{self.unchanged_count} unchanged"
        )


class RegressionDetector:
    """Compare verification results across two code versions."""

    def compare(
        self,
        old_batch: BatchResult,
        new_batch: BatchResult,
    ) -> RegressionReport:
        old_by_hash: Dict[str, Tuple[VerificationInstance, EnrichedResult]] = {}
        for inst, res in old_batch.results:
            old_by_hash[inst.source_hash] = (inst, res)

        report = RegressionReport()
        for inst, new_res in new_batch.results:
            h = inst.source_hash
            if h in old_by_hash:
                _, old_res = old_by_hash[h]
                report.entries.append(RegressionEntry(inst, old_res, new_res))
        return report

    def compare_single(
        self,
        instance: VerificationInstance,
        old_result: EnrichedResult,
        new_result: EnrichedResult,
    ) -> RegressionEntry:
        return RegressionEntry(instance, old_result, new_result)


# ═══════════════════════════════════════════════════════════════════════
# §12  Helpers
# ═══════════════════════════════════════════════════════════════════════

def verdict_from_cech(cech: CechResult) -> GradedVerdict:
    """Lift a ``CechResult`` into a ``GradedVerdict``."""
    obstructions: List[Tuple[Tuple[str, ...], str]] = []
    for obs in cech.obstructions:
        if isinstance(obs, tuple):
            obstructions.append((obs, ""))
        else:
            obstructions.append(((str(obs),), ""))
    return GradedVerdict(
        h0=cech.h0,
        h1=cech.h1_rank,
        unknown=cech.unknown_fibers,
        obstructions=obstructions,
    )


def verdict_from_result(r: Result) -> GradedVerdict:
    """Lift a plain ``Result`` into a ``GradedVerdict``."""
    h1 = r.h1 if hasattr(r, "h1") else (1 if r.equivalent is False else 0)
    h0 = r.h0 if hasattr(r, "h0") else (1 if r.equivalent is True else 0)
    obstructions: List[Tuple[Tuple[str, ...], str]] = []
    if r.equivalent is False:
        obstructions.append((("unknown",), r.explanation))
    return GradedVerdict(h0=h0, h1=h1, obstructions=obstructions)


# ═══════════════════════════════════════════════════════════════════════
#  Self-tests
# ═══════════════════════════════════════════════════════════════════════

def _run_self_tests() -> int:
    """Run all self-tests.  Returns 0 on success, 1 on failure."""

    _counters = {"passed": 0, "failed": 0}
    _errors: List[str] = []

    def _assert(cond: bool, label: str) -> None:
        if cond:
            _counters["passed"] += 1
        else:
            _counters["failed"] += 1
            _errors.append(label)
            print(f"  FAIL: {label}")

    # --- §1 VerificationInstance ---
    print("=== §1 VerificationInstance ===")

    inst = VerificationInstance(
        subject_source="def f(x): return x+1",
        target_source="def g(x): return 1+x",
        mode="equivalence",
        cover=[("int",)],
        metadata={"author": "test"},
    )
    _assert(inst.mode == "equivalence", "mode default")
    _assert(inst.cover == [("int",)], "cover round-trip tuple")

    j = inst.to_json()
    inst2 = VerificationInstance.from_json(j)
    _assert(inst2.subject_source == inst.subject_source, "json subject round-trip")
    _assert(inst2.target_source == inst.target_source, "json target round-trip")
    _assert(inst2.cover == inst.cover, "json cover round-trip")
    _assert(inst2.mode == inst.mode, "json mode round-trip")
    _assert(inst2.metadata == inst.metadata, "json metadata round-trip")

    d = inst.to_dict()
    inst3 = VerificationInstance.from_dict(d)
    _assert(inst3.source_hash == inst.source_hash, "dict hash round-trip")

    try:
        VerificationInstance("a", "b", mode="invalid")
        _assert(False, "invalid mode should raise")
    except ValueError:
        _assert(True, "invalid mode raises ValueError")

    try:
        VerificationInstance("a", "b", cover=["not_a_tuple"])  # type: ignore
        _assert(False, "invalid cover should raise")
    except TypeError:
        _assert(True, "invalid cover raises TypeError")

    # --- §2 GradedVerdict ---
    print("=== §2 GradedVerdict ===")

    v0 = GradedVerdict()
    _assert(v0.confidence == 0.0, "empty confidence is 0")
    _assert(not v0.is_verified, "empty not verified")
    _assert(not v0.has_bugs, "empty no bugs")
    _assert(v0.total == 0, "empty total 0")

    v1 = GradedVerdict(h0=5, h1=0, unknown=0)
    _assert(v1.confidence == 1.0, "all-pass confidence 1.0")
    _assert(v1.is_verified, "all-pass is_verified")
    _assert(not v1.has_bugs, "all-pass no bugs")

    v2 = GradedVerdict(h0=3, h1=1, unknown=1, obstructions=[(("int",), "x=0")])
    _assert(abs(v2.confidence - 0.6) < 1e-9, "3/5 confidence")
    _assert(v2.has_bugs, "h1>0 has_bugs")
    _assert(not v2.is_verified, "h1>0 not verified")
    lo, hi = v2.confidence_interval
    _assert(lo < v2.confidence < hi or v2.total < 3, "CI contains point est")

    v_merged = v1.merge(v2)
    _assert(v_merged.h0 == 8, "merge h0")
    _assert(v_merged.h1 == 1, "merge h1")
    _assert(v_merged.unknown == 1, "merge unknown")
    _assert(len(v_merged.obstructions) == 1, "merge obstructions")

    vj = v2.to_json()
    vd = json.loads(vj)
    _assert(vd["h0"] == 3, "verdict json h0")
    _assert(vd["has_bugs"] is True, "verdict json has_bugs")

    # --- §3 Strategy & EnrichedResult ---
    print("=== §3 Strategy & EnrichedResult ===")

    _assert(Strategy.S0_CLOSED_TERM.value == "closed-term evaluation", "S0 label")
    _assert(Strategy.S4_CECH.value == "per-fiber Z3 + Čech H¹", "S4 label")

    r_plain = Result(equivalent=True, explanation="ok", h0=3, h1=0, confidence=1.0)
    er = EnrichedResult.from_result(r_plain, Strategy.S1_DENOTATIONAL)
    _assert(er.equivalent is True, "enriched equiv")
    _assert(er.strategy == Strategy.S1_DENOTATIONAL, "enriched strategy")
    _assert(er.verdict.h0 == 3, "enriched verdict h0")

    # --- §4 Pipeline builder ---
    print("=== §4 Pipeline builder ===")

    pipe = StrategyPipeline.default()
    _assert(len(pipe._stages) == 3, "default pipeline has 3 stages")

    custom_pipe = StrategyPipeline().add(Strategy.S0_CLOSED_TERM).add(Strategy.S4_CECH)
    _assert(len(custom_pipe._stages) == 2, "custom pipeline has 2 stages")

    # --- §5 H¹ bug localisation ---
    print("=== §5 H¹ bug localisation ===")

    v_bugs = GradedVerdict(h0=2, h1=1, obstructions=[(("int",), "x=42")])
    _assert(validate_h1_bug_theorem(v_bugs), "h1>0 with obstruction valid")

    v_bad = GradedVerdict(h0=2, h1=1, obstructions=[])
    _assert(not validate_h1_bug_theorem(v_bad), "h1>0 without obstruction invalid")

    v_clean = GradedVerdict(h0=5, h1=0, obstructions=[])
    _assert(validate_h1_bug_theorem(v_clean), "h1=0 no obstructions valid")

    v_phantom = GradedVerdict(h0=5, h1=0, obstructions=[(("int",), "x=1")])
    _assert(not validate_h1_bug_theorem(v_phantom), "h1=0 with obstruction invalid")

    witnesses = localize_bugs(v_bugs)
    _assert(len(witnesses) == 1, "one witness")
    _assert(witnesses[0].fiber == ("int",), "witness fiber")
    _assert(witnesses[0].counterexample == "x=42", "witness cx")

    test_src = construct_witness_test(witnesses[0])
    _assert("test_bug_fiber_int" in test_src, "generated test name")
    _assert("x=42" in test_src, "generated test args")

    # --- §6 Bayesian confidence ---
    print("=== §6 Bayesian confidence ===")

    bc = BayesianConfidence()
    _assert(abs(bc.mean - 0.5) < 1e-9, "uninformative prior mean 0.5")

    bc.update(("int",), True)
    bc.update(("int",), True)
    bc.update(("str",), False)
    _assert(bc.alpha == 3.0, "alpha after 2 pass")
    _assert(bc.beta == 2.0, "beta after 1 fail")
    _assert(abs(bc.mean - 0.6) < 1e-9, "posterior mean 3/5")
    lo, hi = bc.interval_95
    _assert(lo < bc.mean < hi, "credible interval contains mean")

    bc2 = BayesianConfidence()
    bc2.update_from_verdict(v2)
    _assert(bc2.alpha == 4.0, "alpha from verdict h0=3 + prior 1")
    _assert(bc2.beta == 2.0, "beta from verdict h1=1 + prior 1")

    bc_dict = bc.to_dict()
    _assert(bc_dict["alpha"] == 3.0, "dict alpha")
    _assert(bc_dict["n_observations"] == 3, "dict n_obs")

    bc.reset()
    _assert(bc.alpha == 1.0, "reset alpha")
    _assert(len(bc.history) == 0, "reset history")

    # --- §7 Confidence monotonicity ---
    print("=== §7 Confidence monotonicity ===")

    base = GradedVerdict(h0=3, h1=0, unknown=2)
    refined = GradedVerdict(h0=5, h1=0, unknown=2)
    _assert(check_confidence_monotonicity(base, refined, True), "more passing → higher κ")

    refined_bad = GradedVerdict(h0=3, h1=1, unknown=2)
    _assert(check_confidence_monotonicity(base, refined_bad, False), "non-passing new fibers → vacuously true")

    # --- §8 Pipeline profiler ---
    print("=== §8 Pipeline profiler ===")

    profiler = PipelineProfiler()
    _assert(profiler.profile.total_ms == 0.0, "profiler starts empty")
    _assert(profiler.profile.bottleneck is None, "no bottleneck when empty")
    _assert(profiler.profile.conclusive_stage is None, "no conclusive stage when empty")

    sp1 = StageProfile(Strategy.S0_CLOSED_TERM, 10.0, False)
    sp2 = StageProfile(Strategy.S4_CECH, 50.0, True, True)
    profile = PipelineProfile(stages=[sp1, sp2], total_ms=60.0)
    _assert(profile.bottleneck == sp2, "bottleneck is S4")
    _assert(profile.conclusive_stage == sp2, "conclusive is S4")
    _assert("60.0ms" in profile.summary(), "summary has total")

    # --- §9 Verification cache ---
    print("=== §9 Verification cache ===")

    cache = VerificationCache(max_size=3)
    _assert(cache.size == 0, "empty cache")
    _assert(cache.hit_rate == 0.0, "empty hit rate")

    inst_a = VerificationInstance("def f(x): return x", "def g(x): return x")
    inst_b = VerificationInstance("def f(x): return x+1", "def g(x): return x+1")
    inst_c = VerificationInstance("def f(x): return x*2", "def g(x): return x*2")
    inst_d = VerificationInstance("def f(x): return x-1", "def g(x): return x-1")

    er_a = EnrichedResult(equivalent=True, explanation="ok")
    cache.put(inst_a, er_a)
    _assert(cache.size == 1, "cache size 1")

    hit = cache.get(inst_a)
    _assert(hit is not None, "cache hit")
    _assert(hit.equivalent is True, "cache hit value")
    _assert(cache.hits == 1, "hits counter")

    miss = cache.get(inst_b)
    _assert(miss is None, "cache miss")
    _assert(cache.misses == 1, "misses counter")
    _assert(abs(cache.hit_rate - 0.5) < 1e-9, "50% hit rate")

    cache.put(inst_b, EnrichedResult(True, "b"))
    cache.put(inst_c, EnrichedResult(True, "c"))
    cache.put(inst_d, EnrichedResult(True, "d"))
    _assert(cache.size == 3, "LRU capped at 3")
    _assert(cache.get(inst_a) is None, "oldest evicted")

    _assert(cache.invalidate(inst_b), "invalidate returns True")
    _assert(cache.size == 2, "size after invalidate")
    _assert(not cache.invalidate(inst_b), "re-invalidate returns False")

    cache.clear()
    _assert(cache.size == 0, "clear empties cache")
    _assert(cache.hits == 0, "clear resets hits")

    # --- §10 Batch runner ---
    print("=== §10 Batch runner ===")

    batch_instances = [
        VerificationInstance("def f(x): return x", "def g(x): return x"),
        VerificationInstance("def f(x): return x+1", "def g(x): return x+2"),
    ]

    runner = BatchRunner(max_workers=1)
    batch_res = runner.run(batch_instances, timeout_ms=100)
    _assert(batch_res.total == 2, "batch total")
    _assert(batch_res.passed + batch_res.failed + batch_res.inconclusive == 2, "batch partition")
    _assert(len(batch_res.summary()) > 0, "batch summary non-empty")

    # --- §11 Regression detector ---
    print("=== §11 Regression detector ===")

    old_r1 = EnrichedResult(equivalent=True, explanation="ok")
    old_r2 = EnrichedResult(equivalent=False, explanation="bug")
    new_r1 = EnrichedResult(equivalent=False, explanation="now fails")
    new_r2 = EnrichedResult(equivalent=True, explanation="fixed")

    i1 = VerificationInstance("def f(x): return x", "def g(x): return x")
    i2 = VerificationInstance("def f(x): return x+1", "def g(x): return x+2")

    old_batch = BatchResult(results=[(i1, old_r1), (i2, old_r2)])
    new_batch = BatchResult(results=[(i1, new_r1), (i2, new_r2)])

    det = RegressionDetector()
    report = det.compare(old_batch, new_batch)
    _assert(len(report.entries) == 2, "two entries")
    _assert(len(report.regressions) == 1, "one regression")
    _assert(len(report.fixes) == 1, "one fix")
    _assert(report.has_regressions, "has_regressions flag")
    _assert(len(report.summary()) > 0, "regression summary non-empty")

    entry = det.compare_single(i1, old_r1, new_r1)
    _assert(entry.regressed, "single regression detected")
    _assert(not entry.fixed, "not a fix")
    _assert(entry.confidence_delta <= 0, "confidence dropped")

    entry2 = det.compare_single(i2, old_r2, new_r2)
    _assert(entry2.fixed, "single fix detected")
    _assert(not entry2.regressed, "not a regression")

    # --- §12 Helpers ---
    print("=== §12 Helpers ===")

    cech = CechResult(h0=4, h1_rank=1, total_fibers=6, unknown_fibers=1,
                      obstructions=[("int",)])
    gv = verdict_from_cech(cech)
    _assert(gv.h0 == 4, "cech->verdict h0")
    _assert(gv.h1 == 1, "cech->verdict h1")
    _assert(gv.unknown == 1, "cech->verdict unknown")

    r = Result(equivalent=True, explanation="ok", h0=7, h1=0, confidence=1.0)
    gv2 = verdict_from_result(r)
    _assert(gv2.h0 == 7, "result->verdict h0")
    _assert(gv2.h1 == 0, "result->verdict h1")

    # --- Summary ---
    passed = _counters["passed"]
    failed = _counters["failed"]
    print()
    print(f"{'='*50}")
    print(f"  {passed} passed, {failed} failed")
    if _errors:
        print(f"  Failures: {_errors}")
    print(f"{'='*50}")
    return 1 if failed else 0


if __name__ == "__main__":
    import sys
    sys.exit(_run_self_tests())
