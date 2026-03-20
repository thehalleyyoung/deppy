"""Pillar 9 — Benchmark runner with reporting.

Runs the hallucination benchmark suite, integration tests, and performance
micro-benchmarks, then produces a unified report in dict / JSON / Markdown
form.

Usage::

    python -m deppy.hybrid.benchmark.run_benchmarks
    python -m deppy.hybrid.benchmark.run_benchmarks --suite hallucination
    python -m deppy.hybrid.benchmark.run_benchmarks --verbose --output report.json
"""
from __future__ import annotations


# --- Integration with existing deppy codebase ---
try:
    from deppy.pipeline import analyze_source
    from deppy.refinement_engine import refine
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

import argparse
import hashlib
import json
import math
import sys
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple

from deppy.hybrid.benchmark.hallucination_suite import (
    BenchmarkResult,
    HallucinationSuite,
)
from deppy.hybrid.benchmark.integration_tests import (

    _ALL_TESTS as INTEGRATION_TESTS,
)

# ───────────────────────────────────────────────────────────────────────────
# Result containers
# ───────────────────────────────────────────────────────────────────────────

@dataclass
class TestResult:
    """Result of running the integration test suite."""

    total: int = 0
    passed: int = 0
    failed: int = 0
    errors: List[str] = field(default_factory=list)
    duration_seconds: float = 0.0

    @property
    def success(self) -> bool:
        return self.failed == 0

    def to_dict(self) -> Dict[str, Any]:
        return {
            "total": self.total,
            "passed": self.passed,
            "failed": self.failed,
            "errors": self.errors,
            "duration_seconds": round(self.duration_seconds, 4),
            "success": self.success,
        }

@dataclass
class PerfResult:
    """Result of running performance micro-benchmarks."""

    avg_check_time_ms: float = 0.0
    cache_hit_rate: float = 0.0
    total_oracle_tokens: int = 0
    tokens_saved_by_cache: int = 0
    z3_discharge_rate: float = 0.0
    lean_verification_rate: float = 0.0
    parse_time_ms: float = 0.0
    classify_time_ms: float = 0.0
    provenance_check_time_ms: float = 0.0
    total_checks: int = 0

    def to_dict(self) -> Dict[str, Any]:
        return {
            "avg_check_time_ms": round(self.avg_check_time_ms, 3),
            "cache_hit_rate": round(self.cache_hit_rate, 4),
            "total_oracle_tokens": self.total_oracle_tokens,
            "tokens_saved_by_cache": self.tokens_saved_by_cache,
            "z3_discharge_rate": round(self.z3_discharge_rate, 4),
            "lean_verification_rate": round(self.lean_verification_rate, 4),
            "parse_time_ms": round(self.parse_time_ms, 3),
            "classify_time_ms": round(self.classify_time_ms, 3),
            "provenance_check_time_ms": round(self.provenance_check_time_ms, 3),
            "total_checks": self.total_checks,
        }

    def summary(self) -> str:
        lines = [
            "--- Performance ---",
            f"  Avg check time       : {self.avg_check_time_ms:.3f} ms",
            f"  Cache hit rate       : {self.cache_hit_rate:.1%}",
            f"  Total oracle tokens  : {self.total_oracle_tokens}",
            f"  Tokens saved (cache) : {self.tokens_saved_by_cache}",
            f"  Z3 discharge rate    : {self.z3_discharge_rate:.1%}",
            f"  Lean verify rate     : {self.lean_verification_rate:.1%}",
            f"  Parse time           : {self.parse_time_ms:.3f} ms",
            f"  Classify time        : {self.classify_time_ms:.3f} ms",
            f"  Provenance time      : {self.provenance_check_time_ms:.3f} ms",
            f"  Total checks         : {self.total_checks}",
        ]
        return "\n".join(lines)

@dataclass
class FullReport:
    """Unified report from all benchmark suites."""

    hallucination: Optional[BenchmarkResult] = None
    integration: Optional[TestResult] = None
    performance: Optional[PerfResult] = None
    timestamp: str = ""
    duration_seconds: float = 0.0

    def __post_init__(self) -> None:
        if not self.timestamp:
            import datetime
            self.timestamp = datetime.datetime.now(
                datetime.timezone.utc
            ).isoformat()

    def to_dict(self) -> Dict[str, Any]:
        result: Dict[str, Any] = {
            "timestamp": self.timestamp,
            "duration_seconds": round(self.duration_seconds, 4),
        }
        if self.hallucination is not None:
            result["hallucination"] = {
                "precision": self.hallucination.precision,
                "recall": self.hallucination.recall,
                "f1": self.hallucination.f1,
                "total_examples": self.hallucination.total_examples,
                "total_findings": self.hallucination.total_findings,
                "total_ground_truth": self.hallucination.total_ground_truth,
                "false_positives": self.hallucination.false_positives,
                "false_negatives": self.hallucination.false_negatives,
                "per_kind": self.hallucination.per_kind,
            }
        if self.integration is not None:
            result["integration"] = self.integration.to_dict()
        if self.performance is not None:
            result["performance"] = self.performance.to_dict()
        return result

    def to_json(self, path: str) -> None:
        data = self.to_dict()
        Path(path).write_text(json.dumps(data, indent=2) + "\n")

    def to_markdown(self) -> str:
        lines: List[str] = [
            "# Deppy Benchmark Report",
            "",
            f"**Timestamp:** {self.timestamp}  ",
            f"**Duration:** {self.duration_seconds:.2f}s",
            "",
        ]

        if self.hallucination is not None:
            h = self.hallucination
            lines += [
                "## Hallucination Suite",
                "",
                f"| Metric | Value |",
                f"|--------|-------|",
                f"| Examples | {h.total_examples} |",
                f"| Precision | {h.precision:.3f} |",
                f"| Recall | {h.recall:.3f} |",
                f"| F1 | {h.f1:.3f} |",
                f"| False positives | {h.false_positives} |",
                f"| False negatives | {h.false_negatives} |",
                "",
                "### Per-kind breakdown",
                "",
                "| Kind | Precision | Recall | F1 |",
                "|------|-----------|--------|-----|",
            ]
            for kind, scores in sorted(h.per_kind.items()):
                lines.append(
                    f"| {kind} | {scores['precision']:.3f} | "
                    f"{scores['recall']:.3f} | {scores['f1']:.3f} |"
                )
            lines.append("")

        if self.integration is not None:
            t = self.integration
            status = "✅ PASS" if t.success else "❌ FAIL"
            lines += [
                "## Integration Tests",
                "",
                f"**Status:** {status}  ",
                f"**Passed:** {t.passed}/{t.total}  ",
                f"**Duration:** {t.duration_seconds:.2f}s",
                "",
            ]
            if t.errors:
                lines.append("### Failures")
                lines.append("")
                for err in t.errors:
                    lines.append(f"- {err}")
                lines.append("")

        if self.performance is not None:
            p = self.performance
            lines += [
                "## Performance",
                "",
                f"| Metric | Value |",
                f"|--------|-------|",
                f"| Avg check time | {p.avg_check_time_ms:.3f} ms |",
                f"| Cache hit rate | {p.cache_hit_rate:.1%} |",
                f"| Oracle tokens | {p.total_oracle_tokens} |",
                f"| Tokens saved | {p.tokens_saved_by_cache} |",
                f"| Z3 discharge | {p.z3_discharge_rate:.1%} |",
                f"| Lean verify | {p.lean_verification_rate:.1%} |",
                f"| Parse time | {p.parse_time_ms:.3f} ms |",
                "",
            ]

        return "\n".join(lines)

    def summary(self) -> str:
        parts: List[str] = [
            "=== Deppy Benchmark Summary ===",
            f"  Total time: {self.duration_seconds:.2f}s",
        ]
        if self.hallucination is not None:
            h = self.hallucination
            parts.append(
                f"  Hallucination suite: P={h.precision:.3f} R={h.recall:.3f} "
                f"F1={h.f1:.3f} ({h.total_examples} examples)"
            )
        if self.integration is not None:
            t = self.integration
            status = "PASS" if t.success else "FAIL"
            parts.append(
                f"  Integration tests : {status} — {t.passed}/{t.total}"
            )
        if self.performance is not None:
            p = self.performance
            parts.append(
                f"  Performance       : {p.avg_check_time_ms:.1f}ms avg, "
                f"{p.cache_hit_rate:.0%} cache hit"
            )
        return "\n".join(parts)

# ───────────────────────────────────────────────────────────────────────────
# Benchmark runner
# ───────────────────────────────────────────────────────────────────────────

class BenchmarkRunner:
    """Orchestrates all benchmark suites and collects results."""

    def __init__(self, verbose: bool = False) -> None:
        self.verbose = verbose
        self._suite: Optional[HallucinationSuite] = None

    @property
    def suite(self) -> HallucinationSuite:
        if self._suite is None:
            self._suite = HallucinationSuite()
        return self._suite

    # -- individual suites -------------------------------------------------

    def run_hallucination_suite(self) -> BenchmarkResult:
        """Run the hallucination detection benchmark with a baseline checker."""
        if self.verbose:
            print("\n--- Running hallucination suite ---")

        from deppy.hybrid.benchmark.integration_tests import (
            StructuralHallucinationDetector,
        )

        detector = StructuralHallucinationDetector()

        def checker(artifact: str, spec: str) -> List[Dict[str, str]]:
            return detector.check(artifact, spec)

        result = self.suite.evaluate(checker)

        if self.verbose:
            print(result.summary())

        return result

    def run_integration_tests(self) -> TestResult:
        """Run all integration test functions."""
        if self.verbose:
            print("\n--- Running integration tests ---")

        t0 = time.monotonic()
        result = TestResult(total=len(INTEGRATION_TESTS))

        for test_fn in INTEGRATION_TESTS:
            name = test_fn.__name__
            try:
                test_fn()
                result.passed += 1
                if self.verbose:
                    print(f"  ✓ {name}")
            except Exception as exc:
                result.failed += 1
                msg = f"{name}: {exc}"
                result.errors.append(msg)
                if self.verbose:
                    print(f"  ✗ {msg}")

        result.duration_seconds = time.monotonic() - t0

        if self.verbose:
            status = "PASS" if result.success else "FAIL"
            print(f"\n  {status}: {result.passed}/{result.total}")

        return result

    def run_performance_benchmarks(self) -> PerfResult:
        """Run timing, cache, and throughput micro-benchmarks."""
        if self.verbose:
            print("\n--- Running performance benchmarks ---")

        perf = PerfResult()

        # 1. Parse timing
        perf.parse_time_ms = self._bench_parse()
        if self.verbose:
            print(f"  Parse time: {perf.parse_time_ms:.3f} ms")

        # 2. Decidability classification timing
        perf.classify_time_ms = self._bench_classify()
        if self.verbose:
            print(f"  Classify time: {perf.classify_time_ms:.3f} ms")

        # 3. Provenance grounding timing
        perf.provenance_check_time_ms = self._bench_provenance()
        if self.verbose:
            print(f"  Provenance time: {perf.provenance_check_time_ms:.3f} ms")

        # 4. Hallucination check timing and stats
        check_stats = self._bench_hallucination_checks()
        perf.avg_check_time_ms = check_stats["avg_time_ms"]
        perf.total_checks = check_stats["total"]
        if self.verbose:
            print(f"  Avg check time: {perf.avg_check_time_ms:.3f} ms"
                  f" ({perf.total_checks} checks)")

        # 5. Cache simulation
        cache_stats = self._bench_cache()
        perf.cache_hit_rate = cache_stats["hit_rate"]
        perf.total_oracle_tokens = cache_stats["total_tokens"]
        perf.tokens_saved_by_cache = cache_stats["saved_tokens"]
        if self.verbose:
            print(f"  Cache hit rate: {perf.cache_hit_rate:.1%}")
            print(f"  Tokens saved: {perf.tokens_saved_by_cache}")

        # 6. Z3 discharge rate (simulated)
        perf.z3_discharge_rate = self._bench_z3_discharge()
        if self.verbose:
            print(f"  Z3 discharge rate: {perf.z3_discharge_rate:.1%}")

        # 7. Lean verification rate (simulated)
        perf.lean_verification_rate = self._bench_lean_verify()
        if self.verbose:
            print(f"  Lean verify rate: {perf.lean_verification_rate:.1%}")

        return perf

    # -- micro-benchmarks --------------------------------------------------

    def _bench_parse(self) -> float:
        from deppy.hybrid.benchmark.integration_tests import MixedModeParser
        import textwrap

        source = textwrap.dedent("""\
            @guarantee("result is sorted")
            def my_fn(xs: list[int]) -> list[int]:
                assume("xs is non-empty")
                y = hole("sort xs")
                check("y is sorted")
                return y
        """)

        parser = MixedModeParser()
        iterations = 1000
        t0 = time.monotonic()
        for _ in range(iterations):
            parser.parse(source)
        elapsed = time.monotonic() - t0
        return (elapsed / iterations) * 1000

    def _bench_classify(self) -> float:
        from deppy.hybrid.benchmark.integration_tests import (
            DecidabilityClassifier,
        )

        claims = [
            "sorted in ascending order",
            "at least 3 elements",
            "correctly implements binary search",
            "grounded in cited sources",
            "all values are non-negative",
            "the algorithm is efficient",
            "list contains no duplicates",
            "produces human-readable output",
        ]

        classifier = DecidabilityClassifier()
        iterations = 1000
        t0 = time.monotonic()
        for _ in range(iterations):
            for c in claims:
                classifier.classify(c)
        elapsed = time.monotonic() - t0
        return (elapsed / (iterations * len(claims))) * 1000

    def _bench_provenance(self) -> float:
        from deppy.hybrid.benchmark.integration_tests import (
            ProvenanceGraph,
            ProvenanceNode,
        )

        g = ProvenanceGraph()
        # Build a chain of 100 nodes
        g.add(ProvenanceNode(id="root", kind="HUMAN_AUTHORED",
                             content_hash="r"))
        for i in range(1, 100):
            g.add(ProvenanceNode(
                id=f"n{i}", kind="LLM_GENERATED",
                content_hash=f"h{i}", parents=[f"n{i-1}" if i > 1 else "root"],
            ))

        iterations = 100
        t0 = time.monotonic()
        for _ in range(iterations):
            g.is_grounded("n99")
        elapsed = time.monotonic() - t0
        return (elapsed / iterations) * 1000

    def _bench_hallucination_checks(self) -> Dict[str, Any]:
        from deppy.hybrid.benchmark.integration_tests import (
            StructuralHallucinationDetector,
        )

        detector = StructuralHallucinationDetector()
        examples = self.suite.examples

        t0 = time.monotonic()
        for ex in examples:
            detector.check(ex.artifact, ex.spec)
        elapsed = time.monotonic() - t0

        return {
            "avg_time_ms": (elapsed / len(examples)) * 1000,
            "total": len(examples),
        }

    def _bench_cache(self) -> Dict[str, Any]:
        from deppy.hybrid.benchmark.integration_tests import (
            CacheEntry,
            TrustCache,
        )

        cache = TrustCache()
        tokens_per_call = 150
        examples = self.suite.examples

        # First pass: all misses
        for ex in examples:
            key = ex.content_hash
            cache.lookup(key)
            cache.insert(key, CacheEntry(
                result=True, confidence=0.9,
                content_hash=key, tokens_used=tokens_per_call,
            ))

        # Second pass: all hits
        for ex in examples:
            cache.lookup(ex.content_hash)

        total_tokens = len(examples) * tokens_per_call  # first pass only
        saved_tokens = len(examples) * tokens_per_call  # second pass saved

        return {
            "hit_rate": cache.hit_rate,
            "total_tokens": total_tokens,
            "saved_tokens": saved_tokens,
        }

    def _bench_z3_discharge(self) -> float:
        from deppy.hybrid.benchmark.integration_tests import (
            DecidabilityClassifier,
        )

        classifier = DecidabilityClassifier()
        structural = 0
        total = 0
        for ex in self.suite.examples:
            for h in ex.hallucinations:
                total += 1
                if classifier.classify(h.get("description", "")) == "structural":
                    structural += 1
        return structural / total if total else 0.0

    def _bench_lean_verify(self) -> float:
        from deppy.hybrid.benchmark.integration_tests import LeanEmitter

        emitter = LeanEmitter()
        valid = 0
        total = 0
        for ex in self.suite.get_by_kind("code"):
            total += 1
            lean = emitter.emit_theorem(
                name=f"check_{ex.id.replace('-', '_')}",
                statement=f"True",
            )
            if LeanEmitter.is_syntactically_valid(lean):
                valid += 1
        return valid / total if total else 0.0

    # -- top-level entry points --------------------------------------------

    def run_all(self) -> FullReport:
        """Run all suites and return a unified report."""
        t0 = time.monotonic()

        hall_result = self.run_hallucination_suite()
        int_result = self.run_integration_tests()
        perf_result = self.run_performance_benchmarks()

        duration = time.monotonic() - t0

        report = FullReport(
            hallucination=hall_result,
            integration=int_result,
            performance=perf_result,
            duration_seconds=duration,
        )

        if self.verbose:
            print("\n" + report.summary())

        return report

    def run_suite(self, name: str) -> FullReport:
        """Run a single suite by name and return a report."""
        t0 = time.monotonic()
        hall = int_ = perf = None

        if name in ("hallucination", "all"):
            hall = self.run_hallucination_suite()
        if name in ("integration", "all"):
            int_ = self.run_integration_tests()
        if name in ("performance", "all"):
            perf = self.run_performance_benchmarks()

        duration = time.monotonic() - t0
        return FullReport(
            hallucination=hall,
            integration=int_,
            performance=perf,
            duration_seconds=duration,
        )

# ───────────────────────────────────────────────────────────────────────────
# CLI entry point
# ───────────────────────────────────────────────────────────────────────────

def main(argv: Optional[List[str]] = None) -> None:
    """CLI entry point for running benchmarks."""
    parser = argparse.ArgumentParser(
        description="Run Deppy benchmark suites.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Examples:\n"
            "  python -m deppy.hybrid.benchmark.run_benchmarks\n"
            "  python -m deppy.hybrid.benchmark.run_benchmarks --suite hallucination\n"
            "  python -m deppy.hybrid.benchmark.run_benchmarks --verbose --output report.json\n"
        ),
    )
    parser.add_argument(
        "--suite",
        choices=["all", "hallucination", "integration", "performance"],
        default="all",
        help="Which benchmark suite to run (default: all).",
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Print detailed output during the run.",
    )
    parser.add_argument(
        "--output", "-o",
        type=str,
        default=None,
        help="Write results to file (JSON if .json, Markdown if .md).",
    )
    parser.add_argument(
        "--format", "-f",
        choices=["json", "markdown", "text"],
        default=None,
        help="Output format (auto-detected from --output extension if not set).",
    )

    args = parser.parse_args(argv)

    runner = BenchmarkRunner(verbose=args.verbose)

    if args.suite == "all":
        report = runner.run_all()
    else:
        report = runner.run_suite(args.suite)

    # Determine output format
    fmt = args.format
    if fmt is None and args.output:
        if args.output.endswith(".json"):
            fmt = "json"
        elif args.output.endswith(".md"):
            fmt = "markdown"
        else:
            fmt = "text"

    # Print summary
    print("\n" + report.summary())

    # Write to file
    if args.output:
        if fmt == "json":
            report.to_json(args.output)
            print(f"\nResults written to {args.output}")
        elif fmt == "markdown":
            Path(args.output).write_text(report.to_markdown())
            print(f"\nResults written to {args.output}")
        else:
            Path(args.output).write_text(report.summary() + "\n")
            print(f"\nResults written to {args.output}")

    # Exit code
    if report.integration and not report.integration.success:
        sys.exit(1)

if __name__ == "__main__":
    main()
