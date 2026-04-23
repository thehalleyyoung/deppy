"""
Exception Freedom Report — Result Types and Visualization
==========================================================

Structured report types for module-level exception-freedom verification.
Each function gets a per-source breakdown with safety classification,
and the module gets an aggregate summary with statistics.

Safety classifications (from most to least trusted):
  PROVED_SAFE         — guard + Z3 proves exception impossible
  SAFE_BY_PATTERN     — recognized safe pattern (e.g., dict.get)
  SAFE_UNDER_PRECOND  — safe if preconditions hold (trust degraded)
  CAUGHT              — exception caught by try/except
  PARTIALLY_GUARDED   — some paths guarded, not all
  UNGUARDED           — no guard found
  UNRESOLVABLE        — analysis cannot determine

Architecture
------------
  SafetyClassification  — per-source result
  FunctionExceptionReport — per-function aggregate
  ModuleExceptionFreedomReport — per-module aggregate with stats
  ReportFormatter       — text / markdown / JSON rendering
"""
from __future__ import annotations

import json
import time
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Sequence

from deppy.pipeline.exception_sources import (
    ExceptionKind, ExceptionSource, Severity,
    FunctionSourceSummary, ModuleSourceSummary,
)
from deppy.pipeline.exception_guards import (
    SafetyLevel, GuardedSource, FunctionGuardAnalysis,
    ModuleGuardAnalysis, GuardKind,
)


# ═══════════════════════════════════════════════════════════════════
# 1.  Result Classifications
# ═══════════════════════════════════════════════════════════════════

class VerificationMethod(Enum):
    """How was safety determined?"""
    GUARD_ANALYSIS     = auto()   # control-flow guard inference
    Z3_PROOF           = auto()   # Z3 solver proved safe
    ABSTRACT_INTERP    = auto()   # abstract interpretation resolved
    EFFECT_ANALYSIS    = auto()   # deppy effect system
    SIDECAR_SUMMARY    = auto()   # sidecar/axiom assumption
    EMPIRICAL_TEST     = auto()   # testing (diagnostic only, NOT proof)
    PATTERN_MATCH      = auto()   # safe API pattern recognized
    TRY_EXCEPT         = auto()   # caught by exception handler
    NOT_ATTEMPTED      = auto()   # analysis skipped


@dataclass
class SafetyClassification:
    """Final safety verdict for one exception source."""
    source: ExceptionSource
    safety: SafetyLevel
    method: VerificationMethod = VerificationMethod.NOT_ATTEMPTED
    condition: str = ""         # condition under which safe
    z3_time_ms: float = 0.0    # Z3 solving time if applicable
    proof_term: str = ""        # deppy proof term reference
    confidence: float = 1.0     # 1.0 = machine-checked, 0.5 = heuristic

    @property
    def is_safe(self) -> bool:
        return self.safety in (SafetyLevel.PROVED_SAFE,
                               SafetyLevel.SAFE_BY_PATTERN,
                               SafetyLevel.CAUGHT)

    @property
    def is_conditionally_safe(self) -> bool:
        return self.safety == SafetyLevel.SAFE_UNDER_PRECOND

    def __repr__(self) -> str:
        sym = "✓" if self.is_safe else ("~" if self.is_conditionally_safe else "✗")
        return (f"{sym} {self.source.kind.name} @ L{self.source.location.lineno}: "
                f"{self.safety.name} ({self.method.name})")


# ═══════════════════════════════════════════════════════════════════
# 2.  Function-Level Report
# ═══════════════════════════════════════════════════════════════════

class FunctionVerdict(Enum):
    """Overall verdict for a function."""
    EXCEPTION_FREE      = auto()  # all sources proved safe
    CONDITIONALLY_SAFE  = auto()  # safe under stated preconditions
    PARTIALLY_VERIFIED  = auto()  # some sources unresolved
    UNSAFE              = auto()  # known unguarded exception sources
    TRIVIALLY_SAFE      = auto()  # no exception sources at all
    SKIPPED             = auto()  # analysis skipped


@dataclass
class FunctionExceptionReport:
    """Exception-freedom report for a single function."""
    name: str
    verdict: FunctionVerdict = FunctionVerdict.SKIPPED
    classifications: list[SafetyClassification] = field(default_factory=list)
    preconditions_assumed: list[str] = field(default_factory=list)
    duration_ms: float = 0.0
    class_name: str | None = None
    is_method: bool = False
    lineno: int = 0

    @property
    def qualified_name(self) -> str:
        if self.class_name:
            return f"{self.class_name}.{self.name}"
        return self.name

    @property
    def total_sources(self) -> int:
        return len(self.classifications)

    @property
    def safe_count(self) -> int:
        return sum(1 for c in self.classifications if c.is_safe)

    @property
    def conditional_count(self) -> int:
        return sum(1 for c in self.classifications if c.is_conditionally_safe)

    @property
    def unsafe_count(self) -> int:
        return sum(1 for c in self.classifications
                   if c.safety == SafetyLevel.UNGUARDED)

    @property
    def unresolvable_count(self) -> int:
        return sum(1 for c in self.classifications
                   if c.safety == SafetyLevel.UNRESOLVABLE)

    def by_kind(self) -> dict[ExceptionKind, list[SafetyClassification]]:
        result: dict[ExceptionKind, list[SafetyClassification]] = {}
        for c in self.classifications:
            result.setdefault(c.source.kind, []).append(c)
        return result

    def by_method(self) -> dict[VerificationMethod, int]:
        counts: dict[VerificationMethod, int] = {}
        for c in self.classifications:
            counts[c.method] = counts.get(c.method, 0) + 1
        return counts


# ═══════════════════════════════════════════════════════════════════
# 3.  Module-Level Report
# ═══════════════════════════════════════════════════════════════════

class ModuleVerdict(Enum):
    """Overall verdict for a module."""
    EXCEPTION_FREE       = auto()  # all functions exception-free
    CONDITIONALLY_SAFE   = auto()  # safe under stated preconditions
    PARTIALLY_VERIFIED   = auto()  # some functions have unresolved sources
    HAS_UNSAFE_FUNCTIONS = auto()  # some functions definitely unsafe
    ANALYSIS_FAILED      = auto()  # analysis could not complete


@dataclass
class VerificationStatistics:
    """Aggregate statistics for the verification run."""
    total_functions: int = 0
    total_exception_sources: int = 0
    proved_safe: int = 0
    safe_by_pattern: int = 0
    safe_under_preconditions: int = 0
    caught_by_try_except: int = 0
    unguarded: int = 0
    unresolvable: int = 0
    z3_calls: int = 0
    z3_total_time_ms: float = 0.0
    abstract_interp_resolutions: int = 0
    guard_resolutions: int = 0
    total_duration_ms: float = 0.0

    @property
    def total_safe(self) -> int:
        return (self.proved_safe + self.safe_by_pattern
                + self.caught_by_try_except)

    @property
    def safety_rate(self) -> float:
        if self.total_exception_sources == 0:
            return 1.0
        return self.total_safe / self.total_exception_sources

    @property
    def conditional_safety_rate(self) -> float:
        if self.total_exception_sources == 0:
            return 1.0
        return ((self.total_safe + self.safe_under_preconditions)
                / self.total_exception_sources)

    def __repr__(self) -> str:
        return (
            f"Stats(sources={self.total_exception_sources}, "
            f"safe={self.total_safe}, "
            f"conditional={self.safe_under_preconditions}, "
            f"unguarded={self.unguarded}, "
            f"unresolvable={self.unresolvable}, "
            f"z3_time={self.z3_total_time_ms:.1f}ms, "
            f"total_time={self.total_duration_ms:.1f}ms)"
        )


@dataclass
class ModuleExceptionFreedomReport:
    """Complete exception-freedom report for a module."""
    module_path: str
    verdict: ModuleVerdict = ModuleVerdict.ANALYSIS_FAILED
    functions: list[FunctionExceptionReport] = field(default_factory=list)
    statistics: VerificationStatistics = field(default_factory=VerificationStatistics)
    preconditions_assumed: list[str] = field(default_factory=list)
    axioms_used: list[str] = field(default_factory=list)
    timestamp: float = field(default_factory=time.time)

    @property
    def exception_free_functions(self) -> list[FunctionExceptionReport]:
        return [f for f in self.functions
                if f.verdict == FunctionVerdict.EXCEPTION_FREE]

    @property
    def conditionally_safe_functions(self) -> list[FunctionExceptionReport]:
        return [f for f in self.functions
                if f.verdict == FunctionVerdict.CONDITIONALLY_SAFE]

    @property
    def unsafe_functions(self) -> list[FunctionExceptionReport]:
        return [f for f in self.functions
                if f.verdict == FunctionVerdict.UNSAFE]

    @property
    def trivially_safe_functions(self) -> list[FunctionExceptionReport]:
        return [f for f in self.functions
                if f.verdict == FunctionVerdict.TRIVIALLY_SAFE]

    def compute_verdict(self) -> None:
        """Compute the module verdict from function verdicts."""
        if not self.functions:
            self.verdict = ModuleVerdict.ANALYSIS_FAILED
            return

        verdicts = {f.verdict for f in self.functions}

        if verdicts <= {FunctionVerdict.EXCEPTION_FREE,
                        FunctionVerdict.TRIVIALLY_SAFE}:
            self.verdict = ModuleVerdict.EXCEPTION_FREE
        elif FunctionVerdict.UNSAFE in verdicts:
            self.verdict = ModuleVerdict.HAS_UNSAFE_FUNCTIONS
        elif FunctionVerdict.PARTIALLY_VERIFIED in verdicts:
            self.verdict = ModuleVerdict.PARTIALLY_VERIFIED
        else:
            self.verdict = ModuleVerdict.CONDITIONALLY_SAFE

    def compute_statistics(self) -> None:
        """Recompute statistics from function reports."""
        stats = VerificationStatistics()
        stats.total_functions = len(self.functions)

        for fn in self.functions:
            for c in fn.classifications:
                stats.total_exception_sources += 1
                if c.safety == SafetyLevel.PROVED_SAFE:
                    stats.proved_safe += 1
                elif c.safety == SafetyLevel.SAFE_BY_PATTERN:
                    stats.safe_by_pattern += 1
                elif c.safety == SafetyLevel.SAFE_UNDER_PRECOND:
                    stats.safe_under_preconditions += 1
                elif c.safety == SafetyLevel.CAUGHT:
                    stats.caught_by_try_except += 1
                elif c.safety == SafetyLevel.UNGUARDED:
                    stats.unguarded += 1
                elif c.safety == SafetyLevel.UNRESOLVABLE:
                    stats.unresolvable += 1

                if c.method == VerificationMethod.Z3_PROOF:
                    stats.z3_calls += 1
                    stats.z3_total_time_ms += c.z3_time_ms
                elif c.method == VerificationMethod.ABSTRACT_INTERP:
                    stats.abstract_interp_resolutions += 1
                elif c.method == VerificationMethod.GUARD_ANALYSIS:
                    stats.guard_resolutions += 1

            stats.total_duration_ms += fn.duration_ms

        self.statistics = stats

    def summary(self) -> str:
        """One-line summary."""
        s = self.statistics
        return (
            f"Module {self.module_path}: {self.verdict.name} — "
            f"{s.total_functions} functions, "
            f"{s.total_exception_sources} exception sources, "
            f"{s.total_safe} proved safe, "
            f"{s.safe_under_preconditions} conditionally safe, "
            f"{s.unguarded} unguarded, "
            f"{s.unresolvable} unresolvable "
            f"({s.total_duration_ms:.1f}ms)"
        )

    def __repr__(self) -> str:
        return self.summary()


# ═══════════════════════════════════════════════════════════════════
# 4.  Report Formatter
# ═══════════════════════════════════════════════════════════════════

class ReportFormatter:
    """Render exception-freedom reports in various formats."""

    @staticmethod
    def to_text(report: ModuleExceptionFreedomReport, *,
                verbose: bool = False) -> str:
        """Render a plain-text report."""
        lines: list[str] = []
        lines.append("=" * 72)
        lines.append(f"  Exception Freedom Report: {report.module_path}")
        lines.append(f"  Verdict: {report.verdict.name}")
        lines.append("=" * 72)
        lines.append("")

        s = report.statistics
        lines.append(f"  Functions analyzed:      {s.total_functions}")
        lines.append(f"  Exception sources found: {s.total_exception_sources}")
        lines.append(f"  Proved safe:             {s.proved_safe}")
        lines.append(f"  Safe by pattern:         {s.safe_by_pattern}")
        lines.append(f"  Caught (try/except):     {s.caught_by_try_except}")
        lines.append(f"  Conditionally safe:      {s.safe_under_preconditions}")
        lines.append(f"  Unguarded:               {s.unguarded}")
        lines.append(f"  Unresolvable:            {s.unresolvable}")
        lines.append(f"  Safety rate:             {s.safety_rate:.1%}")
        lines.append(f"  Cond. safety rate:       {s.conditional_safety_rate:.1%}")
        lines.append(f"  Total time:              {s.total_duration_ms:.1f}ms")
        if s.z3_calls:
            lines.append(f"  Z3 calls:                {s.z3_calls}")
            lines.append(f"  Z3 time:                 {s.z3_total_time_ms:.1f}ms")
        lines.append("")

        # ── Per-function breakdown ────────────────────────────
        lines.append("─" * 72)
        lines.append("  Per-Function Results")
        lines.append("─" * 72)

        # Group by verdict
        for verdict_name, fn_list in [
            ("✓ EXCEPTION FREE", report.exception_free_functions),
            ("✓ TRIVIALLY SAFE", report.trivially_safe_functions),
            ("~ CONDITIONALLY SAFE", report.conditionally_safe_functions),
            ("✗ UNSAFE", report.unsafe_functions),
        ]:
            if fn_list:
                lines.append(f"\n  {verdict_name} ({len(fn_list)}):")
                for fn in fn_list:
                    sym = {"EXCEPTION_FREE": "✓", "TRIVIALLY_SAFE": "·",
                           "CONDITIONALLY_SAFE": "~", "UNSAFE": "✗",
                           "PARTIALLY_VERIFIED": "?", "SKIPPED": "-"
                           }.get(fn.verdict.name, "?")
                    lines.append(
                        f"    {sym} {fn.qualified_name:40s} "
                        f"{fn.safe_count}/{fn.total_sources} safe"
                        f"  ({fn.duration_ms:.1f}ms)"
                    )

                    if verbose:
                        for c in fn.classifications:
                            cs = "✓" if c.is_safe else "✗"
                            lines.append(
                                f"      {cs} L{c.source.location.lineno:4d} "
                                f"{c.source.kind.name:20s} "
                                f"{c.safety.name:20s} "
                                f"{c.method.name}"
                            )

        lines.append("")
        lines.append("=" * 72)
        return "\n".join(lines)

    @staticmethod
    def to_dict(report: ModuleExceptionFreedomReport) -> dict[str, Any]:
        """Render as a JSON-serializable dict."""
        return {
            "module_path": report.module_path,
            "verdict": report.verdict.name,
            "statistics": {
                "total_functions": report.statistics.total_functions,
                "total_exception_sources": report.statistics.total_exception_sources,
                "proved_safe": report.statistics.proved_safe,
                "safe_by_pattern": report.statistics.safe_by_pattern,
                "caught_by_try_except": report.statistics.caught_by_try_except,
                "safe_under_preconditions": report.statistics.safe_under_preconditions,
                "unguarded": report.statistics.unguarded,
                "unresolvable": report.statistics.unresolvable,
                "safety_rate": report.statistics.safety_rate,
                "z3_calls": report.statistics.z3_calls,
                "z3_total_time_ms": report.statistics.z3_total_time_ms,
                "total_duration_ms": report.statistics.total_duration_ms,
            },
            "functions": [
                {
                    "name": fn.qualified_name,
                    "verdict": fn.verdict.name,
                    "total_sources": fn.total_sources,
                    "safe": fn.safe_count,
                    "unsafe": fn.unsafe_count,
                    "classifications": [
                        {
                            "kind": c.source.kind.name,
                            "line": c.source.location.lineno,
                            "safety": c.safety.name,
                            "method": c.method.name,
                            "condition": c.condition,
                        }
                        for c in fn.classifications
                    ],
                }
                for fn in report.functions
            ],
        }

    @staticmethod
    def to_json(report: ModuleExceptionFreedomReport, *,
                indent: int = 2) -> str:
        """Render as JSON string."""
        return json.dumps(ReportFormatter.to_dict(report), indent=indent)

    @staticmethod
    def to_markdown(report: ModuleExceptionFreedomReport) -> str:
        """Render as Markdown."""
        lines: list[str] = []
        lines.append(f"# Exception Freedom Report: {report.module_path}")
        lines.append("")
        lines.append(f"**Verdict:** {report.verdict.name}")
        lines.append("")

        s = report.statistics
        lines.append("## Statistics")
        lines.append("")
        lines.append(f"| Metric | Value |")
        lines.append(f"|--------|-------|")
        lines.append(f"| Functions | {s.total_functions} |")
        lines.append(f"| Exception sources | {s.total_exception_sources} |")
        lines.append(f"| Proved safe | {s.proved_safe} |")
        lines.append(f"| Safe by pattern | {s.safe_by_pattern} |")
        lines.append(f"| Caught | {s.caught_by_try_except} |")
        lines.append(f"| Conditional | {s.safe_under_preconditions} |")
        lines.append(f"| Unguarded | {s.unguarded} |")
        lines.append(f"| Safety rate | {s.safety_rate:.1%} |")
        lines.append(f"| Duration | {s.total_duration_ms:.1f}ms |")
        lines.append("")

        lines.append("## Functions")
        lines.append("")
        lines.append("| Function | Verdict | Safe/Total |")
        lines.append("|----------|---------|------------|")
        for fn in report.functions:
            v = fn.verdict.name
            lines.append(f"| `{fn.qualified_name}` | {v} | "
                         f"{fn.safe_count}/{fn.total_sources} |")

        return "\n".join(lines)
