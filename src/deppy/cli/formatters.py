"""Terminal output formatters for DepPy CLI.

Provides three output modes:
- TerminalFormatter: Colorized terminal output with ANSI codes.
- PlainFormatter: Plain text without colors (for piping/logging).
- JsonFormatter: Machine-readable JSON output.
"""

from __future__ import annotations

import json
import sys
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    List,
    Optional,
    Sequence,
    Tuple,
)

from deppy.pipeline.pipeline import PipelineResult, PipelineTiming
from deppy.pipeline.stages.render_stage import (
    ContractAnnotation,
    Diagnostic,
    DiagnosticSeverity,
    RenderResult,
)


# ===================================================================
#  ANSI color codes
# ===================================================================


class _Colors:
    """ANSI escape codes for terminal colors."""

    RESET = "\033[0m"
    BOLD = "\033[1m"
    DIM = "\033[2m"
    UNDERLINE = "\033[4m"

    RED = "\033[31m"
    GREEN = "\033[32m"
    YELLOW = "\033[33m"
    BLUE = "\033[34m"
    MAGENTA = "\033[35m"
    CYAN = "\033[36m"
    WHITE = "\033[37m"

    BRIGHT_RED = "\033[91m"
    BRIGHT_GREEN = "\033[92m"
    BRIGHT_YELLOW = "\033[93m"
    BRIGHT_BLUE = "\033[94m"
    BRIGHT_MAGENTA = "\033[95m"
    BRIGHT_CYAN = "\033[96m"

    BG_RED = "\033[41m"
    BG_GREEN = "\033[42m"
    BG_YELLOW = "\033[43m"

    @classmethod
    def severity_color(cls, severity: DiagnosticSeverity) -> str:
        mapping = {
            DiagnosticSeverity.ERROR: cls.BRIGHT_RED,
            DiagnosticSeverity.WARNING: cls.BRIGHT_YELLOW,
            DiagnosticSeverity.INFO: cls.BRIGHT_BLUE,
            DiagnosticSeverity.HINT: cls.BRIGHT_CYAN,
        }
        return mapping.get(severity, cls.WHITE)

    @classmethod
    def severity_icon(cls, severity: DiagnosticSeverity) -> str:
        mapping = {
            DiagnosticSeverity.ERROR: "E",
            DiagnosticSeverity.WARNING: "W",
            DiagnosticSeverity.INFO: "I",
            DiagnosticSeverity.HINT: "H",
        }
        return mapping.get(severity, "?")


class _NoColors:
    """Dummy color class for no-color mode."""

    RESET = ""
    BOLD = ""
    DIM = ""
    UNDERLINE = ""
    RED = ""
    GREEN = ""
    YELLOW = ""
    BLUE = ""
    MAGENTA = ""
    CYAN = ""
    WHITE = ""
    BRIGHT_RED = ""
    BRIGHT_GREEN = ""
    BRIGHT_YELLOW = ""
    BRIGHT_BLUE = ""
    BRIGHT_MAGENTA = ""
    BRIGHT_CYAN = ""
    BG_RED = ""
    BG_GREEN = ""
    BG_YELLOW = ""

    @classmethod
    def severity_color(cls, severity: DiagnosticSeverity) -> str:
        return ""

    @classmethod
    def severity_icon(cls, severity: DiagnosticSeverity) -> str:
        mapping = {
            DiagnosticSeverity.ERROR: "E",
            DiagnosticSeverity.WARNING: "W",
            DiagnosticSeverity.INFO: "I",
            DiagnosticSeverity.HINT: "H",
        }
        return mapping.get(severity, "?")


# ===================================================================
#  Formatter base
# ===================================================================


class Formatter(ABC):
    """Abstract base for output formatters."""

    @abstractmethod
    def format_diagnostic(self, diag: Diagnostic) -> str:
        """Format a single diagnostic."""
        ...

    @abstractmethod
    def format_summary(self, result: PipelineResult) -> str:
        """Format a summary of the pipeline result."""
        ...

    @abstractmethod
    def format_progress(self, stage_name: str, status: str = "running") -> str:
        """Format a progress indicator for a stage."""
        ...

    @abstractmethod
    def format_contracts(self, contracts: Sequence[ContractAnnotation]) -> str:
        """Format generated contracts."""
        ...

    def format_result(self, result: PipelineResult) -> str:
        """Format a complete pipeline result."""
        parts: List[str] = []

        # Diagnostics
        for diag in result.diagnostics:
            parts.append(self.format_diagnostic(diag))

        # Summary
        parts.append(self.format_summary(result))

        # Contracts
        if result.contracts:
            parts.append(self.format_contracts(result.contracts))

        return "\n".join(parts)


# ===================================================================
#  Terminal formatter
# ===================================================================


class TerminalFormatter(Formatter):
    """Colorized terminal output formatter.

    Uses ANSI escape codes for coloring severity levels, timing data,
    and structural elements.
    """

    def __init__(self, color: bool = True) -> None:
        self._c = _Colors if color else _NoColors

    def format_diagnostic(self, diag: Diagnostic) -> str:
        c = self._c
        severity = diag.severity
        color = c.severity_color(severity)
        icon = c.severity_icon(severity)
        reset = c.RESET

        parts: List[str] = []

        # Location
        if diag.location:
            loc = diag.location.pretty()
            parts.append(f"{c.BOLD}{loc}{reset}")

        # Severity and code
        parts.append(f"{color}{c.BOLD}[{icon}]{reset}")
        if diag.code:
            parts.append(f"{c.DIM}({diag.code}){reset}")

        # Message
        parts.append(diag.message)

        result = " ".join(parts)

        # Suggestion
        if diag.suggestion:
            result += f"\n  {c.GREEN}hint:{reset} {diag.suggestion}"

        # Related locations
        if diag.related:
            for rel in diag.related:
                result += f"\n  {c.DIM}related:{reset} {rel.pretty()}"

        return result

    def format_summary(self, result: PipelineResult) -> str:
        c = self._c

        lines: List[str] = []
        lines.append("")

        # Status line
        if result.success:
            status = f"{c.BRIGHT_GREEN}{c.BOLD}Analysis complete{c.RESET}"
        else:
            status = f"{c.BRIGHT_RED}{c.BOLD}Analysis found issues{c.RESET}"
        lines.append(status)

        # Counts
        lines.append(
            f"  {c.BOLD}Sites:{c.RESET} {result.site_count}  "
            f"{c.BOLD}Sections:{c.RESET} {len(result.sections)}  "
            f"{c.BOLD}Obstructions:{c.RESET} {result.obstruction_count}"
        )

        # Error/warning counts
        error_str = f"{c.RED}{result.error_count} errors{c.RESET}" if result.error_count else "0 errors"
        warn_str = f"{c.YELLOW}{result.warning_count} warnings{c.RESET}" if result.warning_count else "0 warnings"
        lines.append(f"  {error_str}, {warn_str}")

        # Timing
        if result.timing:
            timing = result.timing
            lines.append(
                f"  {c.DIM}Time: {timing.total_elapsed:.3f}s{c.RESET}"
            )
            for st in timing.stage_timings:
                status_color = c.GREEN if st.status.value == "completed" else c.YELLOW
                lines.append(
                    f"    {c.DIM}{st.stage_name}:{c.RESET} "
                    f"{status_color}{st.elapsed_seconds:.3f}s{c.RESET} "
                    f"({st.status.value})"
                )

        # Convergence
        if result.convergence:
            conv = result.convergence
            conv_status = f"{c.GREEN}converged{c.RESET}" if conv.converged else f"{c.YELLOW}not converged{c.RESET}"
            lines.append(
                f"  Convergence: {conv_status} "
                f"({conv.iterations_used}/{conv.max_iterations} iterations)"
            )

        return "\n".join(lines)

    def format_progress(self, stage_name: str, status: str = "running") -> str:
        c = self._c
        if status == "running":
            return f"{c.CYAN}>>>{c.RESET} {stage_name}..."
        elif status == "done":
            return f"{c.GREEN}   {c.RESET} {stage_name} {c.GREEN}done{c.RESET}"
        elif status == "skip":
            return f"{c.DIM}   {stage_name} skipped{c.RESET}"
        elif status == "fail":
            return f"{c.RED}!!{c.RESET} {stage_name} {c.RED}FAILED{c.RESET}"
        return f"  {stage_name}: {status}"

    def format_contracts(self, contracts: Sequence[ContractAnnotation]) -> str:
        c = self._c
        if not contracts:
            return ""

        lines: List[str] = []
        lines.append(f"\n{c.BOLD}Generated contracts:{c.RESET}")

        # Group by scope
        scope_contracts: Dict[str, List[ContractAnnotation]] = {}
        for contract in contracts:
            scope_contracts.setdefault(contract.scope_name, []).append(contract)

        for scope_name, scope_contracts_list in sorted(scope_contracts.items()):
            lines.append(f"  {c.CYAN}{scope_name}{c.RESET}:")
            for contract in scope_contracts_list:
                kind_color = c.GREEN if contract.kind == "requires" else c.BLUE
                lines.append(
                    f"    {kind_color}@{contract.kind}{c.RESET} "
                    f"{contract.predicate_text}"
                )

        return "\n".join(lines)


# ===================================================================
#  Plain formatter
# ===================================================================


class PlainFormatter(Formatter):
    """Plain text formatter without colors."""

    def format_diagnostic(self, diag: Diagnostic) -> str:
        parts: List[str] = []
        if diag.location:
            parts.append(diag.location.pretty())
        parts.append(f"[{diag.severity.value}]")
        if diag.code:
            parts.append(f"({diag.code})")
        parts.append(diag.message)
        result = " ".join(parts)
        if diag.suggestion:
            result += f"\n  hint: {diag.suggestion}"
        return result

    def format_summary(self, result: PipelineResult) -> str:
        lines: List[str] = []
        status = "SUCCESS" if result.success else "FAILURE"
        lines.append(f"\nAnalysis: {status}")
        lines.append(f"  Sites: {result.site_count}")
        lines.append(f"  Sections: {len(result.sections)}")
        lines.append(f"  Obstructions: {result.obstruction_count}")
        lines.append(f"  Errors: {result.error_count}, Warnings: {result.warning_count}")
        if result.timing:
            lines.append(f"  Time: {result.timing.total_elapsed:.3f}s")
        return "\n".join(lines)

    def format_progress(self, stage_name: str, status: str = "running") -> str:
        return f"  {stage_name}: {status}"

    def format_contracts(self, contracts: Sequence[ContractAnnotation]) -> str:
        if not contracts:
            return ""
        lines: List[str] = ["\nGenerated contracts:"]
        for c in contracts:
            lines.append(f"  @{c.kind} on {c.scope_name}: {c.predicate_text}")
        return "\n".join(lines)


# ===================================================================
#  JSON formatter
# ===================================================================


class JsonFormatter(Formatter):
    """JSON output formatter for machine consumption."""

    def __init__(self, indent: int = 2) -> None:
        self._indent = indent

    def format_diagnostic(self, diag: Diagnostic) -> str:
        data = {
            "severity": diag.severity.value,
            "message": diag.message,
            "code": diag.code,
        }
        if diag.location:
            data["location"] = {
                "file": diag.location.file,
                "line": diag.location.line,
                "col": diag.location.col,
            }
        if diag.suggestion:
            data["suggestion"] = diag.suggestion
        if diag.related:
            data["related"] = [
                {"file": r.file, "line": r.line, "col": r.col}
                for r in diag.related
            ]
        return json.dumps(data, indent=self._indent)

    def format_summary(self, result: PipelineResult) -> str:
        data: Dict[str, Any] = {
            "success": result.success,
            "sites": result.site_count,
            "sections": len(result.sections),
            "obstructions": result.obstruction_count,
            "errors": result.error_count,
            "warnings": result.warning_count,
        }
        if result.timing:
            data["timing"] = {
                "total_seconds": round(result.timing.total_elapsed, 4),
                "stages": {
                    st.stage_name: {
                        "seconds": round(st.elapsed_seconds, 4),
                        "status": st.status.value,
                    }
                    for st in result.timing.stage_timings
                },
            }
        if result.convergence:
            data["convergence"] = {
                "converged": result.convergence.converged,
                "iterations": result.convergence.iterations_used,
                "max_iterations": result.convergence.max_iterations,
            }
        return json.dumps(data, indent=self._indent)

    def format_progress(self, stage_name: str, status: str = "running") -> str:
        return json.dumps({"stage": stage_name, "status": status})

    def format_contracts(self, contracts: Sequence[ContractAnnotation]) -> str:
        data = [
            {
                "scope": c.scope_name,
                "kind": c.kind,
                "predicate": c.predicate_text,
                "trust": c.trust.value,
            }
            for c in contracts
        ]
        return json.dumps({"contracts": data}, indent=self._indent)

    def format_result(self, result: PipelineResult) -> str:
        """Produce a single JSON document for the entire result."""
        diagnostics = []
        for diag in result.diagnostics:
            d: Dict[str, Any] = {
                "severity": diag.severity.value,
                "message": diag.message,
                "code": diag.code,
            }
            if diag.location:
                d["location"] = {
                    "file": diag.location.file,
                    "line": diag.location.line,
                    "col": diag.location.col,
                }
            if diag.suggestion:
                d["suggestion"] = diag.suggestion
            diagnostics.append(d)

        contracts_data = [
            {
                "scope": c.scope_name,
                "kind": c.kind,
                "predicate": c.predicate_text,
                "trust": c.trust.value,
            }
            for c in result.contracts
        ]

        data = {
            "success": result.success,
            "diagnostics": diagnostics,
            "contracts": contracts_data,
            "sites": result.site_count,
            "obstructions": result.obstruction_count,
            "errors": result.error_count,
            "warnings": result.warning_count,
        }

        if result.timing:
            data["timing_seconds"] = round(result.timing.total_elapsed, 4)

        return json.dumps(data, indent=self._indent)


# ===================================================================
#  Formatter factory
# ===================================================================


def create_formatter(format_name: str, color: bool = True) -> Formatter:
    """Create a formatter by name.

    Supported names: 'terminal', 'plain', 'json'.
    """
    if format_name == "json":
        return JsonFormatter()
    if format_name == "plain" or not color:
        return PlainFormatter()
    return TerminalFormatter(color=color)
