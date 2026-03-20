"""
Pillar 6 — End-to-End Verified Pipeline: CLI Interface

Command-line interface for the hybrid verification system.
Provides subcommands for verification, checking, translation,
discharge, specification parsing, status, and reporting.
"""

from __future__ import annotations


# --- Integration with existing deppy codebase ---
try:
    from deppy.cli.main import main as _core_cli_main
    from deppy.cli.config import Config as _CoreCliConfig
    from deppy.cli.formatters import format_result as _core_format_result
    from deppy.render.diagnostic_renderer import Diagnostic as _CoreDiagnostic
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

import argparse
import json
import os
import sys
import textwrap
import time
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Sequence, TextIO

from .stages import (
    PipelineStage,
    StageOutput,
    IdeationStage,
    SpecificationStage,
    SynthesisStage,
    StructuralCheckStage,
    SemanticCheckStage,
    LeanTranslationStage,
    DischargeStage,
    ProductionStage,
    STAGE_NAMES,
    list_stages,
)
from .orchestrator import (

    PipelineConfig,
    PipelineOrchestrator,
    PipelineResult,
    PipelineManifest,
    GateResult,
    SPEC_GATE,
    STRUCTURAL_GATE,
    SEMANTIC_GATE,
    LEAN_GATE,
    PRODUCTION_GATE,
)

# ---------------------------------------------------------------------------
# ANSI color codes
# ---------------------------------------------------------------------------

class _Colors:
    """ANSI escape codes for terminal colouring."""

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

    BG_RED = "\033[41m"
    BG_GREEN = "\033[42m"
    BG_YELLOW = "\033[43m"

    @classmethod
    def disable(cls) -> None:
        """Disable all colour codes (for piped / non-TTY output)."""
        for attr in dir(cls):
            if attr.isupper() and not attr.startswith("_"):
                setattr(cls, attr, "")

# Disable colours if stdout is not a TTY
if not hasattr(sys.stdout, "isatty") or not sys.stdout.isatty():
    _Colors.disable()

C = _Colors

# ---------------------------------------------------------------------------
# ProjectConfig — load from deppy.toml / pyproject.toml
# ---------------------------------------------------------------------------

@dataclass
class ProjectConfig:
    """Project-level configuration loaded from ``deppy.toml`` or
    ``pyproject.toml [tool.deppy.hybrid]``.
    """

    oracle_model: str = "gpt-4"
    z3_timeout_ms: int = 5000
    cache_dir: Optional[str] = None
    lean_project_dir: Optional[str] = None
    trust_thresholds: Dict[str, float] = field(default_factory=lambda: {
        "semantic_confidence": 0.8,
    })
    strict_gates: bool = True
    emit_lean: bool = True
    emit_sarif: bool = False
    max_discharge_attempts: int = 3

    @classmethod
    def load(cls, search_dir: Optional[str] = None) -> ProjectConfig:
        """Search for config in ``deppy.toml`` or ``pyproject.toml``.

        Walks up from *search_dir* (default: cwd) looking for config files.
        """
        start = search_dir or os.getcwd()
        current = os.path.abspath(start)

        for _ in range(20):  # guard against infinite loop
            # Try deppy.toml
            deppy_toml = os.path.join(current, "deppy.toml")
            if os.path.isfile(deppy_toml):
                return cls._load_deppy_toml(deppy_toml)

            # Try pyproject.toml [tool.deppy.hybrid]
            pyproject = os.path.join(current, "pyproject.toml")
            if os.path.isfile(pyproject):
                cfg = cls._load_pyproject(pyproject)
                if cfg is not None:
                    return cfg

            parent = os.path.dirname(current)
            if parent == current:
                break
            current = parent

        return cls()  # defaults

    @classmethod
    def _load_deppy_toml(cls, path: str) -> ProjectConfig:
        """Load config from a ``deppy.toml`` file."""
        try:
            import tomllib  # Python 3.11+
        except ImportError:
            try:
                import tomli as tomllib  # type: ignore[no-redef]
            except ImportError:
                return cls()

        try:
            with open(path, "rb") as f:
                data = tomllib.load(f)
            hybrid = data.get("hybrid", data)
            return cls._from_dict(hybrid)
        except Exception:
            return cls()

    @classmethod
    def _load_pyproject(cls, path: str) -> Optional[ProjectConfig]:
        """Load config from ``pyproject.toml [tool.deppy.hybrid]``."""
        try:
            import tomllib
        except ImportError:
            try:
                import tomli as tomllib  # type: ignore[no-redef]
            except ImportError:
                return None

        try:
            with open(path, "rb") as f:
                data = tomllib.load(f)
            hybrid = data.get("tool", {}).get("deppy", {}).get("hybrid")
            if hybrid is None:
                return None
            return cls._from_dict(hybrid)
        except Exception:
            return None

    @classmethod
    def _from_dict(cls, d: Dict[str, Any]) -> ProjectConfig:
        return cls(
            oracle_model=d.get("oracle_model", "gpt-4"),
            z3_timeout_ms=d.get("z3_timeout_ms", 5000),
            cache_dir=d.get("cache_dir"),
            lean_project_dir=d.get("lean_project_dir"),
            trust_thresholds=d.get("trust_thresholds", {
                "semantic_confidence": 0.8,
            }),
            strict_gates=d.get("strict_gates", True),
            emit_lean=d.get("emit_lean", True),
            emit_sarif=d.get("emit_sarif", False),
            max_discharge_attempts=d.get("max_discharge_attempts", 3),
        )

    def to_pipeline_config(self) -> PipelineConfig:
        """Convert to a ``PipelineConfig`` for the orchestrator."""
        return PipelineConfig(
            llm_model=self.oracle_model,
            z3_timeout_ms=self.z3_timeout_ms,
            strict_gates=self.strict_gates,
            semantic_confidence_threshold=self.trust_thresholds.get(
                "semantic_confidence", 0.8
            ),
            max_discharge_attempts=self.max_discharge_attempts,
            cache_dir=self.cache_dir,
            lean_project_dir=self.lean_project_dir,
            emit_lean=self.emit_lean,
            emit_sarif=self.emit_sarif,
        )

# ---------------------------------------------------------------------------
# OutputFormatter
# ---------------------------------------------------------------------------

class OutputFormatter:
    """Format pipeline outputs for terminal display with ANSI colours.

    Colours:
      - GREEN:  Z3_PROVEN, LEAN_VERIFIED
      - YELLOW: LLM_JUDGED
      - RED:    CONTRADICTED
    """

    # -- Trust levels -------------------------------------------------------

    @staticmethod
    def format_trust_level(level: str) -> str:
        """Coloured trust level string."""
        level_lower = level.lower()
        if level_lower in ("lean_verified",):
            return f"{C.GREEN}{C.BOLD}{level}{C.RESET}"
        elif level_lower in ("z3_proven",):
            return f"{C.GREEN}{level}{C.RESET}"
        elif level_lower in ("llm_judged",):
            return f"{C.YELLOW}{level}{C.RESET}"
        elif level_lower in ("runtime_checked",):
            return f"{C.YELLOW}{C.DIM}{level}{C.RESET}"
        elif level_lower in ("untrusted",):
            return f"{C.DIM}{level}{C.RESET}"
        elif level_lower in ("contradicted",):
            return f"{C.RED}{C.BOLD}{level}{C.RESET}"
        else:
            return level

    # -- Check results ------------------------------------------------------

    @staticmethod
    def format_check_result(result: Dict[str, Any]) -> str:
        """Format a single check result with ✓/✗ icon."""
        status = result.get("status", result.get("judgment", "unknown"))
        spec_id = result.get("spec_id", "")
        reason = result.get("reason", result.get("reasoning", ""))

        if status in ("proven", "supported", "discharged"):
            icon = f"{C.GREEN}✓{C.RESET}"
        elif status in ("refuted", "contradicted", "failed"):
            icon = f"{C.RED}✗{C.RESET}"
        elif status in ("timeout", "unknown", "unclear"):
            icon = f"{C.YELLOW}?{C.RESET}"
        elif status == "sorry":
            icon = f"{C.YELLOW}⚠{C.RESET}"
        else:
            icon = "○"

        line = f"  {icon} {spec_id}"
        if status:
            line += f"  [{status}]"
        if reason:
            # Truncate long reasons
            short = reason[:80] + "..." if len(reason) > 80 else reason
            line += f"  {C.DIM}{short}{C.RESET}"
        return line

    # -- H¹ status ----------------------------------------------------------

    @staticmethod
    def format_h1_status(h1: Any) -> str:
        """Format the H¹ cohomology status."""
        if isinstance(h1, dict):
            status = h1.get("status", h1.get("h1_status", "unknown"))
        elif isinstance(h1, str):
            status = h1
        else:
            status = str(h1)

        if "= 0" in status and "≠" not in status:
            return f"{C.GREEN}{C.BOLD}{status}{C.RESET}"
        elif "≠ 0" in status:
            return f"{C.YELLOW}{C.BOLD}{status}{C.RESET}"
        else:
            return f"{C.DIM}{status}{C.RESET}"

    # -- Pipeline summary ---------------------------------------------------

    @staticmethod
    def format_pipeline_summary(result: Any) -> str:
        """Format a full pipeline summary table."""
        if isinstance(result, PipelineResult):
            return OutputFormatter._format_pipeline_result(result)
        elif isinstance(result, dict):
            return OutputFormatter._format_pipeline_dict(result)
        else:
            return str(result)

    @staticmethod
    def _format_pipeline_result(result: PipelineResult) -> str:
        """Format a PipelineResult object."""
        lines: List[str] = []

        # Header
        if result.success:
            header = f"{C.GREEN}{C.BOLD}Pipeline PASSED{C.RESET}"
        else:
            header = f"{C.RED}{C.BOLD}Pipeline FAILED{C.RESET}"
        lines.append(header)
        lines.append("─" * 60)

        # Trust and H¹
        trust_str = OutputFormatter.format_trust_level(result.overall_trust)
        h1_str = OutputFormatter.format_h1_status(result.h1_status)
        lines.append(f"  Trust:     {trust_str}")
        lines.append(f"  H¹:       {h1_str}")
        lines.append(f"  Duration:  {result.total_duration_ms:.1f} ms")

        if result.error:
            lines.append(f"  {C.RED}Error: {result.error}{C.RESET}")

        # Stage table
        lines.append("")
        lines.append(f"  {'Stage':<22s} {'Trust':<18s} {'Time':>10s}")
        lines.append("  " + "─" * 52)

        for stage in PipelineStage.ordered():
            name = STAGE_NAMES[stage]
            if stage in result.stages:
                out = result.stages[stage]
                if out.is_error:
                    status = f"{C.RED}ERROR{C.RESET}"
                else:
                    status = OutputFormatter.format_trust_level(out.trust_level)
                time_str = f"{out.duration_ms:.1f}ms"
            else:
                status = f"{C.DIM}skipped{C.RESET}"
                time_str = "—"
            lines.append(f"  {name:<22s} {status:<30s} {time_str:>10s}")

        # Gates
        if result.gate_results:
            lines.append("")
            lines.append("  Gates:")
            for name, gr in result.gate_results.items():
                icon = f"{C.GREEN}✓{C.RESET}" if gr.passed else f"{C.RED}✗{C.RESET}"
                lines.append(f"    {icon} {name}")
                for f in gr.failures:
                    lines.append(f"        {C.RED}└─ {f}{C.RESET}")

        # Obligations
        all_obl = result.all_obligations
        if all_obl:
            sorry = result.sorry_count
            lines.append("")
            lines.append(f"  Obligations: {len(all_obl)} total, {sorry} sorry'd")

        return "\n".join(lines)

    @staticmethod
    def _format_pipeline_dict(result: Dict[str, Any]) -> str:
        """Format a pipeline result dict."""
        lines: List[str] = []
        success = result.get("success", False)

        if success:
            lines.append(f"{C.GREEN}{C.BOLD}Pipeline PASSED{C.RESET}")
        else:
            lines.append(f"{C.RED}{C.BOLD}Pipeline FAILED{C.RESET}")

        lines.append("─" * 60)

        trust = result.get("overall_trust", "unknown")
        lines.append(f"  Trust: {OutputFormatter.format_trust_level(trust)}")

        h1 = result.get("h1_status", "unknown")
        lines.append(f"  H¹:    {OutputFormatter.format_h1_status(h1)}")

        return "\n".join(lines)

    # -- Obligations --------------------------------------------------------

    @staticmethod
    def format_obligation(obligation: Dict[str, Any]) -> str:
        """Format a single proof obligation."""
        obl_id = obligation.get("id", obligation.get("obligation_id", "?"))
        status = obligation.get("status", "pending")
        desc = obligation.get("description", "")
        method = obligation.get("method", "")

        if status == "discharged":
            icon = f"{C.GREEN}✓{C.RESET}"
            status_str = f"{C.GREEN}{status}{C.RESET}"
        elif status == "sorry":
            icon = f"{C.YELLOW}⚠{C.RESET}"
            status_str = f"{C.YELLOW}{status}{C.RESET}"
        elif status == "failed":
            icon = f"{C.RED}✗{C.RESET}"
            status_str = f"{C.RED}{status}{C.RESET}"
        else:
            icon = "○"
            status_str = status

        line = f"  {icon} {obl_id:<25s} [{status_str}]"
        if method:
            line += f"  via {method}"
        if desc:
            short = desc[:60] + "..." if len(desc) > 60 else desc
            line += f"\n      {C.DIM}{short}{C.RESET}"
        return line

    # -- Hallucination findings ---------------------------------------------

    @staticmethod
    def format_hallucination(finding: Dict[str, Any]) -> str:
        """Format a hallucination detection finding."""
        kind = finding.get("kind", "unknown")
        severity = finding.get("severity", "warning")
        message = finding.get("message", "")
        location = finding.get("location", "")

        if severity == "error":
            icon = f"{C.RED}✗ HALLUCINATION{C.RESET}"
        elif severity == "warning":
            icon = f"{C.YELLOW}⚠ SUSPICIOUS{C.RESET}"
        else:
            icon = f"{C.DIM}ℹ NOTE{C.RESET}"

        line = f"  {icon}  [{kind}]"
        if location:
            line += f"  at {location}"
        if message:
            line += f"\n      {message}"
        return line

    # -- Stage detail -------------------------------------------------------

    @staticmethod
    def format_stage_detail(stage: PipelineStage, output: StageOutput) -> str:
        """Format detailed output for a single stage."""
        lines: List[str] = []
        name = STAGE_NAMES[stage]

        lines.append(f"{C.BOLD}{name}{C.RESET}")
        lines.append("─" * 40)
        lines.append(
            f"  Trust: {OutputFormatter.format_trust_level(output.trust_level)}"
        )
        lines.append(f"  Time:  {output.duration_ms:.1f} ms")

        if output.is_error:
            lines.append(f"  {C.RED}Error: {output.get('error')}{C.RESET}")
            return "\n".join(lines)

        # Stage-specific details
        if stage == PipelineStage.IDEATION:
            claims = output.get("claims", [])
            lines.append(f"  Claims: {len(claims)}")
            for c in claims[:10]:
                lines.append(f"    • {c.get('text', '?')[:70]}")

        elif stage == PipelineStage.SPECIFICATION:
            stats = output.get("stats", {})
            lines.append(f"  Specs: {stats.get('total', 0)}")
            lines.append(f"    Structural: {stats.get('structural', 0)}")
            lines.append(f"    Semantic:   {stats.get('semantic', 0)}")

        elif stage == PipelineStage.STRUCTURAL_CHECK:
            stats = output.get("stats", {})
            lines.append(f"  Results: {stats.get('total', 0)}")
            lines.append(f"    Proven:  {stats.get('proven', 0)}")
            lines.append(f"    Refuted: {stats.get('refuted', 0)}")
            lines.append(f"    Timeout: {stats.get('timeout', 0)}")

        elif stage == PipelineStage.SEMANTIC_CHECK:
            stats = output.get("stats", {})
            lines.append(f"  Results: {stats.get('total', 0)}")
            lines.append(f"    Supported: {stats.get('supported', 0)}")
            lines.append(f"    Refuted:   {stats.get('refuted', 0)}")
            lines.append(f"    Unclear:   {stats.get('unclear', 0)}")
            lines.append(
                f"    Cache:     {stats.get('cache_hits', 0)} hits / "
                f"{stats.get('cache_misses', 0)} misses"
            )

        elif stage == PipelineStage.LEAN_TRANSLATION:
            stats = output.get("stats", {})
            lines.append(f"  Theorems: {stats.get('theorems', 0)}")
            lines.append(f"  Sorry:    {stats.get('sorry', 0)}")
            lines.append(f"  Lines:    {stats.get('lines', 0)}")

        elif stage == PipelineStage.DISCHARGE:
            stats = output.get("stats", {})
            lines.append(f"  Proofs: {stats.get('total', 0)}")
            lines.append(f"    Discharged: {stats.get('discharged', 0)}")
            lines.append(f"    Sorry:      {stats.get('sorry', 0)}")
            lines.append(f"    Assumed:    {stats.get('assumed', 0)}")

        elif stage == PipelineStage.PRODUCTION:
            artifact = output.get("artifact", {})
            meta = artifact.get("metadata", {})
            lines.append(f"  Proofs:     {meta.get('proof_count', 0)}")
            lines.append(f"  Discharged: {meta.get('discharged_count', 0)}")
            lines.append(f"  Sorry:      {meta.get('sorry_count', 0)}")

        # Obligations
        if output.obligations:
            lines.append(f"  Obligations: {len(output.obligations)}")
            for obl in output.obligations[:5]:
                lines.append(OutputFormatter.format_obligation(obl))
            if len(output.obligations) > 5:
                lines.append(
                    f"    ... and {len(output.obligations) - 5} more"
                )

        return "\n".join(lines)

    # -- SARIF report -------------------------------------------------------

    @staticmethod
    def format_sarif(result: PipelineResult) -> str:
        """Generate a SARIF JSON report from a pipeline result."""
        sarif_results: List[Dict[str, Any]] = []

        for stage, output in result.stages.items():
            if output.is_error:
                sarif_results.append({
                    "ruleId": f"deppy/{stage.value}-error",
                    "level": "error",
                    "message": {"text": output.get("error", "Unknown error")},
                })

            for obl in output.obligations:
                status = obl.get("status", "pending")
                if status == "sorry":
                    sarif_results.append({
                        "ruleId": "deppy/sorry-obligation",
                        "level": "warning",
                        "message": {
                            "text": (
                                f"Obligation {obl.get('id', '?')}: "
                                f"{obl.get('description', 'sorry')}"
                            ),
                        },
                    })
                elif status == "failed":
                    sarif_results.append({
                        "ruleId": "deppy/failed-obligation",
                        "level": "error",
                        "message": {
                            "text": (
                                f"Obligation {obl.get('id', '?')}: "
                                f"{obl.get('description', 'failed')}"
                            ),
                        },
                    })

        for name, gr in result.gate_results.items():
            if not gr.passed:
                sarif_results.append({
                    "ruleId": f"deppy/gate-{name.lower()}",
                    "level": "warning",
                    "message": {
                        "text": f"Gate {name} failed: {'; '.join(gr.failures)}",
                    },
                })

        sarif = {
            "$schema": "https://json.schemastore.org/sarif-2.1.0.json",
            "version": "2.1.0",
            "runs": [{
                "tool": {
                    "driver": {
                        "name": "deppy-hybrid",
                        "version": "0.1.0",
                        "informationUri": "https://github.com/deppy/deppy",
                        "rules": [
                            {
                                "id": "deppy/sorry-obligation",
                                "shortDescription": {
                                    "text": "Proof obligation has sorry'd proof",
                                },
                                "defaultConfiguration": {"level": "warning"},
                            },
                            {
                                "id": "deppy/failed-obligation",
                                "shortDescription": {
                                    "text": "Proof obligation failed to discharge",
                                },
                                "defaultConfiguration": {"level": "error"},
                            },
                        ],
                    },
                },
                "results": sarif_results,
            }],
        }

        return json.dumps(sarif, indent=2)

    # -- HTML report --------------------------------------------------------

    @staticmethod
    def format_html_report(result: PipelineResult) -> str:
        """Generate an HTML report from a pipeline result."""
        trust_color = {
            "lean_verified": "#22c55e",
            "z3_proven": "#22c55e",
            "llm_judged": "#eab308",
            "runtime_checked": "#eab308",
            "untrusted": "#9ca3af",
            "contradicted": "#ef4444",
        }

        tc = trust_color.get(result.overall_trust, "#9ca3af")

        stages_html: List[str] = []
        for stage in PipelineStage.ordered():
            if stage in result.stages:
                out = result.stages[stage]
                sc = trust_color.get(out.trust_level, "#9ca3af")
                status = "ERROR" if out.is_error else out.trust_level
                stages_html.append(
                    f'<tr><td>{STAGE_NAMES[stage]}</td>'
                    f'<td style="color:{sc}">{status}</td>'
                    f'<td>{out.duration_ms:.1f}ms</td></tr>'
                )

        gates_html: List[str] = []
        for name, gr in result.gate_results.items():
            gc = "#22c55e" if gr.passed else "#ef4444"
            status = "PASS" if gr.passed else "FAIL"
            gates_html.append(
                f'<tr><td>{name}</td>'
                f'<td style="color:{gc}">{status}</td></tr>'
            )

        html = textwrap.dedent(f"""\
        <!DOCTYPE html>
        <html>
        <head>
            <title>Deppy Hybrid Verification Report</title>
            <style>
                body {{ font-family: system-ui, sans-serif; max-width: 800px;
                       margin: 2em auto; padding: 0 1em; }}
                h1 {{ color: {tc}; }}
                table {{ border-collapse: collapse; width: 100%; margin: 1em 0; }}
                th, td {{ border: 1px solid #e5e7eb; padding: 0.5em 1em;
                         text-align: left; }}
                th {{ background: #f9fafb; }}
                .meta {{ color: #6b7280; font-size: 0.9em; }}
            </style>
        </head>
        <body>
            <h1>Verification Report</h1>
            <p class="meta">
                Trust: <strong style="color:{tc}">{result.overall_trust}</strong>
                &nbsp;|&nbsp; H¹: {result.h1_status}
                &nbsp;|&nbsp; Duration: {result.total_duration_ms:.1f}ms
            </p>

            <h2>Stages</h2>
            <table>
                <tr><th>Stage</th><th>Trust</th><th>Time</th></tr>
                {''.join(stages_html)}
            </table>

            <h2>Gates</h2>
            <table>
                <tr><th>Gate</th><th>Result</th></tr>
                {''.join(gates_html)}
            </table>
        </body>
        </html>
        """)

        return html

# ---------------------------------------------------------------------------
# HybridCLI
# ---------------------------------------------------------------------------

class HybridCLI:
    """Command-line interface for the hybrid verification system.

    Subcommands::

        deppy hybrid verify <file.py>    Full pipeline on a file
        deppy hybrid check <file.py>     Structural + semantic checks (no Lean)
        deppy hybrid translate <file.py> Python → Lean translation only
        deppy hybrid discharge <file.lean> Discharge obligations in a Lean file
        deppy hybrid spec <text>         Parse NL spec to HybridSpec
        deppy hybrid status              Show current verification status
        deppy hybrid report              Generate HTML/SARIF report
    """

    def __init__(self, out: Optional[TextIO] = None) -> None:
        self._out = out or sys.stdout
        self._formatter = OutputFormatter()
        self._project_config: Optional[ProjectConfig] = None

    # -- Main entry point ---------------------------------------------------

    def run(self, args: Optional[List[str]] = None) -> int:
        """Parse *args* and dispatch to the appropriate subcommand.

        Returns 0 on success, non-zero on failure.
        """
        parser = self._build_parser()
        parsed = parser.parse_args(args)

        if not hasattr(parsed, "func"):
            parser.print_help(self._out)
            return 1

        # Load project config
        self._project_config = ProjectConfig.load()

        try:
            return parsed.func(parsed)
        except KeyboardInterrupt:
            self._print(f"\n{C.YELLOW}Interrupted{C.RESET}")
            return 130
        except Exception as exc:
            self._print(f"{C.RED}Error: {exc}{C.RESET}")
            return 1

    # -- Parser construction ------------------------------------------------

    def _build_parser(self) -> argparse.ArgumentParser:
        """Build the argparse parser with all subcommands."""
        parser = argparse.ArgumentParser(
            prog="deppy hybrid",
            description="Hybrid verification pipeline for Python",
            formatter_class=argparse.RawDescriptionHelpFormatter,
            epilog=textwrap.dedent("""\
                examples:
                  deppy hybrid verify mymodule.py
                  deppy hybrid check mymodule.py --strict
                  deppy hybrid translate mymodule.py -o output.lean
                  deppy hybrid spec "returns sorted list"
                  deppy hybrid status
                  deppy hybrid report --format html -o report.html
            """),
        )
        parser.add_argument(
            "--no-color", action="store_true",
            help="Disable coloured output",
        )
        parser.add_argument(
            "--json", action="store_true",
            help="Output results as JSON",
        )
        parser.add_argument(
            "-v", "--verbose", action="store_true",
            help="Verbose output",
        )

        sub = parser.add_subparsers(dest="command", help="Subcommand")

        # --- verify ---
        p_verify = sub.add_parser(
            "verify", help="Run full verification pipeline on a Python file",
        )
        p_verify.add_argument("file", help="Python source file")
        p_verify.add_argument(
            "--strict", action="store_true", default=None,
            help="Strict gate enforcement (default from config)",
        )
        p_verify.add_argument(
            "--permissive", action="store_true",
            help="Permissive mode: gates are advisory",
        )
        p_verify.add_argument(
            "--no-lean", action="store_true",
            help="Skip Lean translation and discharge",
        )
        p_verify.add_argument(
            "-o", "--output", help="Write result to file",
        )
        p_verify.set_defaults(func=self._cmd_verify)

        # --- check ---
        p_check = sub.add_parser(
            "check", help="Run structural + semantic checks (no Lean)",
        )
        p_check.add_argument("file", help="Python source file")
        p_check.add_argument(
            "--strict", action="store_true", default=None,
            help="Strict gate enforcement",
        )
        p_check.add_argument(
            "--structural-only", action="store_true",
            help="Only run structural (Z3) checks",
        )
        p_check.set_defaults(func=self._cmd_check)

        # --- translate ---
        p_translate = sub.add_parser(
            "translate", help="Translate Python to Lean 4",
        )
        p_translate.add_argument("file", help="Python source file")
        p_translate.add_argument(
            "-o", "--output", help="Output .lean file path",
        )
        p_translate.set_defaults(func=self._cmd_translate)

        # --- discharge ---
        p_discharge = sub.add_parser(
            "discharge", help="Discharge obligations in a Lean file",
        )
        p_discharge.add_argument("file", help="Lean source file")
        p_discharge.add_argument(
            "--max-attempts", type=int, default=3,
            help="Maximum discharge attempts per obligation",
        )
        p_discharge.set_defaults(func=self._cmd_discharge)

        # --- spec ---
        p_spec = sub.add_parser(
            "spec", help="Parse natural language to HybridSpec",
        )
        p_spec.add_argument("text", nargs="+", help="Natural language specification")
        p_spec.set_defaults(func=self._cmd_spec)

        # --- status ---
        p_status = sub.add_parser(
            "status", help="Show verification status of the project",
        )
        p_status.add_argument(
            "--dir", default=".", help="Project directory",
        )
        p_status.set_defaults(func=self._cmd_status)

        # --- report ---
        p_report = sub.add_parser(
            "report", help="Generate verification report",
        )
        p_report.add_argument(
            "--format", choices=["html", "sarif", "json"], default="html",
            help="Report format",
        )
        p_report.add_argument(
            "-o", "--output", help="Output file path",
        )
        p_report.add_argument(
            "--manifest", help="Path to pipeline manifest JSON",
        )
        p_report.set_defaults(func=self._cmd_report)

        return parser

    # -- Subcommand implementations -----------------------------------------

    def _cmd_verify(self, args: argparse.Namespace) -> int:
        """``deppy hybrid verify <file.py>``"""
        source = self._read_file(args.file)
        if source is None:
            return 1

        cfg = self._make_config(args)
        if getattr(args, "no_lean", False):
            cfg.emit_lean = False

        self._print(f"{C.BOLD}Verifying:{C.RESET} {args.file}")
        self._print("")

        orchestrator = PipelineOrchestrator(cfg)
        result = orchestrator.run_full(source, cfg)

        if getattr(args, "json", False):
            self._print(json.dumps(result.to_dict(), indent=2, default=str))
        else:
            self._print(OutputFormatter.format_pipeline_summary(result))

        if getattr(args, "output", None):
            self._write_output(args.output, result)

        return 0 if result.success else 1

    def _cmd_check(self, args: argparse.Namespace) -> int:
        """``deppy hybrid check <file.py>``"""
        source = self._read_file(args.file)
        if source is None:
            return 1

        self._print(f"{C.BOLD}Checking:{C.RESET} {args.file}")
        self._print("")

        # Run ideation + specification + structural (+ optional semantic)
        ideation = IdeationStage()
        ideation_out = ideation.run(source)
        claims = ideation_out.get("claims", [])

        spec_stage = SpecificationStage()
        spec_out = spec_stage.run(claims)

        structural_specs = spec_out.get("structural_specs", [])
        semantic_specs = spec_out.get("semantic_specs", [])

        # Structural checks
        struct_stage = StructuralCheckStage()
        struct_out = struct_stage.run(source, structural_specs)

        self._print(OutputFormatter.format_stage_detail(
            PipelineStage.STRUCTURAL_CHECK, struct_out
        ))

        # Semantic checks (unless structural-only)
        if not getattr(args, "structural_only", False) and semantic_specs:
            sem_stage = SemanticCheckStage()
            sem_out = sem_stage.run(source, semantic_specs)
            self._print("")
            self._print(OutputFormatter.format_stage_detail(
                PipelineStage.SEMANTIC_CHECK, sem_out
            ))

        return 0

    def _cmd_translate(self, args: argparse.Namespace) -> int:
        """``deppy hybrid translate <file.py>``"""
        source = self._read_file(args.file)
        if source is None:
            return 1

        self._print(f"{C.BOLD}Translating:{C.RESET} {args.file} → Lean 4")
        self._print("")

        # Run ideation + specification + translation
        ideation = IdeationStage()
        ideation_out = ideation.run(source)
        claims = ideation_out.get("claims", [])

        spec_stage = SpecificationStage()
        spec_out = spec_stage.run(claims)
        specs = spec_out.get("specs", [])

        lean_stage = LeanTranslationStage()
        lean_out = lean_stage.run(source, specs)

        lean_source = lean_out.get("lean_source", "")

        if getattr(args, "output", None):
            output_path = args.output
            with open(output_path, "w") as f:
                f.write(lean_source)
            self._print(f"{C.GREEN}Written to {output_path}{C.RESET}")
        else:
            self._print(lean_source)

        self._print("")
        self._print(OutputFormatter.format_stage_detail(
            PipelineStage.LEAN_TRANSLATION, lean_out
        ))

        return 0

    def _cmd_discharge(self, args: argparse.Namespace) -> int:
        """``deppy hybrid discharge <file.lean>``"""
        source = self._read_file(args.file)
        if source is None:
            return 1

        self._print(f"{C.BOLD}Discharging:{C.RESET} {args.file}")
        self._print("")

        # Parse sorry'd theorems from Lean file
        import re
        sorry_pattern = re.compile(
            r"theorem\s+(\w+).*?:=\s*by\s*\n\s*sorry", re.DOTALL
        )
        matches = sorry_pattern.findall(source)

        obligations: List[Dict[str, Any]] = []
        for name in matches:
            obligations.append({
                "id": f"lean_{name}",
                "kind": "lean_theorem",
                "theorem": name,
                "status": "sorry",
                "description": f"Theorem {name} has sorry'd proof",
            })

        if not obligations:
            self._print(f"{C.GREEN}No sorry'd obligations found.{C.RESET}")
            return 0

        self._print(f"Found {len(obligations)} sorry'd obligation(s)")

        max_attempts = getattr(args, "max_attempts", 3)
        discharge_stage = DischargeStage(max_attempts=max_attempts)
        discharge_out = discharge_stage.run(obligations)

        self._print("")
        self._print(OutputFormatter.format_stage_detail(
            PipelineStage.DISCHARGE, discharge_out
        ))

        return 0

    def _cmd_spec(self, args: argparse.Namespace) -> int:
        """``deppy hybrid spec <text>``"""
        text = " ".join(args.text)

        self._print(f"{C.BOLD}Parsing spec:{C.RESET} {text}")
        self._print("")

        ideation = IdeationStage()
        ideation_out = ideation.run(text)
        claims = ideation_out.get("claims", [])

        spec_stage = SpecificationStage()
        spec_out = spec_stage.run(claims)

        if getattr(args, "json", False):
            self._print(json.dumps(spec_out.to_dict(), indent=2, default=str))
        else:
            self._print(OutputFormatter.format_stage_detail(
                PipelineStage.IDEATION, ideation_out
            ))
            self._print("")
            self._print(OutputFormatter.format_stage_detail(
                PipelineStage.SPECIFICATION, spec_out
            ))

        return 0

    def _cmd_status(self, args: argparse.Namespace) -> int:
        """``deppy hybrid status``"""
        project_dir = getattr(args, "dir", ".")

        self._print(f"{C.BOLD}Project Status{C.RESET}")
        self._print("─" * 40)

        # Find Python files
        py_files: List[str] = []
        for root, _dirs, files in os.walk(project_dir):
            for f in files:
                if f.endswith(".py") and not f.startswith("_"):
                    py_files.append(os.path.join(root, f))

        self._print(f"  Python files: {len(py_files)}")

        # Look for existing manifests
        manifest_count = 0
        cache_dir = self._project_config.cache_dir if self._project_config else None
        if cache_dir and os.path.isdir(cache_dir):
            for f in os.listdir(cache_dir):
                if f.endswith(".json"):
                    manifest_count += 1

        self._print(f"  Cached results: {manifest_count}")

        # Look for Lean files
        lean_files: List[str] = []
        for root, _dirs, files in os.walk(project_dir):
            for f in files:
                if f.endswith(".lean"):
                    lean_files.append(os.path.join(root, f))

        self._print(f"  Lean files: {len(lean_files)}")

        # Config
        self._print("")
        self._print(f"{C.BOLD}Configuration:{C.RESET}")
        if self._project_config:
            self._print(f"  Oracle model: {self._project_config.oracle_model}")
            self._print(f"  Z3 timeout:   {self._project_config.z3_timeout_ms}ms")
            self._print(f"  Strict gates: {self._project_config.strict_gates}")
            self._print(f"  Emit Lean:    {self._project_config.emit_lean}")
        else:
            self._print(f"  {C.DIM}(using defaults){C.RESET}")

        # Pipeline stages
        self._print("")
        self._print(f"{C.BOLD}Pipeline Stages:{C.RESET}")
        for info in list_stages():
            self._print(f"  {info['order']}. {info['name']:<22s} ({info['class']})")

        return 0

    def _cmd_report(self, args: argparse.Namespace) -> int:
        """``deppy hybrid report``"""
        fmt = getattr(args, "format", "html")
        manifest_path = getattr(args, "manifest", None)

        # Try to load a manifest
        if manifest_path and os.path.isfile(manifest_path):
            manifest = PipelineManifest.load(manifest_path)
            self._print(manifest.summary_text())
        else:
            self._print(
                f"{C.YELLOW}No manifest found. Run 'deppy hybrid verify' "
                f"first.{C.RESET}"
            )
            self._print("")
            self._print("Generating empty report template...")

            # Create a minimal result for reporting
            result = PipelineResult()

            if fmt == "sarif":
                content = OutputFormatter.format_sarif(result)
            elif fmt == "html":
                content = OutputFormatter.format_html_report(result)
            else:
                content = json.dumps(result.to_dict(), indent=2, default=str)

            output_path = getattr(args, "output", None)
            if output_path:
                with open(output_path, "w") as f:
                    f.write(content)
                self._print(f"{C.GREEN}Report written to {output_path}{C.RESET}")
            else:
                self._print(content)

        return 0

    # -- Helpers ------------------------------------------------------------

    def _read_file(self, path: str) -> Optional[str]:
        """Read a source file, returning None on error."""
        if not os.path.isfile(path):
            self._print(f"{C.RED}File not found: {path}{C.RESET}")
            return None
        try:
            with open(path) as f:
                return f.read()
        except OSError as exc:
            self._print(f"{C.RED}Cannot read {path}: {exc}{C.RESET}")
            return None

    def _make_config(self, args: argparse.Namespace) -> PipelineConfig:
        """Build a PipelineConfig from CLI args + project config."""
        if self._project_config:
            cfg = self._project_config.to_pipeline_config()
        else:
            cfg = PipelineConfig.default()

        if getattr(args, "permissive", False):
            cfg.strict_gates = False
        elif getattr(args, "strict", None) is True:
            cfg.strict_gates = True

        return cfg

    def _write_output(self, path: str, result: PipelineResult) -> None:
        """Write pipeline result to a file."""
        data = result.to_dict()
        with open(path, "w") as f:
            json.dump(data, f, indent=2, default=str)
        self._print(f"\n{C.GREEN}Result written to {path}{C.RESET}")

    def _print(self, text: str = "") -> None:
        """Print to the configured output stream."""
        print(text, file=self._out)

# ---------------------------------------------------------------------------
# Module entry point
# ---------------------------------------------------------------------------

def main(args: Optional[List[str]] = None) -> int:
    """Entry point for ``deppy hybrid`` CLI."""
    cli = HybridCLI()
    return cli.run(args)

if __name__ == "__main__":
    sys.exit(main())
