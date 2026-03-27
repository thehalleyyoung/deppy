"""Command implementations for the DepPy CLI.

Each command class handles a specific subcommand:
- CheckCommand: Run sheaf-descent analysis and report diagnostics.
- ExplainCommand: Explain the analysis for a specific site or scope.
- ProveCommand: Attempt to prove a specific property.
- GenerateCommand: Generate contract annotations from analysis.
- WatchCommand: Watch files for changes and re-analyze.
"""

from __future__ import annotations

from collections import Counter
from html import escape as _html_escape
import json
import os
import sys
import time
from abc import ABC, abstractmethod
from pathlib import Path
from typing import (
    Any,
    Dict,
    List,
    Optional,
    Sequence,
    Set,
    TextIO,
    Tuple,
)

from deppy.core._protocols import SiteId, SiteKind, TrustLevel
from deppy.pipeline.pipeline import AnalysisPipeline, PipelineHooks, PipelineResult
from deppy.pipeline.pipeline_config import PipelineConfig, OutputFormat, Verbosity
from deppy.pipeline.stages.render_stage import (
    ContractAnnotation,
    Diagnostic,
    DiagnosticSeverity,
)
from deppy.cli.config import CLIConfig
from deppy.cli.formatters import (
    Formatter,
    TerminalFormatter,
    PlainFormatter,
    JsonFormatter,
    create_formatter,
)
from deppy.scan_scope import iter_default_python_files

try:
    from deppy.hybrid.diagnostics.localization import (
        DiagnosticFormatter as _HybridDiagnosticFormatter,
        ExistingCodeChecker as _HybridExistingCodeChecker,
    )
except ImportError:
    _HybridDiagnosticFormatter = None
    _HybridExistingCodeChecker = None

# ===================================================================
#  Command base
# ===================================================================


class Command(ABC):
    """Base class for CLI commands."""

    @abstractmethod
    def run(self, cli_config: CLIConfig) -> int:
        """Execute the command and return an exit code (0 = success)."""
        ...

    def _create_pipeline(self, cli_config: CLIConfig) -> AnalysisPipeline:
        """Create an AnalysisPipeline from CLI config."""
        pipeline_config = cli_config.to_pipeline_config()
        formatter = create_formatter(
            cli_config.output_format, color=cli_config.color
        )

        hooks = PipelineHooks(
            _on_stage_start=self._make_stage_start_hook(formatter, cli_config),
            _on_stage_complete=self._make_stage_complete_hook(formatter, cli_config),
        )

        return AnalysisPipeline(config=pipeline_config, hooks=hooks)

    def _create_formatter(self, cli_config: CLIConfig) -> Formatter:
        return create_formatter(cli_config.output_format, color=cli_config.color)

    @staticmethod
    def _make_stage_start_hook(
        formatter: Formatter, cli_config: CLIConfig
    ) -> Optional[Any]:
        if cli_config.verbosity >= 2:
            def _hook(name: str) -> None:
                msg = formatter.format_progress(name, "running")
                print(msg, file=sys.stderr)
            return _hook
        return None

    @staticmethod
    def _make_stage_complete_hook(
        formatter: Formatter, cli_config: CLIConfig
    ) -> Optional[Any]:
        if cli_config.verbosity >= 2:
            def _hook(name: str, elapsed: float) -> None:
                msg = formatter.format_progress(name, "done")
                print(msg, file=sys.stderr)
            return _hook
        return None

    def _resolve_source_files(self, cli_config: CLIConfig) -> List[str]:
        """Resolve source file paths from CLI config."""
        files: List[str] = []
        for path_str in cli_config.source_paths:
            path = Path(path_str)
            if path.is_file():
                files.append(str(path.resolve()))
            elif path.is_dir():
                for py_file in iter_default_python_files(path):
                    files.append(str(py_file))
            else:
                print(f"Warning: {path_str} not found", file=sys.stderr)
        return files

    def _print_result(
        self,
        result: PipelineResult,
        formatter: Formatter,
        cli_config: CLIConfig,
        stream: TextIO = sys.stdout,
    ) -> None:
        """Print the pipeline result using the formatter."""
        output = formatter.format_result(result)
        print(output, file=stream)


# ===================================================================
#  CheckCommand
# ===================================================================


class CheckCommand(Command):
    """Run sheaf-descent analysis on source files and report diagnostics.

    This is the primary command.  It runs the full analysis pipeline
    and reports obstructions, warnings, and inferred contracts.
    """

    def run(self, cli_config: CLIConfig) -> int:
        """Execute the check command.

        Returns 0 on success, 1 if errors were found, 2 on failure.
        """
        files = self._resolve_source_files(cli_config)
        if not files:
            print("No source files to analyze.", file=sys.stderr)
            return 2

        if (
            _HybridExistingCodeChecker is not None
            and _HybridDiagnosticFormatter is not None
        ):
            return self._run_hybrid_check(files, cli_config)

        pipeline = self._create_pipeline(cli_config)
        formatter = self._create_formatter(cli_config)
        html_mode = cli_config.output_format == "html"

        total_errors = 0
        total_warnings = 0
        all_results: List[PipelineResult] = []

        for file_path in files:
            if cli_config.verbosity >= 1:
                print(f"Analyzing {file_path}...", file=sys.stderr)

            result = pipeline.run(file_path)
            all_results.append(result)

            if not html_mode:
                for diag in result.diagnostics:
                    formatted = formatter.format_diagnostic(diag)
                    if diag.severity == DiagnosticSeverity.ERROR:
                        print(formatted, file=sys.stderr)
                    else:
                        print(formatted, file=sys.stdout)

            total_errors += result.error_count
            total_warnings += result.warning_count

        if html_mode:
            report_path = self._write_report(
                self._render_pipeline_html_report(files, all_results),
                cli_config,
                default_name="deppy-report.html",
            )
            print(f"Wrote HTML report to {report_path}", file=sys.stdout)
        else:
            if len(files) > 1:
                self._print_multi_file_summary(
                    files, all_results, formatter, cli_config
                )
            elif all_results:
                summary = formatter.format_summary(all_results[0])
                print(summary, file=sys.stdout)

            if cli_config.verbosity >= 1:
                for result in all_results:
                    if result.contracts:
                        contracts_str = formatter.format_contracts(result.contracts)
                        if contracts_str:
                            print(contracts_str, file=sys.stdout)

        if total_errors > 0:
            return 1
        return 0

    def _run_hybrid_check(self, files: List[str], cli_config: CLIConfig) -> int:
        """Run the zero-change hybrid checker on existing code."""
        checker = _HybridExistingCodeChecker(
            include_h1_names=cli_config.verbosity >= 3
        )
        formatter = _HybridDiagnosticFormatter(
            show_detail=cli_config.verbosity >= 2,
            show_fix=cli_config.verbosity >= 1,
            show_trust=cli_config.verbosity >= 1,
            colour=cli_config.color and cli_config.output_format != "plain",
        )

        results = []
        all_diagnostics = []
        error_files = 0

        for file_path in files:
            if cli_config.verbosity >= 1:
                print(f"Checking {file_path}...", file=sys.stderr)

            result = checker.check_file(file_path)
            results.append(result)
            all_diagnostics.extend(result.diagnostics)
            if result.has_errors():
                error_files += 1

            if cli_config.output_format in {"terminal", "plain"}:
                rendered = formatter.format_terminal(result.diagnostics)
                print(rendered, file=sys.stdout, end="")
                print(result.summary(), file=sys.stdout)

        if cli_config.output_format == "json":
            print(
                json.dumps([result.to_dict() for result in results], indent=2),
                file=sys.stdout,
            )
        elif cli_config.output_format == "sarif":
            print(
                json.dumps(formatter.format_sarif(all_diagnostics), indent=2),
                file=sys.stdout,
            )
        elif cli_config.output_format == "html":
            report_path = self._write_report(
                self._render_hybrid_html_report(results),
                cli_config,
                default_name="deppy-report.html",
            )
            print(f"Wrote HTML report to {report_path}", file=sys.stdout)
        elif len(results) > 1:
            total_h1 = sum(result.h1_dimension for result in results)
            total_issues = sum(len(result.diagnostics) for result in results)
            print(f"\nSummary ({len(results)} files):", file=sys.stdout)
            print(f"  Files with errors: {error_files}", file=sys.stdout)
            print(f"  Issues: {total_issues}", file=sys.stdout)
            print(f"  H¹ dimension: {total_h1}", file=sys.stdout)

        return 1 if error_files else 0

    def _write_report(
        self,
        content: str,
        cli_config: CLIConfig,
        *,
        default_name: str,
    ) -> Path:
        output_name = getattr(cli_config, "generate_output", None) or default_name
        output_path = Path(output_name).expanduser()
        if not output_path.is_absolute():
            output_path = (Path.cwd() / output_path).resolve()
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(content, encoding="utf-8")
        return output_path

    @staticmethod
    def _issue_code_family(code: str) -> str:
        parts = code.split("-")
        return parts[1] if len(parts) >= 3 else ""

    @classmethod
    def _warning_likelihood(
        cls,
        *,
        severity: str,
        code: str,
        trust_level: Optional[str] = None,
    ) -> str:
        if severity != "warning":
            return ""
        family = cls._issue_code_family(code)
        trust = trust_level or ""
        if family == "SC" or trust in {"Z3_PROVEN", "LEAN_VERIFIED"}:
            return "high"
        if family == "IS" and trust in {"LLM_JUDGED", "UNTRUSTED", ""}:
            return "low"
        return "medium"

    @classmethod
    def _hybrid_issue_score(cls, diag: Any) -> int:
        severity_weight = {
            "error": 3000,
            "warning": 1500,
            "info": 400,
            "hint": 200,
        }
        trust_weight = {
            "LEAN_VERIFIED": 500,
            "Z3_PROVEN": 420,
            "PROPERTY_CHECKED": 320,
            "RUNTIME_CHECKED": 250,
            "LLM_JUDGED": 120,
            "UNTRUSTED": 40,
        }
        family_weight = {
            "SC": 350,
            "IC": 260,
            "IS": -180,
        }
        severity = getattr(diag.severity, "value", "warning")
        family = cls._issue_code_family(getattr(diag, "code", ""))
        trust = getattr(diag, "trust_level", "")
        score = severity_weight.get(severity, 0)
        score += trust_weight.get(trust, 0)
        score += family_weight.get(family, 0)
        score += min(len(getattr(diag, "detail", "") or ""), 400) // 20
        return score

    @staticmethod
    def _describe_issue_group_count(count: int) -> str:
        return f"{count} issue group{'s' if count != 1 else ''}"

    @staticmethod
    def _trust_display_label(trust_level: str) -> str:
        labels = {
            "LEAN_VERIFIED": "Lean proof",
            "Z3_PROVEN": "Z3/SMT proof",
            "PROPERTY_CHECKED": "Property test",
            "RUNTIME_CHECKED": "Runtime check",
            "LLM_JUDGED": "LLM semantic check",
            "UNTRUSTED": "Heuristic signal",
        }
        return labels.get(trust_level, trust_level.replace("_", " ").title())

    @classmethod
    def _render_hybrid_evidence_panel(cls, trust_counts: Counter[str]) -> str:
        llm_count = trust_counts.get("LLM_JUDGED", 0)
        z3_count = trust_counts.get("Z3_PROVEN", 0)
        lean_count = trust_counts.get("LEAN_VERIFIED", 0)
        property_count = trust_counts.get("PROPERTY_CHECKED", 0)
        runtime_count = trust_counts.get("RUNTIME_CHECKED", 0)
        heuristic_count = trust_counts.get("UNTRUSTED", 0)

        summary_bits = []
        for trust_level in (
            "LLM_JUDGED",
            "Z3_PROVEN",
            "PROPERTY_CHECKED",
            "RUNTIME_CHECKED",
            "LEAN_VERIFIED",
            "UNTRUSTED",
        ):
            count = trust_counts.get(trust_level, 0)
            if count:
                summary_bits.append(
                    f"<li><strong>{count}</strong> × {cls._trust_display_label(trust_level)}</li>"
                )
        summary_list = (
            "<ul>" + "".join(summary_bits) + "</ul>"
            if summary_bits
            else "<p class=\"empty-state\">No issues found.</p>"
        )

        if llm_count and z3_count:
            run_summary = (
                "This report includes both LLM-guided semantic findings and "
                "Z3-backed structural findings."
            )
        elif z3_count:
            run_summary = (
                "This report is dominated by solver-backed findings. The issues shown "
                "here have Z3 support."
            )
        elif llm_count:
            run_summary = (
                "This report is dominated by LLM-guided semantic findings. These are "
                "useful for docstring and intent mismatches, but they are not Z3 proofs."
            )
        else:
            run_summary = (
                "This report uses the same mixed checker, but none of the current "
                "findings are tagged as LLM-guided or Z3-backed."
            )

        absent_bits = []
        if not z3_count:
            absent_bits.append("No Z3-backed findings appeared in this run.")
        if not llm_count:
            absent_bits.append("No LLM-guided semantic findings appeared in this run.")
        absent_note = (
            f"<p class=\"note\">{' '.join(absent_bits)}</p>"
            if absent_bits
            else ""
        )

        engines = []
        if llm_count:
            engines.append("LLM semantic checks")
        if z3_count:
            engines.append("Z3/SMT proofs")
        if property_count:
            engines.append("property tests")
        if runtime_count:
            engines.append("runtime checks")
        if lean_count:
            engines.append("Lean proofs")
        if heuristic_count:
            engines.append("heuristic signals")
        engine_line = ", ".join(engines) if engines else "no issue evidence"

        return (
            "<section class=\"panel\">\n"
            "  <h2>Evidence sources</h2>\n"
            "  <p>Deppy can combine LLM-guided semantic checks with solver-backed checks. "
            "Each issue card shows the primary evidence for that finding, not the full set "
            "of engines available in the system.</p>\n"
            f"  <p>{_html_escape(run_summary)}</p>\n"
            f"  <p class=\"note\">This run contains: {_html_escape(engine_line)}.</p>\n"
            f"  {summary_list}\n"
            f"  {absent_note}\n"
            "</section>\n"
        )

    @classmethod
    def _pipeline_issue_score(cls, diag: Diagnostic) -> int:
        severity_weight = {
            "error": 3000,
            "warning": 1500,
            "info": 400,
            "hint": 200,
        }
        family_weight = {
            "SC": 350,
            "IC": 260,
            "IS": -180,
        }
        severity = diag.severity.value
        family = cls._issue_code_family(diag.code or "")
        score = severity_weight.get(severity, 0)
        score += family_weight.get(family, 0)
        score += min(len(diag.message or ""), 200) // 20
        return score

    def _render_hybrid_html_report(self, results: Sequence[Any]) -> str:
        issue_results = [result for result in results if result.diagnostics]
        ranked_results = sorted(
            issue_results,
            key=lambda result: (
                max((self._hybrid_issue_score(diag) for diag in result.diagnostics), default=0),
                len(result.diagnostics),
                result.h1_dimension,
            ),
            reverse=True,
        )
        all_diagnostics = sorted(
            (
                diag
                for result in ranked_results
                for diag in result.diagnostics
            ),
            key=self._hybrid_issue_score,
            reverse=True,
        )
        error_count = sum(1 for diag in all_diagnostics if diag.is_error())
        warning_count = sum(1 for diag in all_diagnostics if diag.is_warning())
        info_count = len(all_diagnostics) - error_count - warning_count
        total_h1 = sum(result.h1_dimension for result in ranked_results)
        code_counts = Counter(
            diag.code for diag in all_diagnostics if getattr(diag, "code", "")
        )
        trust_counts: Counter[str] = Counter(
            getattr(diag, "trust_level", "") or "UNTRUSTED"
            for diag in all_diagnostics
        )
        likely_low_signal = [
            diag
            for diag in all_diagnostics
            if diag.code.startswith("DEPPY-IS-") and diag.trust_level == "LLM_JUDGED"
        ]
        file_rows = []
        detail_sections = []
        for result in ranked_results:
            file_errors = sum(1 for diag in result.diagnostics if diag.is_error())
            file_warnings = sum(1 for diag in result.diagnostics if diag.is_warning())
            file_infos = len(result.diagnostics) - file_errors - file_warnings
            file_rows.append(
                "<tr>"
                f"<td>{_html_escape(result.file_path)}</td>"
                f"<td>{len(result.diagnostics)}</td>"
                f"<td>{file_errors}</td>"
                f"<td>{file_warnings}</td>"
                f"<td>{file_infos}</td>"
                f"<td>{result.h1_dimension}</td>"
                "</tr>"
            )
            ranked_file_diagnostics = sorted(
                result.diagnostics,
                key=self._hybrid_issue_score,
                reverse=True,
            )
            cards = "\n".join(
                self._render_hybrid_diagnostic_card(diag)
                for diag in ranked_file_diagnostics
            )
            detail_sections.append(
                "<section class=\"file-section\">"
                f"<h2>{_html_escape(result.file_path)}</h2>"
                f"<p class=\"file-summary\">"
                f"{file_errors} errors, {file_warnings} warnings, {file_infos} info/hints"
                f" across {self._describe_issue_group_count(result.h1_dimension)}."
                f"</p>"
                f"{cards}"
                "</section>"
            )

        code_rows = "\n".join(
            "<tr>"
            f"<td>{_html_escape(code)}</td>"
            f"<td>{count}</td>"
            "</tr>"
            for code, count in code_counts.most_common(12)
        )
        if not code_rows:
            code_rows = '<tr><td colspan="2">No issues found.</td></tr>'
        top_issue_cards = "\n".join(
            self._render_hybrid_diagnostic_card(diag)
            for diag in all_diagnostics[:25]
        )
        top_issue_section = (
            "<section class=\"panel\">\n"
            "  <h2>Most likely issues</h2>\n"
            f"{top_issue_cards}\n"
            "</section>\n"
            if top_issue_cards
            else "<section class=\"panel\">\n"
            "  <h2>Overview</h2>\n"
            "  <p class=\"empty-state\">No issues found.</p>\n"
            "</section>\n"
        )

        return (
            "<!DOCTYPE html>\n"
            "<html lang=\"en\">\n"
            "<head>\n"
            "  <meta charset=\"utf-8\">\n"
            "  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n"
            "  <title>deppy check dashboard</title>\n"
            "  <style>\n"
            "    body { margin: 0; font-family: Inter, -apple-system, BlinkMacSystemFont, sans-serif; background: #0b1020; color: #e8ecf3; }\n"
            "    main { max-width: 1240px; margin: 0 auto; padding: 32px 24px 56px; }\n"
            "    h1, h2, h3 { margin: 0 0 12px; }\n"
            "    p { line-height: 1.5; }\n"
            "    .hero { margin-bottom: 24px; }\n"
            "    .hero p { color: #aab4c8; max-width: 70ch; }\n"
            "    .grid { display: grid; gap: 16px; grid-template-columns: repeat(auto-fit, minmax(180px, 1fr)); margin: 20px 0 24px; }\n"
            "    .stat { background: #121a30; border: 1px solid #24304f; border-radius: 12px; padding: 16px; }\n"
            "    .stat .label { display: block; color: #91a0bd; font-size: 0.9rem; margin-bottom: 6px; }\n"
            "    .stat .value { font-size: 1.9rem; font-weight: 700; }\n"
            "    .panel { background: #121a30; border: 1px solid #24304f; border-radius: 14px; padding: 18px; margin-bottom: 22px; }\n"
            "    table { width: 100%; border-collapse: collapse; }\n"
            "    th, td { text-align: left; padding: 10px 12px; border-bottom: 1px solid #24304f; vertical-align: top; }\n"
            "    th { color: #8fa1c8; font-size: 0.86rem; text-transform: uppercase; letter-spacing: 0.04em; }\n"
            "    .note { color: #aab4c8; margin-top: 8px; }\n"
            "    .file-section { margin-bottom: 28px; }\n"
            "    .file-summary { color: #9eacc8; margin-bottom: 14px; }\n"
            "    .diag-card { background: #0f1629; border: 1px solid #263253; border-left-width: 5px; border-radius: 12px; padding: 14px 16px; margin-bottom: 14px; }\n"
            "    .diag-card.error { border-left-color: #f87171; }\n"
            "    .diag-card.warning { border-left-color: #fbbf24; }\n"
            "    .diag-card.warning.warning-high { background: #3a1616; border-left-color: #ef4444; }\n"
            "    .diag-card.warning.warning-medium { background: #3b230f; border-left-color: #f97316; }\n"
            "    .diag-card.warning.warning-low { background: #3a3113; border-left-color: #eab308; }\n"
            "    .diag-card.info { border-left-color: #60a5fa; }\n"
            "    .diag-card.hint { border-left-color: #34d399; }\n"
            "    .diag-meta { display: flex; flex-wrap: wrap; gap: 8px; align-items: center; margin-bottom: 10px; }\n"
            "    .badge { display: inline-flex; align-items: center; border-radius: 999px; padding: 3px 10px; font-size: 0.8rem; font-weight: 600; }\n"
            "    .severity-error { background: rgba(248, 113, 113, 0.15); color: #fca5a5; }\n"
            "    .severity-warning { background: rgba(251, 191, 36, 0.16); color: #fcd34d; }\n"
            "    .severity-info { background: rgba(96, 165, 250, 0.16); color: #93c5fd; }\n"
            "    .severity-hint { background: rgba(52, 211, 153, 0.16); color: #6ee7b7; }\n"
            "    .likelihood-high { background: rgba(239, 68, 68, 0.18); color: #fca5a5; }\n"
            "    .likelihood-medium { background: rgba(249, 115, 22, 0.18); color: #fdba74; }\n"
            "    .likelihood-low { background: rgba(234, 179, 8, 0.18); color: #fde68a; }\n"
            "    .trust { background: rgba(148, 163, 184, 0.15); color: #cbd5e1; }\n"
            "    .trust.llm-judged { background: rgba(245, 158, 11, 0.16); color: #fcd34d; }\n"
            "    .trust.z3-proven { background: rgba(96, 165, 250, 0.16); color: #93c5fd; }\n"
            "    .trust.property-checked { background: rgba(52, 211, 153, 0.16); color: #6ee7b7; }\n"
            "    .location { color: #93c5fd; font-family: ui-monospace, SFMono-Regular, monospace; }\n"
            "    .diag-title { font-size: 1.05rem; margin: 6px 0 8px; }\n"
            "    .diag-detail, .diag-code, .diag-fix { margin-top: 10px; }\n"
            "    pre { white-space: pre-wrap; word-break: break-word; background: #0a1020; border: 1px solid #24304f; border-radius: 10px; padding: 12px; color: #cbd5e1; }\n"
            "    code { font-family: ui-monospace, SFMono-Regular, monospace; }\n"
            "    .empty-state { color: #91a0bd; }\n"
            "  </style>\n"
            "</head>\n"
            "<body>\n"
            "<main>\n"
            "<section class=\"hero\">\n"
            "  <h1>deppy check dashboard</h1>\n"
            "  <p>This static dashboard hides clean files, ranks findings by likely actionability, and shades warnings by likelihood so the strongest signals rise first.</p>\n"
            "</section>\n"
            "<section class=\"grid\">\n"
            f"  <div class=\"stat\"><span class=\"label\">Files with issues</span><span class=\"value\">{len(ranked_results)}</span></div>\n"
            f"  <div class=\"stat\"><span class=\"label\">Issues</span><span class=\"value\">{len(all_diagnostics)}</span></div>\n"
            f"  <div class=\"stat\"><span class=\"label\">Errors</span><span class=\"value\">{error_count}</span></div>\n"
            f"  <div class=\"stat\"><span class=\"label\">Warnings</span><span class=\"value\">{warning_count}</span></div>\n"
            f"  <div class=\"stat\"><span class=\"label\">Info / hints</span><span class=\"value\">{info_count}</span></div>\n"
            f"  <div class=\"stat\"><span class=\"label\">Independent issue groups</span><span class=\"value\">{total_h1}</span></div>\n"
            "</section>\n"
            "<section class=\"panel\">\n"
            "  <h2>Signal quality</h2>\n"
            f"  <p><strong>{len(likely_low_signal)}</strong> diagnostics look like likely low-signal heuristic intent warnings (`DEPPY-IS-*` + `LLM_JUDGED`). These are the first candidates to down-rank or hide by default when you want a bug-focused view.</p>\n"
            "</section>\n"
            f"{self._render_hybrid_evidence_panel(trust_counts)}"
            "<section class=\"panel\">\n"
            "  <h2>Likelihood legend</h2>\n"
            "  <p><span class=\"badge likelihood-high\">High-likelihood warning</span> proof-backed or structurally strong warning</p>\n"
            "  <p><span class=\"badge likelihood-medium\">Medium-likelihood warning</span> mixed evidence that still deserves review</p>\n"
            "  <p><span class=\"badge likelihood-low\">Low-likelihood warning</span> heuristic/docstring-heavy signal likely to include false positives</p>\n"
            "</section>\n"
            f"{top_issue_section}"
            "<section class=\"panel\">\n"
            "  <h2>Files</h2>\n"
            "  <table><thead><tr><th>File</th><th>Issues</th><th>Errors</th><th>Warnings</th><th>Info</th><th>Groups</th></tr></thead><tbody>\n"
            f"{''.join(file_rows)}\n"
            "  </tbody></table>\n"
            "</section>\n"
            "<section class=\"panel\">\n"
            "  <h2>Top diagnostic codes</h2>\n"
            "  <table><thead><tr><th>Code</th><th>Count</th></tr></thead><tbody>\n"
            f"{code_rows}\n"
            "  </tbody></table>\n"
            "  <p class=\"note\">A high share of repeated `DEPPY-IS-*` warnings usually indicates documentation/intent heuristics outrunning structural or code-level bug evidence.</p>\n"
            "</section>\n"
            "<section class=\"panel\">\n"
            "  <h2>Diagnostics by file</h2>\n"
            f"{''.join(detail_sections)}\n"
            "</section>\n"
            "</main>\n"
            "</body>\n"
            "</html>\n"
        )

    def _render_hybrid_diagnostic_card(self, diag: Any) -> str:
        severity = diag.severity.value
        trust_class = diag.trust_level.lower().replace("_", "-")
        trust_label = self._trust_display_label(diag.trust_level)
        warning_likelihood = self._warning_likelihood(
            severity=severity,
            code=diag.code,
            trust_level=diag.trust_level,
        )
        card_class = f"diag-card {severity}"
        likelihood_badge = ""
        if warning_likelihood:
            card_class += f" warning-{warning_likelihood}"
            likelihood_badge = (
                f"<span class=\"badge likelihood-{warning_likelihood}\">"
                f"{_html_escape(warning_likelihood.title())} likelihood"
                "</span>"
            )
        detail_html = (
            f"<div class=\"diag-detail\"><strong>Why:</strong><pre>{_html_escape(diag.detail)}</pre></div>"
            if diag.detail
            else ""
        )
        code_html = (
            f"<div class=\"diag-code\"><strong>Code:</strong><pre>{_html_escape(diag.code_fragment)}</pre></div>"
            if diag.code_fragment
            else ""
        )
        intent_html = (
            f"<div class=\"diag-detail\"><strong>Intent:</strong> {_html_escape(diag.intent_fragment)}</div>"
            if diag.intent_fragment
            else ""
        )
        fix_html = ""
        if diag.suggested_fix is not None:
            fix_html = (
                "<div class=\"diag-fix\">"
                f"<strong>Suggested fix:</strong> {_html_escape(diag.suggested_fix.description)} "
                f"({_html_escape(f'{diag.suggested_fix.confidence:.0%}')} / {_html_escape(diag.suggested_fix.provenance)})"
                "</div>"
            )
        return (
            f"<article class=\"{card_class}\">"
            "<div class=\"diag-meta\">"
            f"<span class=\"badge severity-{severity}\">{_html_escape(severity.upper())}</span>"
            f"{likelihood_badge}"
            f"<span class=\"badge trust {trust_class}\" title=\"{_html_escape(diag.trust_level)}\">{_html_escape(trust_label)}</span>"
            f"<span class=\"badge\">{_html_escape(diag.code)}</span>"
            f"<span class=\"location\">{_html_escape(diag.location_str)}</span>"
            "</div>"
            f"<h3 class=\"diag-title\">{_html_escape(diag.message)}</h3>"
            f"{intent_html}"
            f"{detail_html}"
            f"{code_html}"
            f"{fix_html}"
            "</article>"
        )

    def _render_pipeline_html_report(
        self,
        files: Sequence[str],
        results: Sequence[PipelineResult],
    ) -> str:
        issue_results = [
            (file_path, result)
            for file_path, result in zip(files, results)
            if result.diagnostics
        ]
        issue_results.sort(
            key=lambda item: (
                max((self._pipeline_issue_score(diag) for diag in item[1].diagnostics), default=0),
                item[1].error_count,
                item[1].warning_count,
            ),
            reverse=True,
        )
        diagnostics = sorted([
            (file_path, diag)
            for file_path, result in issue_results
            for diag in result.diagnostics
        ], key=lambda item: self._pipeline_issue_score(item[1]), reverse=True)
        error_count = sum(1 for _, diag in diagnostics if diag.severity == DiagnosticSeverity.ERROR)
        warning_count = sum(1 for _, diag in diagnostics if diag.severity == DiagnosticSeverity.WARNING)
        info_count = len(diagnostics) - error_count - warning_count
        file_rows = []
        detail_sections = []
        for file_path, result in issue_results:
            file_rows.append(
                "<tr>"
                f"<td>{_html_escape(file_path)}</td>"
                f"<td>{len(result.diagnostics)}</td>"
                f"<td>{result.error_count}</td>"
                f"<td>{result.warning_count}</td>"
                f"<td>{result.obstruction_count}</td>"
                "</tr>"
            )
            cards = []
            for diag in sorted(result.diagnostics, key=self._pipeline_issue_score, reverse=True):
                severity = diag.severity.value
                location = diag.location.pretty() if diag.location else file_path
                warning_likelihood = self._warning_likelihood(
                    severity=severity,
                    code=diag.code or "",
                )
                card_class = f"diag-card {severity}"
                likelihood_badge = ""
                if warning_likelihood:
                    card_class += f" warning-{warning_likelihood}"
                    likelihood_badge = (
                        f"<span class=\"badge likelihood-{warning_likelihood}\">"
                        f"{_html_escape(warning_likelihood.title())} likelihood"
                        "</span>"
                    )
                suggestion = (
                    f"<div class=\"diag-fix\"><strong>Suggested fix:</strong> {_html_escape(diag.suggestion)}</div>"
                    if diag.suggestion
                    else ""
                )
                related = ""
                if diag.related:
                    related = "<div class=\"diag-detail\"><strong>Related:</strong><ul>" + "".join(
                        f"<li>{_html_escape(rel.pretty())}</li>" for rel in diag.related
                    ) + "</ul></div>"
                cards.append(
                    f"<article class=\"{card_class}\">"
                    "<div class=\"diag-meta\">"
                    f"<span class=\"badge severity-{severity}\">{_html_escape(severity.upper())}</span>"
                    f"{likelihood_badge}"
                    f"<span class=\"badge\">{_html_escape(diag.code or 'DEPPY')}</span>"
                    f"<span class=\"location\">{_html_escape(location)}</span>"
                    "</div>"
                    f"<h3 class=\"diag-title\">{_html_escape(diag.message)}</h3>"
                    f"{suggestion}"
                    f"{related}"
                    "</article>"
                )
            section_body = "".join(cards) if cards else '<p class="empty-state">No issues in this file.</p>'
            detail_sections.append(
                "<section class=\"file-section\">"
                f"<h2>{_html_escape(file_path)}</h2>"
                f"{section_body}"
                "</section>"
            )
        top_issue_cards = "".join(
            self._render_pipeline_issue_card(file_path, diag)
            for file_path, diag in diagnostics[:25]
        )
        top_issue_section = (
            "  <section class=\"panel\"><h2>Most likely issues</h2>"
            f"{top_issue_cards}</section>\n"
            if top_issue_cards
            else "  <section class=\"panel\"><h2>Overview</h2>"
            "<p class=\"empty-state\">No issues found.</p></section>\n"
        )

        return (
            "<!DOCTYPE html>\n"
            "<html lang=\"en\">\n"
            "<head>\n"
            "  <meta charset=\"utf-8\">\n"
            "  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n"
            "  <title>deppy check dashboard</title>\n"
            "  <style>\n"
            "    body { margin: 0; font-family: Inter, -apple-system, BlinkMacSystemFont, sans-serif; background: #0b1020; color: #e8ecf3; }\n"
            "    main { max-width: 1180px; margin: 0 auto; padding: 32px 24px 56px; }\n"
            "    .grid { display: grid; gap: 16px; grid-template-columns: repeat(auto-fit, minmax(180px, 1fr)); margin: 20px 0 24px; }\n"
            "    .stat, .panel { background: #121a30; border: 1px solid #24304f; border-radius: 12px; padding: 16px; }\n"
            "    table { width: 100%; border-collapse: collapse; }\n"
            "    th, td { text-align: left; padding: 10px 12px; border-bottom: 1px solid #24304f; }\n"
            "    .diag-card { background: #0f1629; border: 1px solid #263253; border-left-width: 5px; border-radius: 12px; padding: 14px 16px; margin-bottom: 14px; }\n"
            "    .diag-card.error { border-left-color: #f87171; }\n"
            "    .diag-card.warning { border-left-color: #fbbf24; }\n"
            "    .diag-card.warning.warning-high { background: #3a1616; border-left-color: #ef4444; }\n"
            "    .diag-card.warning.warning-medium { background: #3b230f; border-left-color: #f97316; }\n"
            "    .diag-card.warning.warning-low { background: #3a3113; border-left-color: #eab308; }\n"
            "    .diag-card.info, .diag-card.hint { border-left-color: #60a5fa; }\n"
            "    .badge { display: inline-flex; border-radius: 999px; padding: 3px 10px; font-size: 0.8rem; font-weight: 600; background: rgba(148, 163, 184, 0.15); color: #cbd5e1; }\n"
            "    .severity-error { background: rgba(248, 113, 113, 0.15); color: #fca5a5; }\n"
            "    .severity-warning { background: rgba(251, 191, 36, 0.16); color: #fcd34d; }\n"
            "    .severity-info, .severity-hint { background: rgba(96, 165, 250, 0.16); color: #93c5fd; }\n"
            "    .likelihood-high { background: rgba(239, 68, 68, 0.18); color: #fca5a5; }\n"
            "    .likelihood-medium { background: rgba(249, 115, 22, 0.18); color: #fdba74; }\n"
            "    .likelihood-low { background: rgba(234, 179, 8, 0.18); color: #fde68a; }\n"
            "    .diag-meta { display: flex; flex-wrap: wrap; gap: 8px; align-items: center; margin-bottom: 10px; }\n"
            "    .location { color: #93c5fd; font-family: ui-monospace, SFMono-Regular, monospace; }\n"
            "    .diag-fix, .diag-detail { margin-top: 10px; }\n"
            "    .empty-state { color: #91a0bd; }\n"
            "  </style>\n"
            "</head>\n"
            "<body><main>\n"
            "  <h1>deppy check dashboard</h1>\n"
            "  <div class=\"grid\">"
            f"<div class=\"stat\"><strong>Files with issues</strong><div>{len(issue_results)}</div></div>"
            f"<div class=\"stat\"><strong>Issues</strong><div>{len(diagnostics)}</div></div>"
            f"<div class=\"stat\"><strong>Errors</strong><div>{error_count}</div></div>"
            f"<div class=\"stat\"><strong>Warnings</strong><div>{warning_count}</div></div>"
            f"<div class=\"stat\"><strong>Info / hints</strong><div>{info_count}</div></div>"
            "</div>\n"
            f"{top_issue_section}"
            "  <section class=\"panel\"><h2>Files</h2><table><thead><tr><th>File</th><th>Issues</th><th>Errors</th><th>Warnings</th><th>Groups</th></tr></thead><tbody>"
            f"{''.join(file_rows)}</tbody></table></section>\n"
            "  <section class=\"panel\"><h2>Diagnostics by file</h2>"
            f"{''.join(detail_sections)}</section>\n"
            "</main></body>\n"
            "</html>\n"
        )

    def _render_pipeline_issue_card(self, file_path: str, diag: Diagnostic) -> str:
        severity = diag.severity.value
        warning_likelihood = self._warning_likelihood(
            severity=severity,
            code=diag.code or "",
        )
        card_class = f"diag-card {severity}"
        likelihood_badge = ""
        if warning_likelihood:
            card_class += f" warning-{warning_likelihood}"
            likelihood_badge = (
                f"<span class=\"badge likelihood-{warning_likelihood}\">"
                f"{_html_escape(warning_likelihood.title())} likelihood"
                "</span>"
            )
        location = diag.location.pretty() if diag.location else file_path
        suggestion = (
            f"<div class=\"diag-fix\"><strong>Suggested fix:</strong> {_html_escape(diag.suggestion)}</div>"
            if diag.suggestion
            else ""
        )
        return (
            f"<article class=\"{card_class}\">"
            "<div class=\"diag-meta\">"
            f"<span class=\"badge severity-{severity}\">{_html_escape(severity.upper())}</span>"
            f"{likelihood_badge}"
            f"<span class=\"badge\">{_html_escape(diag.code or 'DEPPY')}</span>"
            f"<span class=\"location\">{_html_escape(location)}</span>"
            "</div>"
            f"<h3 class=\"diag-title\">{_html_escape(diag.message)}</h3>"
            f"{suggestion}"
            "</article>"
        )

    def _print_multi_file_summary(
        self,
        files: List[str],
        results: List[PipelineResult],
        formatter: Formatter,
        cli_config: CLIConfig,
    ) -> None:
        """Print a summary across multiple files."""
        total_sites = sum(r.site_count for r in results)
        total_sections = sum(len(r.sections) for r in results)
        total_obstructions = sum(r.obstruction_count for r in results)
        total_errors = sum(r.error_count for r in results)
        total_warnings = sum(r.warning_count for r in results)
        total_contracts = sum(len(r.contracts) for r in results)

        print(f"\nSummary ({len(files)} files):", file=sys.stdout)
        print(f"  Sites: {total_sites}", file=sys.stdout)
        print(f"  Sections: {total_sections}", file=sys.stdout)
        print(f"  Obstructions: {total_obstructions}", file=sys.stdout)
        print(f"  Errors: {total_errors}", file=sys.stdout)
        print(f"  Warnings: {total_warnings}", file=sys.stdout)
        print(f"  Contracts: {total_contracts}", file=sys.stdout)


# ===================================================================
#  ExplainCommand
# ===================================================================


class ExplainCommand(Command):
    """Explain the sheaf-descent analysis for a specific site or scope.

    Shows the cover structure, sections, morphisms, and any obstructions
    affecting the specified target.
    """

    def run(self, cli_config: CLIConfig) -> int:
        """Execute the explain command."""
        files = self._resolve_source_files(cli_config)
        if not files:
            print("No source files specified.", file=sys.stderr)
            return 2

        pipeline = self._create_pipeline(cli_config)
        formatter = self._create_formatter(cli_config)
        target_site = cli_config.explain_site

        for file_path in files:
            result = pipeline.run(file_path)
            self._explain_result(result, target_site, formatter)

        return 0

    def _explain_result(
        self,
        result: PipelineResult,
        target_site: Optional[str],
        formatter: Formatter,
    ) -> None:
        """Print explanation for the analysis result."""
        print("\n=== Sheaf-Descent Analysis Explanation ===\n")

        # Cover information
        if result.cover:
            cover = result.cover
            print(f"Cover: {len(cover.sites)} sites, "
                  f"{len(cover.morphisms)} morphisms, "
                  f"{len(cover.overlaps)} overlaps")
            print(f"  Input boundary: {len(cover.input_boundary)} sites")
            print(f"  Output boundary: {len(cover.output_boundary)} sites")
            print(f"  Error sites: {len(cover.error_sites)} sites")
            print()

        # Sections
        if result.sections:
            print("Local sections:")
            for site_id, section in sorted(
                result.sections.items(), key=lambda x: str(x[0])
            ):
                if target_site and target_site not in str(site_id):
                    continue
                print(f"  {site_id}")
                print(f"    Trust: {section.trust.value}")
                print(f"    Provenance: {section.provenance}")
                if section.carrier_type:
                    print(f"    Carrier: {section.carrier_type}")
                if section.refinements:
                    print(f"    Refinements:")
                    for k, v in sorted(section.refinements.items()):
                        print(f"      {k}: {v!r}")
                print()

        # Obstructions
        if result.obstructions:
            print("Obstructions (H^1 classes):")
            for obs in result.obstructions:
                print(f"  {obs.explanation}")
                for a, b in obs.conflicting_overlaps:
                    print(f"    Between: {a} and {b}")
                print()

        # Convergence
        if result.convergence:
            conv = result.convergence
            status = "converged" if conv.converged else "NOT CONVERGED"
            print(f"Convergence: {status}")
            print(f"  Iterations: {conv.iterations_used}/{conv.max_iterations}")
            if conv.history:
                print(f"  Delta history: {[f'{d:.0f}' for d in conv.history]}")
            print()


# ===================================================================
#  ProveCommand
# ===================================================================


class ProveCommand(Command):
    """Attempt to prove a specific property using the sheaf analysis.

    Given a target function and property specification, runs the
    analysis and checks whether the property is established at the
    required trust level.
    """

    def run(self, cli_config: CLIConfig) -> int:
        """Execute the prove command."""
        files = self._resolve_source_files(cli_config)
        if not files:
            print("No source files specified.", file=sys.stderr)
            return 2

        target = cli_config.prove_target
        if not target:
            print("No proof target specified. Use --target.", file=sys.stderr)
            return 2

        pipeline = self._create_pipeline(cli_config)

        proved = False
        for file_path in files:
            result = pipeline.run(file_path)
            proved = self._check_proof(result, target)
            if proved:
                break

        if proved:
            print(f"PROVED: {target}")
            return 0
        else:
            print(f"UNPROVED: {target}")
            print("The property could not be established at the required trust level.")
            return 1

    def _check_proof(self, result: PipelineResult, target: str) -> bool:
        """Check if the target property is proved in the result.

        A property is proved if:
        1. The relevant section has trust >= TRUSTED_AUTO.
        2. There are no obstructions involving the target.
        3. The convergence was achieved.
        """
        if not result.success:
            return False

        if result.convergence and not result.convergence.converged:
            return False

        # Check for obstructions involving the target
        for obs in result.obstructions:
            for site_a, site_b in obs.conflicting_overlaps:
                if target in str(site_a) or target in str(site_b):
                    return False

        # Check sections for the target
        for site_id, section in result.sections.items():
            if target in str(site_id) or target in (section.provenance or ""):
                if section.trust in (TrustLevel.TRUSTED_AUTO, TrustLevel.PROOF_BACKED):
                    return True

        return False


# ===================================================================
#  GenerateCommand
# ===================================================================


class GenerateCommand(Command):
    """Generate contract annotations from analysis results.

    Runs the full analysis and outputs generated @requires, @ensures,
    and @invariant decorators that can be added to source code.
    """

    def run(self, cli_config: CLIConfig) -> int:
        """Execute the generate command."""
        files = self._resolve_source_files(cli_config)
        if not files:
            print("No source files specified.", file=sys.stderr)
            return 2

        pipeline = self._create_pipeline(cli_config)
        output_path = cli_config.generate_output

        all_contracts: List[ContractAnnotation] = []

        for file_path in files:
            result = pipeline.run(file_path)
            all_contracts.extend(result.contracts)

        if not all_contracts:
            print("No contracts generated.", file=sys.stderr)
            return 0

        output = self._format_contracts(all_contracts)

        if output_path:
            Path(output_path).write_text(output, encoding="utf-8")
            print(f"Contracts written to {output_path}", file=sys.stderr)
        else:
            print(output)

        return 0

    def _format_contracts(self, contracts: Sequence[ContractAnnotation]) -> str:
        """Format contracts as Python source annotations."""
        lines: List[str] = [
            "# Generated by DepPy sheaf-descent analysis",
            "# These contracts can be applied as decorators.",
            "",
        ]

        # Group by scope
        scope_contracts: Dict[str, List[ContractAnnotation]] = {}
        for c in contracts:
            scope_contracts.setdefault(c.scope_name, []).append(c)

        for scope_name in sorted(scope_contracts.keys()):
            lines.append(f"# Contracts for: {scope_name}")
            for contract in scope_contracts[scope_name]:
                lines.append(f"# {contract.to_decorator_string()}")
            lines.append("")

        return "\n".join(lines)


# ===================================================================
#  WatchCommand
# ===================================================================


class WatchCommand(Command):
    """Watch source files for changes and re-analyze automatically.

    Uses file modification time polling to detect changes, then
    re-runs the analysis pipeline on changed files.
    """

    def run(self, cli_config: CLIConfig) -> int:
        """Execute the watch command.

        This blocks indefinitely, polling for file changes.
        Press Ctrl+C to stop.
        """
        files = self._resolve_source_files(cli_config)
        if not files:
            print("No source files to watch.", file=sys.stderr)
            return 2

        pipeline = self._create_pipeline(cli_config)
        formatter = self._create_formatter(cli_config)

        print(f"Watching {len(files)} files for changes...", file=sys.stderr)
        print("Press Ctrl+C to stop.\n", file=sys.stderr)

        # Initial analysis
        mtimes: Dict[str, float] = {}
        for file_path in files:
            mtimes[file_path] = self._get_mtime(file_path)
            result = pipeline.run(file_path)
            self._print_brief_result(result, file_path, formatter)

        # Poll loop
        poll_interval = 1.0  # seconds
        try:
            while True:
                time.sleep(poll_interval)
                for file_path in files:
                    new_mtime = self._get_mtime(file_path)
                    if new_mtime != mtimes.get(file_path, 0):
                        mtimes[file_path] = new_mtime
                        print(f"\nFile changed: {file_path}", file=sys.stderr)
                        result = pipeline.run(file_path)
                        self._print_brief_result(result, file_path, formatter)
        except KeyboardInterrupt:
            print("\nWatch stopped.", file=sys.stderr)
            return 0

    @staticmethod
    def _get_mtime(file_path: str) -> float:
        """Get file modification time, or 0 if file doesn't exist."""
        try:
            return os.path.getmtime(file_path)
        except OSError:
            return 0.0

    def _print_brief_result(
        self,
        result: PipelineResult,
        file_path: str,
        formatter: Formatter,
    ) -> None:
        """Print a brief result summary for watch mode."""
        status = "OK" if result.success else "ISSUES"
        errors = result.error_count
        warnings = result.warning_count
        sites = result.site_count
        elapsed = (
            f"{result.timing.total_elapsed:.3f}s"
            if result.timing
            else "?"
        )

        name = Path(file_path).name
        print(
            f"  [{status}] {name}: "
            f"{sites} sites, {errors} errors, {warnings} warnings "
            f"({elapsed})"
        )

        # Print errors only
        for diag in result.diagnostics:
            if diag.severity == DiagnosticSeverity.ERROR:
                formatted = formatter.format_diagnostic(diag)
                print(f"    {formatted}")


# ===================================================================
#  Command registry
# ===================================================================


_COMMANDS: Dict[str, type] = {
    "check": CheckCommand,
    "explain": ExplainCommand,
    "prove": ProveCommand,
    "generate": GenerateCommand,
    "watch": WatchCommand,
}


def get_command(name: str) -> Optional[Command]:
    """Look up a command by name and return an instance."""
    cls = _COMMANDS.get(name)
    if cls is not None:
        return cls()
    return None


def available_commands() -> List[str]:
    """Return the list of available command names."""
    return sorted(_COMMANDS.keys())
