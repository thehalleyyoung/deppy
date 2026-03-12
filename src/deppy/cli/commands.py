"""Command implementations for the DepPy CLI.

Each command class handles a specific subcommand:
- CheckCommand: Run sheaf-descent analysis and report diagnostics.
- ExplainCommand: Explain the analysis for a specific site or scope.
- ProveCommand: Attempt to prove a specific property.
- GenerateCommand: Generate contract annotations from analysis.
- WatchCommand: Watch files for changes and re-analyze.
"""

from __future__ import annotations

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
                for py_file in sorted(path.rglob("*.py")):
                    name = py_file.name
                    if not any(
                        pattern in str(py_file)
                        for pattern in ("__pycache__", ".git", ".tox", ".venv")
                    ):
                        files.append(str(py_file.resolve()))
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

        pipeline = self._create_pipeline(cli_config)
        formatter = self._create_formatter(cli_config)

        total_errors = 0
        total_warnings = 0
        all_results: List[PipelineResult] = []

        for file_path in files:
            if cli_config.verbosity >= 1:
                print(f"Analyzing {file_path}...", file=sys.stderr)

            result = pipeline.run(file_path)
            all_results.append(result)

            # Print diagnostics
            for diag in result.diagnostics:
                formatted = formatter.format_diagnostic(diag)
                if diag.severity == DiagnosticSeverity.ERROR:
                    print(formatted, file=sys.stderr)
                else:
                    print(formatted, file=sys.stdout)

            total_errors += result.error_count
            total_warnings += result.warning_count

        # Print combined summary if multiple files
        if len(files) > 1:
            self._print_multi_file_summary(
                files, all_results, formatter, cli_config
            )
        elif all_results:
            summary = formatter.format_summary(all_results[0])
            print(summary, file=sys.stdout)

        # Print contracts if requested
        if cli_config.verbosity >= 1:
            for result in all_results:
                if result.contracts:
                    contracts_str = formatter.format_contracts(result.contracts)
                    if contracts_str:
                        print(contracts_str, file=sys.stdout)

        if total_errors > 0:
            return 1
        return 0

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
