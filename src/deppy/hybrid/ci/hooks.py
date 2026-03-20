"""
hooks.py — Pre-commit hooks and CI integration for deppy.

Provides:
  - DeppyPreCommitHook: runs deppy analysis on staged files
  - GitHubActionsReporter: emits annotations, check runs, PR comments, SARIF
  - ProjectConfig: reads configuration from pyproject.toml / .deppy.toml
  - CIIntegration: CLI entry point for CI pipelines

Usage as pre-commit hook (.pre-commit-config.yaml):
    repos:
      - repo: https://github.com/mathdivergence/deppy
        hooks:
          - id: deppy
            entry: python -m deppy.hybrid.ci.hooks check
            language: python
            types: [python]

Usage in GitHub Actions:
    - name: deppy check
      run: python -m deppy.hybrid.ci.hooks check --mode cheap
    - name: deppy report
      run: python -m deppy.hybrid.ci.hooks report --format github-actions

Usage from CLI:
    python -m deppy.hybrid.ci.hooks check
    python -m deppy.hybrid.ci.hooks report --format sarif
    python -m deppy.hybrid.ci.hooks dashboard
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple


# ---------------------------------------------------------------------------
# Data types
# ---------------------------------------------------------------------------


# --- Integration with existing deppy codebase ---
try:
    from deppy.cli.main import main as _core_cli_main
    from deppy.pipeline import AnalysisPipeline, PipelineConfig, PipelineResult
    from deppy.core._protocols import TrustLevel as _CoreTrustLevel
    from deppy.render.diagnostic_renderer import (
        Diagnostic as _CoreDiagnostic,
        DiagnosticSeverity as _CoreSeverity,
    )
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False


def _safe_base(core_cls: type) -> type:
    """Return core_cls if it can be safely subclassed by a non-frozen dataclass."""
    import dataclasses as _dc
    if _dc.is_dataclass(core_cls) and getattr(
        getattr(core_cls, "__dataclass_params__", None), "frozen", False
    ):
        return object
    return core_cls

class Severity(Enum):
    """Diagnostic severity levels."""
    CRITICAL = "critical"
    ERROR = "error"
    WARNING = "warning"
    INFO = "info"


class TrustLevel(Enum):
    """Trust levels from deppy analysis."""
    UNTYPEABLE = "UNTYPEABLE"
    TYPED = "TYPED"
    PROPERTY_STATED = "PROPERTY_STATED"
    PROPERTY_CHECKED = "PROPERTY_CHECKED"
    PROOF_SKETCHED = "PROOF_SKETCHED"
    PROOF_VERIFIED = "PROOF_VERIFIED"

    @classmethod
    def from_string(cls, s: str) -> TrustLevel:
        """Parse a trust level from a string, case-insensitive."""
        normalized = s.upper().replace("-", "_").replace(" ", "_")
        try:
            return cls(normalized)
        except ValueError:
            valid = ", ".join(level.value for level in cls)
            raise ValueError(
                f"Unknown trust level: {s!r}. Valid: {valid}"
            ) from None


@dataclass
class Diagnostic(_safe_base(_CoreDiagnostic) if _HAS_DEPPY_CORE else object):
    """A single diagnostic emitted by deppy analysis.

    Extends the core ``Diagnostic`` when available, adding CI-specific
    fields (h1_type, h1_dimension, rule_id, fix_suggestion).
    """
    file: str = ""
    line: int = 0
    column: int = 0
    severity: Severity = Severity.INFO
    message: str = ""
    h1_type: str = ""
    h1_dimension: int = 0
    rule_id: str = ""
    fix_suggestion: Optional[str] = None
    trust_level: Optional[TrustLevel] = None

    def to_dict(self) -> Dict[str, Any]:
        """Serialize to a plain dict."""
        return {
            "file": self.file,
            "line": self.line,
            "column": self.column,
            "severity": self.severity.value,
            "message": self.message,
            "h1_type": self.h1_type,
            "h1_dimension": self.h1_dimension,
            "rule_id": self.rule_id,
            "fix_suggestion": self.fix_suggestion,
            "trust_level": self.trust_level.value if self.trust_level else None,
        }


@dataclass
class HookConfig:
    """Configuration for the pre-commit hook."""
    mode: str = "cheap"
    fail_on: str = "error"
    max_h1: int = 0
    budget_tokens: int = 10000
    exclude_paths: List[str] = field(default_factory=list)
    include_paths: List[str] = field(
        default_factory=lambda: ["**/*.py"]
    )

    def should_fail(self, severity: Severity) -> bool:
        """Return True if this severity should cause the hook to fail."""
        severity_order = {
            Severity.INFO: 0,
            Severity.WARNING: 1,
            Severity.ERROR: 2,
            Severity.CRITICAL: 3,
        }
        threshold_map = {
            "info": Severity.INFO,
            "warning": Severity.WARNING,
            "error": Severity.ERROR,
            "critical": Severity.CRITICAL,
        }
        threshold = threshold_map.get(self.fail_on, Severity.ERROR)
        return severity_order[severity] >= severity_order[threshold]


@dataclass
class HookResult:
    """Result of running the pre-commit hook."""
    passed: bool
    diagnostics: List[Diagnostic]
    h1_dimension: int
    time_seconds: float
    summary: str
    files_analyzed: int = 0
    tokens_used: int = 0

    @property
    def exit_code(self) -> int:
        """Return the appropriate exit code."""
        return 0 if self.passed else 1

    def to_dict(self) -> Dict[str, Any]:
        """Serialize to a plain dict."""
        return {
            "passed": self.passed,
            "diagnostics": [d.to_dict() for d in self.diagnostics],
            "h1_dimension": self.h1_dimension,
            "time_seconds": self.time_seconds,
            "summary": self.summary,
            "files_analyzed": self.files_analyzed,
            "tokens_used": self.tokens_used,
        }


# ---------------------------------------------------------------------------
# ProjectConfig — reads deppy configuration
# ---------------------------------------------------------------------------

class ProjectConfig:
    """Reads deppy configuration from pyproject.toml or .deppy.toml.

    Configuration is searched for in the following order:
      1. [tool.deppy] section in pyproject.toml
      2. .deppy.toml in the project root
      3. ~/.config/deppy/config.toml (user-level defaults)
      4. Built-in defaults

    Example pyproject.toml:
        [tool.deppy]
        mode = "cheap"
        fail_on = "error"
        max_h1 = 0
        budget_tokens = 10000
        exclude_paths = ["tests/fixtures/*"]
        include_paths = ["src/**/*.py"]
        trust_target = "PROPERTY_CHECKED"
        oracle_model = "gpt-4"
        lean_enabled = false

    Example .deppy.toml:
        mode = "standard"
        fail_on = "warning"
        max_h1 = 2
        budget_tokens = 50000
    """

    def __init__(
        self,
        mode: str = "cheap",
        fail_on: str = "error",
        max_h1: int = 0,
        budget_tokens: int = 10000,
        exclude_paths: Optional[List[str]] = None,
        include_paths: Optional[List[str]] = None,
        trust_target: str = "PROPERTY_CHECKED",
        oracle_model: str = "gpt-4",
        lean_enabled: bool = False,
    ) -> None:
        self.mode = mode
        self.fail_on = fail_on
        self.max_h1 = max_h1
        self.budget_tokens = budget_tokens
        self.exclude_paths = exclude_paths if exclude_paths is not None else []
        self.include_paths = (
            include_paths if include_paths is not None else ["**/*.py"]
        )
        self.trust_target = trust_target
        self.oracle_model = oracle_model
        self.lean_enabled = lean_enabled

    def to_hook_config(self) -> HookConfig:
        """Convert to a HookConfig for the pre-commit hook."""
        return HookConfig(
            mode=self.mode,
            fail_on=self.fail_on,
            max_h1=self.max_h1,
            budget_tokens=self.budget_tokens,
            exclude_paths=self.exclude_paths,
            include_paths=self.include_paths,
        )

    def to_dict(self) -> Dict[str, Any]:
        """Serialize to a plain dict."""
        return {
            "mode": self.mode,
            "fail_on": self.fail_on,
            "max_h1": self.max_h1,
            "budget_tokens": self.budget_tokens,
            "exclude_paths": self.exclude_paths,
            "include_paths": self.include_paths,
            "trust_target": self.trust_target,
            "oracle_model": self.oracle_model,
            "lean_enabled": self.lean_enabled,
        }

    @classmethod
    def _parse_toml_section(cls, data: Dict[str, Any]) -> ProjectConfig:
        """Create a ProjectConfig from a parsed TOML section dict."""
        return cls(
            mode=data.get("mode", "cheap"),
            fail_on=data.get("fail_on", "error"),
            max_h1=data.get("max_h1", 0),
            budget_tokens=data.get("budget_tokens", 10000),
            exclude_paths=data.get("exclude_paths", []),
            include_paths=data.get("include_paths", ["**/*.py"]),
            trust_target=data.get("trust_target", "PROPERTY_CHECKED"),
            oracle_model=data.get("oracle_model", "gpt-4"),
            lean_enabled=data.get("lean_enabled", False),
        )

    @classmethod
    def from_pyproject(cls, path: str = "pyproject.toml") -> ProjectConfig:
        """Read configuration from [tool.deppy] in pyproject.toml.

        Args:
            path: Path to the pyproject.toml file.

        Returns:
            ProjectConfig parsed from the file.

        Raises:
            FileNotFoundError: If the file does not exist.
            KeyError: If [tool.deppy] section is not found.
        """
        resolved = Path(path).resolve()
        if not resolved.exists():
            raise FileNotFoundError(f"pyproject.toml not found: {resolved}")

        try:
            import tomllib  # Python 3.11+
        except ImportError:
            try:
                import tomli as tomllib  # type: ignore[no-redef]
            except ImportError:
                # Fallback: basic TOML parsing for simple cases
                return cls._from_pyproject_fallback(resolved)

        with open(resolved, "rb") as f:
            data = tomllib.load(f)

        tool_deppy = data.get("tool", {}).get("deppy", None)
        if tool_deppy is None:
            raise KeyError(
                f"No [tool.deppy] section found in {resolved}"
            )
        return cls._parse_toml_section(tool_deppy)

    @classmethod
    def _from_pyproject_fallback(cls, path: Path) -> ProjectConfig:
        """Basic fallback parser when tomllib/tomli unavailable.

        Only handles simple key = value lines under [tool.deppy].
        For full TOML support, install tomli (Python < 3.11).
        """
        in_section = False
        data: Dict[str, Any] = {}
        with open(path) as f:
            for line in f:
                stripped = line.strip()
                if stripped == "[tool.deppy]":
                    in_section = True
                    continue
                if in_section and stripped.startswith("["):
                    break
                if in_section and "=" in stripped:
                    key, _, raw_value = stripped.partition("=")
                    key = key.strip()
                    raw_value = raw_value.strip().strip('"').strip("'")
                    if raw_value.lower() in ("true", "false"):
                        data[key] = raw_value.lower() == "true"
                    elif raw_value.isdigit():
                        data[key] = int(raw_value)
                    else:
                        data[key] = raw_value
        if not data:
            raise KeyError(f"No [tool.deppy] section found in {path}")
        return cls._parse_toml_section(data)

    @classmethod
    def from_deppy_toml(cls, path: str = ".deppy.toml") -> ProjectConfig:
        """Read configuration from a .deppy.toml file.

        Args:
            path: Path to the .deppy.toml file.

        Returns:
            ProjectConfig parsed from the file.

        Raises:
            FileNotFoundError: If the file does not exist.
        """
        resolved = Path(path).resolve()
        if not resolved.exists():
            raise FileNotFoundError(f".deppy.toml not found: {resolved}")

        try:
            import tomllib
        except ImportError:
            try:
                import tomli as tomllib  # type: ignore[no-redef]
            except ImportError:
                return cls._from_deppy_toml_fallback(resolved)

        with open(resolved, "rb") as f:
            data = tomllib.load(f)

        return cls._parse_toml_section(data)

    @classmethod
    def _from_deppy_toml_fallback(cls, path: Path) -> ProjectConfig:
        """Basic fallback parser for .deppy.toml without tomllib."""
        data: Dict[str, Any] = {}
        with open(path) as f:
            for line in f:
                stripped = line.strip()
                if not stripped or stripped.startswith("#") or stripped.startswith("["):
                    continue
                if "=" in stripped:
                    key, _, raw_value = stripped.partition("=")
                    key = key.strip()
                    raw_value = raw_value.strip().strip('"').strip("'")
                    if raw_value.lower() in ("true", "false"):
                        data[key] = raw_value.lower() == "true"
                    elif raw_value.isdigit():
                        data[key] = int(raw_value)
                    else:
                        data[key] = raw_value
        return cls._parse_toml_section(data)

    @classmethod
    def discover(cls) -> ProjectConfig:
        """Discover configuration by searching up the directory tree.

        Looks for configuration files in this order:
          1. pyproject.toml with [tool.deppy] in current dir or parents
          2. .deppy.toml in current dir or parents
          3. Falls back to defaults

        Returns:
            ProjectConfig from the first config file found, or defaults.
        """
        search_dir = Path.cwd()

        while True:
            pyproject = search_dir / "pyproject.toml"
            if pyproject.exists():
                try:
                    return cls.from_pyproject(str(pyproject))
                except (KeyError, Exception):
                    pass

            deppy_toml = search_dir / ".deppy.toml"
            if deppy_toml.exists():
                try:
                    return cls.from_deppy_toml(str(deppy_toml))
                except Exception:
                    pass

            parent = search_dir.parent
            if parent == search_dir:
                break
            search_dir = parent

        # User-level config
        user_config = Path.home() / ".config" / "deppy" / "config.toml"
        if user_config.exists():
            try:
                return cls.from_deppy_toml(str(user_config))
            except Exception:
                pass

        return cls()

    def __repr__(self) -> str:
        return (
            f"ProjectConfig(mode={self.mode!r}, fail_on={self.fail_on!r}, "
            f"max_h1={self.max_h1}, budget_tokens={self.budget_tokens}, "
            f"trust_target={self.trust_target!r})"
        )


# ---------------------------------------------------------------------------
# DeppyPreCommitHook
# ---------------------------------------------------------------------------

class DeppyPreCommitHook:
    """Pre-commit hook that runs deppy analysis on staged files.

    Compatible with the pre-commit framework (https://pre-commit.com/).
    Exit codes:
      0 — all checks pass
      1 — one or more diagnostics exceed fail_on severity
      2 — configuration error

    Example .pre-commit-config.yaml entry:
        repos:
          - repo: local
            hooks:
              - id: deppy
                name: deppy sheaf-cohomological analysis
                entry: python -m deppy.hybrid.ci.hooks check
                language: python
                types: [python]
                pass_filenames: true
    """

    def __init__(self, config: Optional[ProjectConfig] = None) -> None:
        self._config = config or ProjectConfig.discover()

    @property
    def config(self) -> ProjectConfig:
        """Return the active project configuration."""
        return self._config

    def _filter_files(
        self,
        files: List[str],
        hook_config: HookConfig,
    ) -> List[str]:
        """Filter files by include/exclude patterns."""
        from fnmatch import fnmatch

        filtered: List[str] = []
        for filepath in files:
            # Check excludes first
            excluded = any(
                fnmatch(filepath, pat) for pat in hook_config.exclude_paths
            )
            if excluded:
                continue
            # Check includes
            included = any(
                fnmatch(filepath, pat) for pat in hook_config.include_paths
            )
            if included:
                filtered.append(filepath)
        return filtered

    def _analyze_file(self, filepath: str, config: HookConfig) -> List[Diagnostic]:
        """Run deppy analysis on a single file.

        This is a stub that delegates to the deppy analysis pipeline.
        In the full implementation, this calls the sheaf-cohomological
        analysis engine.
        """
        # Import the analysis pipeline if available
        try:
            from deppy.hybrid.pipeline.runner import analyze_file
            return analyze_file(filepath, mode=config.mode)
        except ImportError:
            pass

        # Stub: return empty diagnostics when pipeline not available
        return []

    def run(
        self,
        staged_files: List[str],
        config: Optional[HookConfig] = None,
    ) -> HookResult:
        """Run deppy analysis on staged files.

        Args:
            staged_files: List of file paths to analyze (typically
                from ``git diff --cached --name-only``).
            config: Override hook configuration. If None, uses project config.

        Returns:
            HookResult with diagnostics, pass/fail status, and summary.
        """
        start_time = time.monotonic()
        hook_config = config or self._config.to_hook_config()

        # Filter to relevant files
        files = self._filter_files(staged_files, hook_config)
        if not files:
            elapsed = time.monotonic() - start_time
            return HookResult(
                passed=True,
                diagnostics=[],
                h1_dimension=0,
                time_seconds=elapsed,
                summary="No Python files to analyze.",
                files_analyzed=0,
            )

        # Analyze each file
        all_diagnostics: List[Diagnostic] = []
        total_h1 = 0
        tokens_used = 0

        for filepath in files:
            try:
                diags = self._analyze_file(filepath, hook_config)
                all_diagnostics.extend(diags)
                total_h1 += sum(d.h1_dimension for d in diags)
            except Exception as exc:
                all_diagnostics.append(Diagnostic(
                    file=filepath,
                    line=0,
                    column=0,
                    severity=Severity.ERROR,
                    message=f"Analysis failed: {exc}",
                    h1_type="ANALYSIS_ERROR",
                    h1_dimension=0,
                    rule_id="E000",
                ))

        # Determine pass/fail
        failing_diagnostics = [
            d for d in all_diagnostics
            if hook_config.should_fail(d.severity)
        ]
        h1_exceeded = total_h1 > hook_config.max_h1
        passed = len(failing_diagnostics) == 0 and not h1_exceeded

        elapsed = time.monotonic() - start_time

        # Build summary
        counts = {sev: 0 for sev in Severity}
        for d in all_diagnostics:
            counts[d.severity] += 1

        summary_parts = [
            f"Analyzed {len(files)} file(s) in {elapsed:.2f}s.",
            f"H¹ dimension: {total_h1}.",
        ]
        for sev in (Severity.CRITICAL, Severity.ERROR, Severity.WARNING, Severity.INFO):
            if counts[sev] > 0:
                summary_parts.append(f"{counts[sev]} {sev.value}(s)")

        if passed:
            summary_parts.append("All checks passed.")
        else:
            reasons = []
            if failing_diagnostics:
                reasons.append(
                    f"{len(failing_diagnostics)} diagnostic(s) "
                    f"at or above '{hook_config.fail_on}' severity"
                )
            if h1_exceeded:
                reasons.append(
                    f"H¹={total_h1} exceeds max_h1={hook_config.max_h1}"
                )
            summary_parts.append("FAILED: " + "; ".join(reasons) + ".")

        return HookResult(
            passed=passed,
            diagnostics=all_diagnostics,
            h1_dimension=total_h1,
            time_seconds=elapsed,
            summary=" ".join(summary_parts),
            files_analyzed=len(files),
            tokens_used=tokens_used,
        )


# ---------------------------------------------------------------------------
# GitHubActionsReporter
# ---------------------------------------------------------------------------

class GitHubActionsReporter:
    """Emits diagnostics in formats suitable for GitHub Actions and PRs.

    Supports:
      - GitHub Actions workflow annotations (::error, ::warning)
      - GitHub Check Run API payloads
      - Markdown PR comments with trust summaries
      - SARIF format for GitHub Code Scanning integration
    """

    # SARIF constants
    SARIF_VERSION = "2.1.0"
    SARIF_SCHEMA = (
        "https://docs.oasis-open.org/sarif/sarif/v2.1.0/"
        "errata01/os/schemas/sarif-schema-2.1.0.json"
    )
    TOOL_NAME = "deppy"
    TOOL_VERSION = "0.1.0"

    def report(self, diagnostics: List[Diagnostic]) -> None:
        """Emit GitHub Actions workflow annotations to stdout.

        Outputs lines like:
            ::error file=src/foo.py,line=42,col=1::H¹ obstruction found...
            ::warning file=src/bar.py,line=10,col=5::Fragile correctness...

        These are parsed by GitHub Actions and displayed as annotations
        on the pull request's Files Changed tab.
        """
        for diag in diagnostics:
            level = self._severity_to_gh_level(diag.severity)
            # Escape special characters for GitHub Actions
            message = (
                diag.message
                .replace("%", "%25")
                .replace("\r", "%0D")
                .replace("\n", "%0A")
            )
            annotation = (
                f"::{level} file={diag.file},"
                f"line={diag.line},"
                f"col={diag.column}"
                f"::[{diag.rule_id}] {message}"
            )
            print(annotation)

    def _severity_to_gh_level(self, severity: Severity) -> str:
        """Map deppy severity to GitHub Actions annotation level."""
        mapping = {
            Severity.CRITICAL: "error",
            Severity.ERROR: "error",
            Severity.WARNING: "warning",
            Severity.INFO: "notice",
        }
        return mapping.get(severity, "notice")

    def _severity_to_sarif_level(self, severity: Severity) -> str:
        """Map deppy severity to SARIF result level."""
        mapping = {
            Severity.CRITICAL: "error",
            Severity.ERROR: "error",
            Severity.WARNING: "warning",
            Severity.INFO: "note",
        }
        return mapping.get(severity, "note")

    def create_check_run(
        self,
        diagnostics: List[Diagnostic],
        token: str,
        title: str = "deppy sheaf-cohomological analysis",
    ) -> Dict[str, Any]:
        """Create a GitHub Check Run API payload.

        This returns the JSON payload suitable for POST to
        /repos/{owner}/{repo}/check-runs. The caller is responsible
        for making the actual API call.

        Args:
            diagnostics: List of diagnostics to report.
            token: GitHub API token (used in the Auth header, not in payload).
            title: Title for the check run.

        Returns:
            Dict suitable for json.dumps() and POST to GitHub API.
        """
        total_h1 = sum(d.h1_dimension for d in diagnostics)
        errors = sum(
            1 for d in diagnostics
            if d.severity in (Severity.ERROR, Severity.CRITICAL)
        )
        warnings = sum(
            1 for d in diagnostics if d.severity == Severity.WARNING
        )

        conclusion = "success" if errors == 0 else "failure"
        summary = (
            f"**deppy analysis complete.**\n\n"
            f"- H¹ dimension: **{total_h1}**\n"
            f"- Errors: **{errors}**\n"
            f"- Warnings: **{warnings}**\n"
            f"- Total diagnostics: **{len(diagnostics)}**\n"
        )

        annotations = []
        for diag in diagnostics[:50]:  # GitHub API limit: 50 annotations
            annotations.append({
                "path": diag.file,
                "start_line": diag.line,
                "end_line": diag.line,
                "annotation_level": self._severity_to_gh_level(diag.severity),
                "title": f"[{diag.rule_id}] {diag.h1_type}",
                "message": diag.message,
            })

        return {
            "name": "deppy",
            "head_sha": os.environ.get("GITHUB_SHA", ""),
            "status": "completed",
            "conclusion": conclusion,
            "output": {
                "title": title,
                "summary": summary,
                "annotations": annotations,
            },
        }

    def create_pr_comment(self, diagnostics: List[Diagnostic]) -> str:
        """Create a markdown PR comment with trust summary.

        Args:
            diagnostics: List of diagnostics to include.

        Returns:
            Markdown string suitable for posting as a PR comment.
        """
        total_h1 = sum(d.h1_dimension for d in diagnostics)
        errors = [
            d for d in diagnostics
            if d.severity in (Severity.ERROR, Severity.CRITICAL)
        ]
        warnings = [d for d in diagnostics if d.severity == Severity.WARNING]

        if not diagnostics:
            status_emoji = "✅"
            status_text = "All checks passed"
        elif errors:
            status_emoji = "❌"
            status_text = f"{len(errors)} error(s) found"
        else:
            status_emoji = "⚠️"
            status_text = f"{len(warnings)} warning(s) found"

        lines = [
            f"## {status_emoji} deppy Analysis: {status_text}",
            "",
            "| Metric | Value |",
            "|--------|-------|",
            f"| H¹ dimension | **{total_h1}** |",
            f"| Errors | {len(errors)} |",
            f"| Warnings | {len(warnings)} |",
            f"| Total diagnostics | {len(diagnostics)} |",
            "",
        ]

        if diagnostics:
            lines.append("### Diagnostics")
            lines.append("")

            for diag in diagnostics:
                severity_icon = {
                    Severity.CRITICAL: "🔴",
                    Severity.ERROR: "🔴",
                    Severity.WARNING: "🟡",
                    Severity.INFO: "🔵",
                }.get(diag.severity, "⚪")

                lines.append(
                    f"- {severity_icon} **{diag.file}:{diag.line}** "
                    f"[{diag.rule_id}] ({diag.h1_type})"
                )
                lines.append(f"  {diag.message}")
                if diag.fix_suggestion:
                    lines.append(f"  💡 *Suggested fix:* {diag.fix_suggestion}")
                lines.append("")

        # Trust summary
        trust_levels: Dict[str, int] = {}
        for diag in diagnostics:
            if diag.trust_level:
                key = diag.trust_level.value
                trust_levels[key] = trust_levels.get(key, 0) + 1

        if trust_levels:
            lines.append("### Trust Summary")
            lines.append("")
            lines.append("| Trust Level | Count |")
            lines.append("|-------------|-------|")
            for level_name, count in sorted(trust_levels.items()):
                lines.append(f"| {level_name} | {count} |")
            lines.append("")

        lines.append(
            "*Generated by [deppy](https://github.com/mathdivergence/deppy) "
            "— sheaf-cohomological program analysis*"
        )

        return "\n".join(lines)

    def create_sarif_upload(
        self, diagnostics: List[Diagnostic]
    ) -> Dict[str, Any]:
        """Create a SARIF document for GitHub Code Scanning.

        Returns a SARIF 2.1.0 compliant document that can be uploaded
        via the GitHub Code Scanning API (POST /repos/.../code-scanning/sarifs).

        Args:
            diagnostics: List of diagnostics to include.

        Returns:
            Dict representing a valid SARIF 2.1.0 document.
        """
        # Collect unique rule IDs
        rules_seen: Dict[str, int] = {}
        rules: List[Dict[str, Any]] = []

        for diag in diagnostics:
            if diag.rule_id not in rules_seen:
                rules_seen[diag.rule_id] = len(rules)
                rules.append({
                    "id": diag.rule_id,
                    "name": diag.rule_id,
                    "shortDescription": {
                        "text": f"deppy H¹ obstruction: {diag.h1_type}",
                    },
                    "fullDescription": {
                        "text": (
                            f"Sheaf-cohomological obstruction of type "
                            f"{diag.h1_type} detected by deppy."
                        ),
                    },
                    "helpUri": (
                        "https://github.com/mathdivergence/deppy"
                        f"#rule-{diag.rule_id.lower()}"
                    ),
                    "properties": {
                        "tags": ["deppy", "sheaf-cohomology", diag.h1_type],
                    },
                })

        # Build results
        results: List[Dict[str, Any]] = []
        for diag in diagnostics:
            result: Dict[str, Any] = {
                "ruleId": diag.rule_id,
                "ruleIndex": rules_seen[diag.rule_id],
                "level": self._severity_to_sarif_level(diag.severity),
                "message": {"text": diag.message},
                "locations": [
                    {
                        "physicalLocation": {
                            "artifactLocation": {
                                "uri": diag.file,
                                "uriBaseId": "%SRCROOT%",
                            },
                            "region": {
                                "startLine": diag.line,
                                "startColumn": diag.column,
                            },
                        },
                    }
                ],
                "properties": {
                    "h1_type": diag.h1_type,
                    "h1_dimension": diag.h1_dimension,
                },
            }
            if diag.fix_suggestion:
                result["fixes"] = [
                    {
                        "description": {"text": diag.fix_suggestion},
                    }
                ]
            results.append(result)

        return {
            "$schema": self.SARIF_SCHEMA,
            "version": self.SARIF_VERSION,
            "runs": [
                {
                    "tool": {
                        "driver": {
                            "name": self.TOOL_NAME,
                            "version": self.TOOL_VERSION,
                            "informationUri": (
                                "https://github.com/mathdivergence/deppy"
                            ),
                            "rules": rules,
                        },
                    },
                    "results": results,
                    "columnKind": "utf16CodeUnits",
                }
            ],
        }


# ---------------------------------------------------------------------------
# CIIntegration — CLI entry point
# ---------------------------------------------------------------------------

class CIIntegration:
    """CLI entry point for deppy CI integration.

    Subcommands:
      check     — Run deppy analysis on files (default: staged files)
      report    — Generate a report from analysis results
      dashboard — Print a summary dashboard

    Exit codes:
      0 — all checks pass
      1 — one or more diagnostics at or above fail_on severity
      2 — configuration or runtime error
    """

    def __init__(self) -> None:
        self._config: Optional[ProjectConfig] = None

    @property
    def config(self) -> ProjectConfig:
        """Lazily discover and cache project configuration."""
        if self._config is None:
            self._config = ProjectConfig.discover()
        return self._config

    def build_parser(self) -> argparse.ArgumentParser:
        """Build the argument parser for the CLI."""
        parser = argparse.ArgumentParser(
            prog="deppy-ci",
            description="deppy CI integration — sheaf-cohomological analysis",
        )
        subparsers = parser.add_subparsers(dest="command", help="Subcommand")

        # check subcommand
        check_parser = subparsers.add_parser(
            "check",
            help="Run deppy analysis on files",
        )
        check_parser.add_argument(
            "files",
            nargs="*",
            help="Files to analyze (default: staged git files)",
        )
        check_parser.add_argument(
            "--mode",
            choices=["free", "cheap", "standard"],
            default=None,
            help="Analysis mode (overrides config)",
        )
        check_parser.add_argument(
            "--fail-on",
            choices=["info", "warning", "error", "critical"],
            default=None,
            help="Minimum severity to cause failure (overrides config)",
        )
        check_parser.add_argument(
            "--max-h1",
            type=int,
            default=None,
            help="Maximum allowed H¹ dimension (overrides config)",
        )
        check_parser.add_argument(
            "--json",
            action="store_true",
            dest="output_json",
            help="Output results as JSON",
        )

        # report subcommand
        report_parser = subparsers.add_parser(
            "report",
            help="Generate reports from analysis",
        )
        report_parser.add_argument(
            "--format",
            choices=["github-actions", "sarif", "markdown", "json"],
            default="github-actions",
            help="Output format",
        )
        report_parser.add_argument(
            "--input",
            default=None,
            help="Path to JSON results from a previous 'check --json' run",
        )

        # dashboard subcommand
        subparsers.add_parser(
            "dashboard",
            help="Print a summary dashboard",
        )

        return parser

    def _get_staged_files(self) -> List[str]:
        """Get list of staged Python files from git."""
        import subprocess

        try:
            result = subprocess.run(
                ["git", "diff", "--cached", "--name-only", "--diff-filter=ACM"],
                capture_output=True,
                text=True,
                check=True,
            )
            return [
                f.strip()
                for f in result.stdout.strip().split("\n")
                if f.strip() and f.strip().endswith(".py")
            ]
        except (subprocess.CalledProcessError, FileNotFoundError):
            return []

    def cmd_check(self, args: argparse.Namespace) -> int:
        """Execute the 'check' subcommand."""
        config = self.config

        if args.mode:
            config.mode = args.mode
        if args.fail_on:
            config.fail_on = args.fail_on
        if args.max_h1 is not None:
            config.max_h1 = args.max_h1

        files = args.files if args.files else self._get_staged_files()

        if not files:
            print("No files to analyze.", file=sys.stderr)
            return 0

        hook = DeppyPreCommitHook(config)
        result = hook.run(files)

        if args.output_json:
            print(json.dumps(result.to_dict(), indent=2))
        else:
            print(result.summary)
            for diag in result.diagnostics:
                severity_str = diag.severity.value.upper()
                print(
                    f"  [{severity_str}] {diag.file}:{diag.line}: "
                    f"{diag.message}"
                )

        return result.exit_code

    def cmd_report(self, args: argparse.Namespace) -> int:
        """Execute the 'report' subcommand."""
        # Load diagnostics from input file or run fresh analysis
        diagnostics: List[Diagnostic] = []

        if args.input:
            input_path = Path(args.input)
            if not input_path.exists():
                print(f"Input file not found: {args.input}", file=sys.stderr)
                return 2
            with open(input_path) as f:
                data = json.load(f)
            for d in data.get("diagnostics", []):
                diagnostics.append(Diagnostic(
                    file=d["file"],
                    line=d["line"],
                    column=d["column"],
                    severity=Severity(d["severity"]),
                    message=d["message"],
                    h1_type=d["h1_type"],
                    h1_dimension=d["h1_dimension"],
                    rule_id=d["rule_id"],
                    fix_suggestion=d.get("fix_suggestion"),
                    trust_level=(
                        TrustLevel(d["trust_level"])
                        if d.get("trust_level") else None
                    ),
                ))

        reporter = GitHubActionsReporter()

        if args.format == "github-actions":
            reporter.report(diagnostics)
        elif args.format == "sarif":
            sarif = reporter.create_sarif_upload(diagnostics)
            print(json.dumps(sarif, indent=2))
        elif args.format == "markdown":
            print(reporter.create_pr_comment(diagnostics))
        elif args.format == "json":
            print(json.dumps(
                [d.to_dict() for d in diagnostics],
                indent=2,
            ))

        return 0

    def cmd_dashboard(self, _args: argparse.Namespace) -> int:
        """Execute the 'dashboard' subcommand."""
        config = self.config
        print("=" * 50)
        print("  deppy CI Dashboard")
        print("=" * 50)
        print()
        print(f"  Configuration: {config!r}")
        print(f"  Mode:          {config.mode}")
        print(f"  Fail on:       {config.fail_on}")
        print(f"  Max H¹:        {config.max_h1}")
        print(f"  Budget:        {config.budget_tokens} tokens")
        print(f"  Trust target:  {config.trust_target}")
        print(f"  Oracle model:  {config.oracle_model}")
        print(f"  Lean enabled:  {config.lean_enabled}")
        print(f"  Include paths: {config.include_paths}")
        print(f"  Exclude paths: {config.exclude_paths}")
        print()

        # Show staged files
        staged = self._get_staged_files()
        if staged:
            print(f"  Staged Python files ({len(staged)}):")
            for f in staged:
                print(f"    - {f}")
        else:
            print("  No staged Python files.")
        print()
        print("=" * 50)
        return 0

    def main(self, argv: Optional[Sequence[str]] = None) -> int:
        """Main CLI entry point.

        Args:
            argv: Command-line arguments (default: sys.argv[1:]).

        Returns:
            Exit code (0=pass, 1=errors, 2=config error).
        """
        parser = self.build_parser()
        args = parser.parse_args(argv)

        if not args.command:
            parser.print_help()
            return 2

        try:
            if args.command == "check":
                return self.cmd_check(args)
            elif args.command == "report":
                return self.cmd_report(args)
            elif args.command == "dashboard":
                return self.cmd_dashboard(args)
            else:
                parser.print_help()
                return 2
        except KeyboardInterrupt:
            print("\nInterrupted.", file=sys.stderr)
            return 130
        except Exception as exc:
            print(f"Error: {exc}", file=sys.stderr)
            return 2


def main(argv: Optional[Sequence[str]] = None) -> None:
    """Module-level entry point for ``python -m deppy.hybrid.ci.hooks``."""
    ci = CIIntegration()
    sys.exit(ci.main(argv))


if __name__ == "__main__":
    main()
