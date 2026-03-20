"""
Gradual trust visualization — the trust presheaf rendered as a dashboard.
=========================================================================

The *trust level* at each code site is a local section of the trust presheaf

    Trust : S^op → {UNTRUSTED, LLM_JUDGED, PROPERTY_CHECKED, Z3_PROVEN, LEAN_VERIFIED}

A consistent global section means the project has a uniform trust guarantee.
In practice, trust is heterogeneous: some functions are proven, others are
just vibes.  This module visualises that heterogeneity so developers can
see *where they are* and *what it would cost* to level up.

Usage
-----
>>> from deppy.hybrid.diagnostics.trust_dashboard import TrustDashboard
>>> dashboard = TrustDashboard.from_directory("src/")
>>> print(dashboard.render_terminal())
"""

from __future__ import annotations

import json
import math
import os
import textwrap
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Dict,
    Iterable,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

try:
    import z3 as _z3

    _HAS_Z3 = True
except ImportError:
    _z3 = None  # type: ignore[assignment]
    _HAS_Z3 = False

if TYPE_CHECKING:
    from deppy.hybrid.diagnostics.localization import CheckResult

import logging


# --- Integration with existing deppy codebase ---
try:
    from deppy.kernel.trust_classifier import TrustClassifier as _CoreTrustClassifier, trust_rank
    from deppy.core._protocols import TrustLevel as _CoreTrustLevel
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

logger = logging.getLogger(__name__)


# ═══════════════════════════════════════════════════════════════════════════════
# Trust level constants & ordering
# ═══════════════════════════════════════════════════════════════════════════════

TRUST_UNTRUSTED = "UNTRUSTED"
TRUST_LLM_JUDGED = "LLM_JUDGED"
TRUST_PROPERTY_CHECKED = "PROPERTY_CHECKED"
TRUST_Z3_PROVEN = "Z3_PROVEN"
TRUST_LEAN_VERIFIED = "LEAN_VERIFIED"

TRUST_LEVELS: List[str] = [
    TRUST_UNTRUSTED,
    TRUST_LLM_JUDGED,
    TRUST_PROPERTY_CHECKED,
    TRUST_Z3_PROVEN,
    TRUST_LEAN_VERIFIED,
]

_TRUST_ORDER: Dict[str, int] = {lvl: i for i, lvl in enumerate(TRUST_LEVELS)}

# ANSI colours
_RESET = "\033[0m"
_BOLD = "\033[1m"
_DIM = "\033[2m"
_RED = "\033[31m"
_YELLOW = "\033[33m"
_GREEN = "\033[32m"
_BLUE = "\033[34m"
_MAGENTA = "\033[35m"
_CYAN = "\033[36m"
_WHITE = "\033[37m"
_BG_RED = "\033[41m"
_BG_YELLOW = "\033[43m"
_BG_GREEN = "\033[42m"
_BG_BLUE = "\033[44m"
_BG_MAGENTA = "\033[45m"

_TRUST_COLOUR: Dict[str, str] = {
    TRUST_UNTRUSTED: _RED,
    TRUST_LLM_JUDGED: _YELLOW,
    TRUST_PROPERTY_CHECKED: _GREEN,
    TRUST_Z3_PROVEN: _BLUE,
    TRUST_LEAN_VERIFIED: _MAGENTA,
}

_TRUST_BG: Dict[str, str] = {
    TRUST_UNTRUSTED: _BG_RED,
    TRUST_LLM_JUDGED: _BG_YELLOW,
    TRUST_PROPERTY_CHECKED: _BG_GREEN,
    TRUST_Z3_PROVEN: _BG_BLUE,
    TRUST_LEAN_VERIFIED: _BG_MAGENTA,
}

_TRUST_ICON: Dict[str, str] = {
    TRUST_UNTRUSTED: "✖",
    TRUST_LLM_JUDGED: "🤖",
    TRUST_PROPERTY_CHECKED: "✔",
    TRUST_Z3_PROVEN: "⊢",
    TRUST_LEAN_VERIFIED: "🏆",
}

_TRUST_LABEL: Dict[str, str] = {
    TRUST_UNTRUSTED: "Untrusted",
    TRUST_LLM_JUDGED: "LLM Judged",
    TRUST_PROPERTY_CHECKED: "Property Checked",
    TRUST_Z3_PROVEN: "Z3 Proven",
    TRUST_LEAN_VERIFIED: "Lean Verified",
}


def trust_ge(a: str, b: str) -> bool:
    """Return True if trust level *a* is at least as strong as *b*."""
    return _TRUST_ORDER.get(a, -1) >= _TRUST_ORDER.get(b, -1)


def trust_min(levels: Iterable[str]) -> str:
    """Return the weakest trust level in the collection."""
    result = TRUST_LEAN_VERIFIED
    for lvl in levels:
        if _TRUST_ORDER.get(lvl, -1) < _TRUST_ORDER.get(result, 99):
            result = lvl
    return result


# ═══════════════════════════════════════════════════════════════════════════════
# Data containers
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class FunctionTrust:
    """Trust information for a single function/method."""

    file_path: str = ""
    function_name: str = ""
    trust_level: str = TRUST_UNTRUSTED
    n_diagnostics: int = 0
    n_errors: int = 0
    n_warnings: int = 0
    has_docstring: bool = False
    has_type_annotations: bool = False
    has_assertions: bool = False
    h1_dimension: int = 0

    @property
    def qualified_name(self) -> str:
        return f"{self.file_path}::{self.function_name}"


@dataclass
class FileTrust:
    """Trust information aggregated for a single file."""

    file_path: str = ""
    trust_level: str = TRUST_UNTRUSTED
    functions: List[FunctionTrust] = field(default_factory=list)
    n_diagnostics: int = 0
    n_functions: int = 0
    h1_dimension: int = 0

    @property
    def trust_distribution(self) -> Dict[str, int]:
        counts: Dict[str, int] = {lvl: 0 for lvl in TRUST_LEVELS}
        for fn in self.functions:
            if fn.trust_level in counts:
                counts[fn.trust_level] += 1
        return counts


@dataclass
class PromotionAdvice:
    """Advice for promoting one site to a higher trust level.

    Attributes
    ----------
    target:
        The function or file being advised about.
    current_level:
        Current trust level.
    next_level:
        The proposed next trust level.
    action_needed:
        Human-readable description of what to do.
    estimated_cost_tokens:
        Estimated LLM tokens to perform this action.
    estimated_cost_dollars:
        Estimated cost in USD (at ~$3/1M input tokens).
    """

    target: str = ""
    current_level: str = TRUST_UNTRUSTED
    next_level: str = TRUST_LLM_JUDGED
    action_needed: str = ""
    estimated_cost_tokens: int = 0
    estimated_cost_dollars: float = 0.0

    @property
    def roi_score(self) -> float:
        """Higher is better — trust steps gained per dollar."""
        step = _TRUST_ORDER.get(self.next_level, 0) - _TRUST_ORDER.get(
            self.current_level, 0
        )
        if self.estimated_cost_dollars <= 0:
            return float("inf") if step > 0 else 0.0
        return step / self.estimated_cost_dollars

    def to_dict(self) -> Dict[str, Any]:
        return {
            "target": self.target,
            "current_level": self.current_level,
            "next_level": self.next_level,
            "action_needed": self.action_needed,
            "estimated_cost_tokens": self.estimated_cost_tokens,
            "estimated_cost_dollars": self.estimated_cost_dollars,
            "roi_score": self.roi_score,
        }


@dataclass
class CostEstimate:
    """Estimated cost of verifying to a target trust level.

    Attributes
    ----------
    oracle_tokens:
        Total LLM tokens needed.
    oracle_cost_usd:
        Total LLM cost in USD.
    z3_time_seconds:
        Estimated Z3 solving time.
    lean_obligations:
        Number of Lean proof obligations to discharge.
    """

    oracle_tokens: int = 0
    oracle_cost_usd: float = 0.0
    z3_time_seconds: float = 0.0
    lean_obligations: int = 0

    def to_dict(self) -> Dict[str, Any]:
        return {
            "oracle_tokens": self.oracle_tokens,
            "oracle_cost_usd": self.oracle_cost_usd,
            "z3_time_seconds": self.z3_time_seconds,
            "lean_obligations": self.lean_obligations,
        }

    def summary(self) -> str:
        parts: List[str] = []
        if self.oracle_tokens:
            parts.append(f"{self.oracle_tokens:,} tokens (${self.oracle_cost_usd:.2f})")
        if self.z3_time_seconds:
            parts.append(f"~{self.z3_time_seconds:.1f}s Z3 time")
        if self.lean_obligations:
            parts.append(f"{self.lean_obligations} Lean obligations")
        return ", ".join(parts) or "free"


# ═══════════════════════════════════════════════════════════════════════════════
# TrustDashboard — aggregate trust view
# ═══════════════════════════════════════════════════════════════════════════════


class TrustDashboard:
    """Aggregate trust visualization over a codebase or set of check results.

    The trust level is a global section of the trust presheaf; this class
    collects per-file and per-function sections and renders them.

    Parameters
    ----------
    file_trusts:
        Mapping from file path to :class:`FileTrust`.
    """

    def __init__(self, file_trusts: Optional[Dict[str, FileTrust]] = None) -> None:
        self._files: Dict[str, FileTrust] = file_trusts or {}

    # ------------------------------------------------------------------
    # Constructors
    # ------------------------------------------------------------------

    @classmethod
    def from_check_results(cls, results: Sequence[CheckResult]) -> TrustDashboard:
        """Build a dashboard from a list of :class:`CheckResult` objects."""
        file_trusts: Dict[str, FileTrust] = {}

        for result in results:
            fp = result.file_path
            ft = FileTrust(
                file_path=fp,
                n_diagnostics=len(result.diagnostics),
                h1_dimension=result.h1_dimension,
            )

            # Group diagnostics by function (if available via code attribute)
            func_groups: Dict[str, List[Any]] = defaultdict(list)
            for diag in result.diagnostics:
                # Extract function name from the code fragment or h1_generator
                func_name = _extract_function_name(diag)
                func_groups[func_name].append(diag)

            for func_name, diags in func_groups.items():
                worst_trust = TRUST_LEAN_VERIFIED
                n_err = 0
                n_warn = 0
                for d in diags:
                    if _TRUST_ORDER.get(d.trust_level, 0) < _TRUST_ORDER.get(
                        worst_trust, 99
                    ):
                        worst_trust = d.trust_level
                    if d.severity.value == "error":
                        n_err += 1
                    elif d.severity.value == "warning":
                        n_warn += 1

                fn_trust = FunctionTrust(
                    file_path=fp,
                    function_name=func_name,
                    trust_level=worst_trust,
                    n_diagnostics=len(diags),
                    n_errors=n_err,
                    n_warnings=n_warn,
                )
                ft.functions.append(fn_trust)

            ft.n_functions = len(ft.functions)
            if ft.functions:
                ft.trust_level = trust_min(fn.trust_level for fn in ft.functions)
            else:
                # No diagnostics → assume the file is at least property-checked
                ft.trust_level = (
                    TRUST_PROPERTY_CHECKED if not result.diagnostics else TRUST_UNTRUSTED
                )

            file_trusts[fp] = ft

        return cls(file_trusts)

    @classmethod
    def from_directory(
        cls,
        dir_path: str,
        glob_pattern: str = "**/*.py",
    ) -> TrustDashboard:
        """Check a directory and build a dashboard.

        This is a convenience that imports :class:`ExistingCodeChecker`
        and runs it over all matching files.
        """
        from deppy.hybrid.diagnostics.localization import ExistingCodeChecker

        checker = ExistingCodeChecker()
        result = checker.check_directory(dir_path, glob=glob_pattern)
        return cls.from_check_results([result])

    # ------------------------------------------------------------------
    # Queries
    # ------------------------------------------------------------------

    @property
    def files(self) -> Dict[str, FileTrust]:
        return dict(self._files)

    def overall_trust(self) -> Dict[str, Any]:
        """Overall trust distribution as percentages.

        Returns a dict like::

            {
                "UNTRUSTED": 15.0,
                "LLM_JUDGED": 40.0,
                "PROPERTY_CHECKED": 30.0,
                "Z3_PROVEN": 10.0,
                "LEAN_VERIFIED": 5.0,
                "total_functions": 200,
                "overall_level": "UNTRUSTED",
            }
        """
        counter: Dict[str, int] = {lvl: 0 for lvl in TRUST_LEVELS}
        total = 0
        for ft in self._files.values():
            for fn in ft.functions:
                if fn.trust_level in counter:
                    counter[fn.trust_level] += 1
                total += 1

        if total == 0:
            return {
                **{lvl: 0.0 for lvl in TRUST_LEVELS},
                "total_functions": 0,
                "overall_level": TRUST_UNTRUSTED,
            }

        pcts = {lvl: round(100.0 * cnt / total, 1) for lvl, cnt in counter.items()}
        all_levels = [fn.trust_level for ft in self._files.values() for fn in ft.functions]
        overall = trust_min(all_levels) if all_levels else TRUST_UNTRUSTED

        return {
            **pcts,
            "total_functions": total,
            "overall_level": overall,
        }

    def per_file_trust(self) -> Dict[str, Dict[str, Any]]:
        """Per-file trust breakdown."""
        result: Dict[str, Dict[str, Any]] = {}
        for fp, ft in sorted(self._files.items()):
            dist = ft.trust_distribution
            total = sum(dist.values())
            pcts = (
                {lvl: round(100.0 * cnt / total, 1) for lvl, cnt in dist.items()}
                if total
                else {lvl: 0.0 for lvl in TRUST_LEVELS}
            )
            result[fp] = {
                "trust_level": ft.trust_level,
                "n_functions": ft.n_functions,
                "n_diagnostics": ft.n_diagnostics,
                "h1_dimension": ft.h1_dimension,
                "distribution": pcts,
            }
        return result

    def per_function_trust(self) -> Dict[str, Dict[str, Any]]:
        """Per-function trust breakdown."""
        result: Dict[str, Dict[str, Any]] = {}
        for ft in self._files.values():
            for fn in ft.functions:
                result[fn.qualified_name] = {
                    "trust_level": fn.trust_level,
                    "n_diagnostics": fn.n_diagnostics,
                    "n_errors": fn.n_errors,
                    "n_warnings": fn.n_warnings,
                    "has_docstring": fn.has_docstring,
                    "has_type_annotations": fn.has_type_annotations,
                    "has_assertions": fn.has_assertions,
                }
        return result

    # ------------------------------------------------------------------
    # Terminal rendering
    # ------------------------------------------------------------------

    def render_terminal(self, width: int = 80) -> str:
        """Coloured terminal dashboard with progress bars."""
        lines: List[str] = []
        overall = self.overall_trust()

        # Header
        lines.append(f"{_BOLD}{'═' * width}{_RESET}")
        lines.append(f"{_BOLD}  deppy trust dashboard{_RESET}")
        lines.append(f"{_BOLD}{'═' * width}{_RESET}")
        lines.append("")

        # Overall trust bar
        total_fn = overall["total_functions"]
        overall_lvl = overall["overall_level"]
        clr = _TRUST_COLOUR.get(overall_lvl, "")
        icon = _TRUST_ICON.get(overall_lvl, "?")
        lines.append(
            f"  Overall: {clr}{icon} {_TRUST_LABEL.get(overall_lvl, overall_lvl)}{_RESET}"
            f"  ({total_fn} functions)"
        )
        lines.append("")

        # Distribution bar
        bar_width = width - 4
        lines.append("  " + self._trust_bar(overall, bar_width))
        lines.append("  " + self._trust_legend())
        lines.append("")

        # Per-file breakdown
        lines.append(f"  {_BOLD}Per-file breakdown:{_RESET}")
        lines.append(f"  {'─' * (width - 4)}")

        for fp, ft in sorted(self._files.items()):
            fclr = _TRUST_COLOUR.get(ft.trust_level, "")
            ficon = _TRUST_ICON.get(ft.trust_level, "?")
            short = _short_path(fp)
            diag_str = f"  {ft.n_diagnostics} diag" if ft.n_diagnostics else ""
            lines.append(
                f"  {fclr}{ficon}{_RESET} {short:<40} "
                f"{fclr}{ft.trust_level:<20}{_RESET}{diag_str}"
            )
            # Mini bar for each file
            if ft.functions:
                dist = ft.trust_distribution
                total = sum(dist.values())
                if total:
                    file_overall = {
                        lvl: round(100.0 * cnt / total, 1)
                        for lvl, cnt in dist.items()
                    }
                    lines.append("    " + self._trust_bar(file_overall, bar_width - 4))

        lines.append("")
        lines.append(f"{_BOLD}{'═' * width}{_RESET}")
        return "\n".join(lines)

    def _trust_bar(self, dist: Dict[str, Any], width: int) -> str:
        """Render a coloured progress bar from a trust distribution."""
        segments: List[Tuple[str, float]] = []
        for lvl in TRUST_LEVELS:
            pct = dist.get(lvl, 0.0)
            if isinstance(pct, (int, float)) and pct > 0:
                segments.append((lvl, pct))

        if not segments:
            return f"{_DIM}[{'·' * width}]{_RESET}"

        bar_chars: List[str] = []
        assigned = 0
        for lvl, pct in segments:
            n = max(1, round(pct / 100.0 * width)) if pct > 0 else 0
            n = min(n, width - assigned)
            bg = _TRUST_BG.get(lvl, "")
            bar_chars.append(f"{bg}{' ' * n}{_RESET}")
            assigned += n

        remaining = width - assigned
        if remaining > 0:
            bar_chars.append(f"{_DIM}{'·' * remaining}{_RESET}")

        return "[" + "".join(bar_chars) + "]"

    def _trust_legend(self) -> str:
        """Render the colour legend."""
        parts: List[str] = []
        for lvl in TRUST_LEVELS:
            clr = _TRUST_COLOUR.get(lvl, "")
            icon = _TRUST_ICON.get(lvl, "?")
            label = _TRUST_LABEL.get(lvl, lvl)
            parts.append(f"{clr}{icon} {label}{_RESET}")
        return "  ".join(parts)

    # ------------------------------------------------------------------
    # HTML rendering
    # ------------------------------------------------------------------

    def render_html(self) -> str:
        """HTML dashboard with heatmap and trust bars."""
        overall = self.overall_trust()
        per_file = self.per_file_trust()

        file_rows: List[str] = []
        for fp, info in sorted(per_file.items()):
            lvl = info["trust_level"]
            css_class = f"trust-{lvl.lower()}"
            dist = info.get("distribution", {})
            bar_segments: List[str] = []
            for t_lvl in TRUST_LEVELS:
                pct = dist.get(t_lvl, 0.0)
                if pct > 0:
                    bar_segments.append(
                        f'<div class="bar-segment bar-{t_lvl.lower()}" '
                        f'style="width:{pct}%" title="{t_lvl}: {pct}%"></div>'
                    )
            bar_html = "".join(bar_segments)
            file_rows.append(
                f"<tr class='{css_class}'>"
                f"<td>{_html_escape(fp)}</td>"
                f"<td>{lvl}</td>"
                f"<td>{info['n_functions']}</td>"
                f"<td>{info['n_diagnostics']}</td>"
                f"<td><div class='trust-bar'>{bar_html}</div></td>"
                f"</tr>"
            )

        table_body = "\n".join(file_rows)
        overall_lvl = overall["overall_level"]

        return (
            "<!DOCTYPE html>\n"
            '<html lang="en">\n'
            "<head>\n"
            '  <meta charset="utf-8">\n'
            "  <title>deppy trust dashboard</title>\n"
            "  <style>\n"
            "    body { font-family: 'SF Mono', monospace; margin: 2em; background: #1a1a2e; color: #e0e0e0; }\n"
            "    h1 { color: #4fc3f7; }\n"
            "    .overall { font-size: 1.3em; margin: 1em 0; padding: 1em; border-radius: 8px; }\n"
            "    .overall.trust-untrusted { background: #3a1515; border: 1px solid #f44; }\n"
            "    .overall.trust-llm_judged { background: #3a3515; border: 1px solid #fa0; }\n"
            "    .overall.trust-property_checked { background: #153a15; border: 1px solid #4a4; }\n"
            "    .overall.trust-z3_proven { background: #15153a; border: 1px solid #44f; }\n"
            "    .overall.trust-lean_verified { background: #3a153a; border: 1px solid #f4f; }\n"
            "    table { border-collapse: collapse; width: 100%%; margin-top: 1em; }\n"
            "    th, td { text-align: left; padding: 8px 12px; border-bottom: 1px solid #333; }\n"
            "    th { background: #252545; color: #8888cc; }\n"
            "    tr:hover { background: #252535; }\n"
            "    .trust-bar { display: flex; height: 16px; border-radius: 3px; overflow: hidden; background: #333; }\n"
            "    .bar-segment { height: 100%%; }\n"
            "    .bar-untrusted { background: #f44; }\n"
            "    .bar-llm_judged { background: #fa0; }\n"
            "    .bar-property_checked { background: #4a4; }\n"
            "    .bar-z3_proven { background: #44f; }\n"
            "    .bar-lean_verified { background: #f4f; }\n"
            "    .legend { margin: 1em 0; display: flex; gap: 1.5em; }\n"
            "    .legend-item { display: flex; align-items: center; gap: 0.4em; }\n"
            "    .legend-swatch { width: 14px; height: 14px; border-radius: 2px; }\n"
            "  </style>\n"
            "</head>\n"
            "<body>\n"
            f"  <h1>🔒 deppy trust dashboard</h1>\n"
            f'  <div class="overall trust-{overall_lvl.lower()}">\n'
            f"    Overall: <strong>{overall_lvl}</strong>"
            f" — {overall['total_functions']} functions\n"
            f"  </div>\n"
            '  <div class="legend">\n'
            '    <span class="legend-item"><span class="legend-swatch bar-untrusted"></span> Untrusted</span>\n'
            '    <span class="legend-item"><span class="legend-swatch bar-llm_judged"></span> LLM Judged</span>\n'
            '    <span class="legend-item"><span class="legend-swatch bar-property_checked"></span> Property Checked</span>\n'
            '    <span class="legend-item"><span class="legend-swatch bar-z3_proven"></span> Z3 Proven</span>\n'
            '    <span class="legend-item"><span class="legend-swatch bar-lean_verified"></span> Lean Verified</span>\n'
            "  </div>\n"
            "  <table>\n"
            "    <thead><tr><th>File</th><th>Trust</th><th>Functions</th><th>Diagnostics</th><th>Distribution</th></tr></thead>\n"
            f"    <tbody>\n{table_body}\n    </tbody>\n"
            "  </table>\n"
            "</body>\n"
            "</html>\n"
        )

    # ------------------------------------------------------------------
    # JSON rendering
    # ------------------------------------------------------------------

    def render_json(self) -> Dict[str, Any]:
        """Machine-readable JSON representation."""
        return {
            "version": "1.0",
            "tool": "deppy",
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "overall": self.overall_trust(),
            "per_file": self.per_file_trust(),
            "per_function": self.per_function_trust(),
        }


# ═══════════════════════════════════════════════════════════════════════════════
# TrustHeatmap — ASCII heatmap of the file tree
# ═══════════════════════════════════════════════════════════════════════════════


class TrustHeatmap:
    """Generate an ASCII heatmap of trust levels across the file tree.

    Colours:

    * 🔴 red    = UNTRUSTED
    * 🟡 yellow = LLM_JUDGED
    * 🟢 green  = PROPERTY_CHECKED
    * 🔵 blue   = Z3_PROVEN
    * 🟣 gold   = LEAN_VERIFIED
    """

    def __init__(self, colour: bool = True) -> None:
        self.colour = colour

    def generate(self, dashboard: TrustDashboard) -> str:
        """Generate the ASCII heatmap from a :class:`TrustDashboard`."""
        lines: List[str] = []
        files = dashboard.files
        if not files:
            return "  (no files)\n"

        # Build a tree structure
        tree = self._build_tree(files)

        # Render
        lines.append(f"{_BOLD}Trust Heatmap{_RESET}" if self.colour else "Trust Heatmap")
        lines.append("")
        self._render_tree(tree, lines, prefix="", is_last=True, depth=0)
        lines.append("")
        lines.append(self._legend())
        return "\n".join(lines)

    def _build_tree(
        self, files: Dict[str, FileTrust]
    ) -> Dict[str, Any]:
        """Build a nested dict representing the file tree."""
        tree: Dict[str, Any] = {}
        for fp, ft in sorted(files.items()):
            parts = Path(fp).parts
            current = tree
            for part in parts[:-1]:
                if part not in current:
                    current[part] = {}
                node = current[part]
                if isinstance(node, dict):
                    current = node
                else:
                    break
            if parts:
                current[parts[-1]] = ft
        return tree

    def _render_tree(
        self,
        tree: Dict[str, Any],
        lines: List[str],
        prefix: str,
        is_last: bool,
        depth: int,
    ) -> None:
        """Recursively render the tree with box-drawing characters."""
        entries = sorted(tree.items(), key=lambda kv: (not isinstance(kv[1], dict), kv[0]))
        for i, (name, value) in enumerate(entries):
            last = i == len(entries) - 1
            connector = "└── " if last else "├── "
            extension = "    " if last else "│   "

            if isinstance(value, FileTrust):
                # Leaf node: file
                clr = _TRUST_COLOUR.get(value.trust_level, "") if self.colour else ""
                rst = _RESET if self.colour else ""
                icon = _TRUST_ICON.get(value.trust_level, "?")
                bar = self._mini_bar(value)
                lines.append(f"{prefix}{connector}{clr}{icon} {name}{rst}  {bar}")

                # Show functions within the file
                for j, fn in enumerate(value.functions):
                    fn_last = j == len(value.functions) - 1
                    fn_conn = "└── " if fn_last else "├── "
                    fn_clr = _TRUST_COLOUR.get(fn.trust_level, "") if self.colour else ""
                    fn_icon = _TRUST_ICON.get(fn.trust_level, "?")
                    lines.append(
                        f"{prefix}{extension}    {fn_conn}"
                        f"{fn_clr}{fn_icon} {fn.function_name}{rst}"
                    )
            elif isinstance(value, dict):
                # Directory node
                dir_trust = self._aggregate_dir_trust(value)
                clr = _TRUST_COLOUR.get(dir_trust, "") if self.colour else ""
                rst = _RESET if self.colour else ""
                icon = _TRUST_ICON.get(dir_trust, "?")
                lines.append(f"{prefix}{connector}{clr}{icon} {name}/{rst}")
                self._render_tree(value, lines, prefix + extension, last, depth + 1)

    def _aggregate_dir_trust(self, tree: Dict[str, Any]) -> str:
        """Compute the aggregate trust of a directory (worst of children)."""
        levels: List[str] = []
        for value in tree.values():
            if isinstance(value, FileTrust):
                levels.append(value.trust_level)
            elif isinstance(value, dict):
                levels.append(self._aggregate_dir_trust(value))
        return trust_min(levels) if levels else TRUST_UNTRUSTED

    def _mini_bar(self, ft: FileTrust) -> str:
        """A compact inline bar showing the function trust distribution."""
        if not ft.functions:
            return ""
        dist = ft.trust_distribution
        total = sum(dist.values())
        if total == 0:
            return ""

        bar_width = 20
        chars: List[str] = []
        assigned = 0
        for lvl in TRUST_LEVELS:
            cnt = dist.get(lvl, 0)
            if cnt == 0:
                continue
            n = max(1, round(cnt / total * bar_width))
            n = min(n, bar_width - assigned)
            if self.colour:
                bg = _TRUST_BG.get(lvl, "")
                chars.append(f"{bg}{' ' * n}{_RESET}")
            else:
                char = lvl[0]
                chars.append(char * n)
            assigned += n

        remaining = bar_width - assigned
        if remaining > 0:
            dim = _DIM if self.colour else ""
            rst = _RESET if self.colour else ""
            chars.append(f"{dim}{'·' * remaining}{rst}")

        return "[" + "".join(chars) + "]"

    def _legend(self) -> str:
        """Trust level legend."""
        parts: List[str] = []
        for lvl in TRUST_LEVELS:
            clr = _TRUST_COLOUR.get(lvl, "") if self.colour else ""
            rst = _RESET if self.colour else ""
            icon = _TRUST_ICON.get(lvl, "?")
            label = _TRUST_LABEL.get(lvl, lvl)
            parts.append(f"  {clr}{icon} {label}{rst}")
        return "Legend:\n" + "\n".join(parts)


# ═══════════════════════════════════════════════════════════════════════════════
# PromotionAdvisor — cheapest path to higher trust
# ═══════════════════════════════════════════════════════════════════════════════

# Cost model (approximate):
#   UNTRUSTED → LLM_JUDGED:       ~500 tokens ($0.0015)  — just ask the oracle
#   LLM_JUDGED → PROPERTY_CHECKED: ~2000 tokens ($0.006) — generate property test
#   PROPERTY_CHECKED → Z3_PROVEN:   ~5000 tokens ($0.015) + ~2s Z3 time
#   Z3_PROVEN → LEAN_VERIFIED:     ~10000 tokens ($0.03) + 1 Lean obligation

_PROMOTION_COSTS: Dict[Tuple[str, str], Dict[str, Any]] = {
    (TRUST_UNTRUSTED, TRUST_LLM_JUDGED): {
        "action": "Run LLM oracle check (add a docstring if missing)",
        "tokens": 500,
        "usd": 0.0015,
        "z3_sec": 0.0,
        "lean": 0,
    },
    (TRUST_LLM_JUDGED, TRUST_PROPERTY_CHECKED): {
        "action": "Add a property-based test or runtime check",
        "tokens": 2000,
        "usd": 0.006,
        "z3_sec": 0.0,
        "lean": 0,
    },
    (TRUST_PROPERTY_CHECKED, TRUST_Z3_PROVEN): {
        "action": "Encode the property as a Z3 constraint and prove it",
        "tokens": 5000,
        "usd": 0.015,
        "z3_sec": 2.0,
        "lean": 0,
    },
    (TRUST_Z3_PROVEN, TRUST_LEAN_VERIFIED): {
        "action": "Translate Z3 proof to Lean and verify in the kernel",
        "tokens": 10000,
        "usd": 0.03,
        "z3_sec": 0.0,
        "lean": 1,
    },
}

# Extra heuristic costs for common promotions from UNTRUSTED
_HEURISTIC_ACTIONS: Dict[str, Dict[str, Any]] = {
    "add_type_hint": {
        "action": "Add type annotations (return type + parameters)",
        "tokens": 200,
        "usd": 0.0006,
    },
    "add_docstring": {
        "action": "Add a docstring describing the function's contract",
        "tokens": 300,
        "usd": 0.0009,
    },
    "add_assertion": {
        "action": "Add assert statements for preconditions",
        "tokens": 150,
        "usd": 0.00045,
    },
}


class PromotionAdvisor:
    """Advise on the cheapest way to promote trust levels.

    Ranks promotions by ROI: cheapest-per-trust-step first.
    """

    def advise(self, dashboard: TrustDashboard) -> List[PromotionAdvice]:
        """Generate promotion advice for all functions in the dashboard.

        Returns a list of :class:`PromotionAdvice` sorted by ROI (best first).
        """
        advice_list: List[PromotionAdvice] = []

        for ft in dashboard.files.values():
            for fn in ft.functions:
                next_promotions = self._next_promotions(fn)
                advice_list.extend(next_promotions)

        # Sort by ROI (descending) — cheapest wins
        advice_list.sort(key=lambda a: -a.roi_score)
        return advice_list

    def cheapest_path_to(
        self,
        dashboard: TrustDashboard,
        target_trust: str,
    ) -> List[PromotionAdvice]:
        """Compute the cheapest promotion path to reach *target_trust* globally.

        Returns the ordered list of promotions needed, cheapest first.
        """
        target_order = _TRUST_ORDER.get(target_trust, 0)
        needed: List[PromotionAdvice] = []

        for ft in dashboard.files.values():
            for fn in ft.functions:
                current_order = _TRUST_ORDER.get(fn.trust_level, 0)
                if current_order >= target_order:
                    continue

                # Walk up the lattice
                current = fn.trust_level
                while _TRUST_ORDER.get(current, 0) < target_order:
                    next_lvl = self._next_level(current)
                    if next_lvl is None:
                        break
                    pair = (current, next_lvl)
                    cost_info = _PROMOTION_COSTS.get(pair, {})
                    needed.append(
                        PromotionAdvice(
                            target=fn.qualified_name,
                            current_level=current,
                            next_level=next_lvl,
                            action_needed=cost_info.get(
                                "action", f"Promote from {current} to {next_lvl}"
                            ),
                            estimated_cost_tokens=cost_info.get("tokens", 0),
                            estimated_cost_dollars=cost_info.get("usd", 0.0),
                        )
                    )
                    current = next_lvl

        needed.sort(key=lambda a: -a.roi_score)
        return needed

    def _next_promotions(self, fn: FunctionTrust) -> List[PromotionAdvice]:
        """Get the immediate next promotion(s) for a function."""
        promotions: List[PromotionAdvice] = []
        next_lvl = self._next_level(fn.trust_level)
        if next_lvl is None:
            return promotions

        pair = (fn.trust_level, next_lvl)
        cost_info = _PROMOTION_COSTS.get(pair, {})

        promotions.append(
            PromotionAdvice(
                target=fn.qualified_name,
                current_level=fn.trust_level,
                next_level=next_lvl,
                action_needed=cost_info.get(
                    "action", f"Promote from {fn.trust_level} to {next_lvl}"
                ),
                estimated_cost_tokens=cost_info.get("tokens", 0),
                estimated_cost_dollars=cost_info.get("usd", 0.0),
            )
        )

        # Also suggest heuristic micro-actions for UNTRUSTED functions
        if fn.trust_level == TRUST_UNTRUSTED:
            for key, info in _HEURISTIC_ACTIONS.items():
                promotions.append(
                    PromotionAdvice(
                        target=fn.qualified_name,
                        current_level=TRUST_UNTRUSTED,
                        next_level=TRUST_LLM_JUDGED,
                        action_needed=info["action"],
                        estimated_cost_tokens=info["tokens"],
                        estimated_cost_dollars=info["usd"],
                    )
                )

        return promotions

    def _next_level(self, current: str) -> Optional[str]:
        """Return the next trust level above *current*, or None if at top."""
        idx = _TRUST_ORDER.get(current, -1)
        if idx < 0 or idx >= len(TRUST_LEVELS) - 1:
            return None
        return TRUST_LEVELS[idx + 1]


# ═══════════════════════════════════════════════════════════════════════════════
# CostEstimator — estimate verification costs per mode
# ═══════════════════════════════════════════════════════════════════════════════

# Verification modes (from cheap to thorough)
MODE_FREE = "free"
MODE_CHEAP = "cheap"
MODE_STANDARD = "standard"
MODE_THOROUGH = "thorough"

# What trust level does each mode aim for?
_MODE_TARGET: Dict[str, str] = {
    MODE_FREE: TRUST_UNTRUSTED,      # just parse — no verification
    MODE_CHEAP: TRUST_LLM_JUDGED,    # LLM oracle only
    MODE_STANDARD: TRUST_Z3_PROVEN,  # Z3 proofs where possible
    MODE_THOROUGH: TRUST_LEAN_VERIFIED,  # full Lean verification
}


class CostEstimator:
    """Estimate the cost of verifying to a target trust mode.

    Modes:

    * **free** — no verification, just parse
    * **cheap** — LLM oracle checks only
    * **standard** — Z3 proofs where possible
    * **thorough** — full Lean verification
    """

    def estimate_verification_cost(
        self,
        dashboard: TrustDashboard,
        target_mode: str = MODE_STANDARD,
    ) -> CostEstimate:
        """Estimate the total cost to bring the codebase to *target_mode*.

        Parameters
        ----------
        dashboard:
            Current trust state.
        target_mode:
            One of ``"free"``, ``"cheap"``, ``"standard"``, ``"thorough"``.

        Returns
        -------
        CostEstimate
        """
        target_trust = _MODE_TARGET.get(target_mode, TRUST_UNTRUSTED)
        target_order = _TRUST_ORDER.get(target_trust, 0)

        total_tokens = 0
        total_usd = 0.0
        total_z3 = 0.0
        total_lean = 0

        for ft in dashboard.files.values():
            for fn in ft.functions:
                current_order = _TRUST_ORDER.get(fn.trust_level, 0)
                if current_order >= target_order:
                    continue

                # Walk up the lattice
                current = fn.trust_level
                while _TRUST_ORDER.get(current, 0) < target_order:
                    next_lvl = self._next_level(current)
                    if next_lvl is None:
                        break
                    pair = (current, next_lvl)
                    cost_info = _PROMOTION_COSTS.get(pair, {})
                    total_tokens += cost_info.get("tokens", 0)
                    total_usd += cost_info.get("usd", 0.0)
                    total_z3 += cost_info.get("z3_sec", 0.0)
                    total_lean += cost_info.get("lean", 0)
                    current = next_lvl

        return CostEstimate(
            oracle_tokens=total_tokens,
            oracle_cost_usd=round(total_usd, 4),
            z3_time_seconds=round(total_z3, 1),
            lean_obligations=total_lean,
        )

    def estimate_all_modes(
        self, dashboard: TrustDashboard
    ) -> Dict[str, CostEstimate]:
        """Estimate costs for all verification modes."""
        return {
            mode: self.estimate_verification_cost(dashboard, mode)
            for mode in (MODE_FREE, MODE_CHEAP, MODE_STANDARD, MODE_THOROUGH)
        }

    def render_cost_table(self, dashboard: TrustDashboard) -> str:
        """Render a terminal-friendly cost comparison table."""
        estimates = self.estimate_all_modes(dashboard)
        lines: List[str] = []
        lines.append(f"{'Mode':<12} {'Tokens':>10} {'Cost':>10} {'Z3 Time':>10} {'Lean':>6}")
        lines.append("─" * 52)
        for mode in (MODE_FREE, MODE_CHEAP, MODE_STANDARD, MODE_THOROUGH):
            est = estimates[mode]
            lines.append(
                f"{mode:<12} {est.oracle_tokens:>10,} "
                f"{'$' + f'{est.oracle_cost_usd:.4f}':>10} "
                f"{est.z3_time_seconds:>9.1f}s "
                f"{est.lean_obligations:>5}"
            )
        return "\n".join(lines)

    def _next_level(self, current: str) -> Optional[str]:
        idx = _TRUST_ORDER.get(current, -1)
        if idx < 0 or idx >= len(TRUST_LEVELS) - 1:
            return None
        return TRUST_LEVELS[idx + 1]


# ═══════════════════════════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════════════════════════


def _extract_function_name(diag: Any) -> str:
    """Best-effort extraction of function name from a diagnostic."""
    # Try h1_generator (e.g., "H1_IS_my_func" → "my_func")
    h1 = getattr(diag, "h1_generator", None)
    if h1 and isinstance(h1, str):
        for prefix in ("H1_IS_", "H1_IC_", "H1_SC_", "H1_EC_", "H1_EP_", "H1_PC_"):
            if h1.startswith(prefix):
                return h1[len(prefix):]

    # Try parsing from code attribute
    code = getattr(diag, "code", "")
    if code:
        return code

    return "<unknown>"


def _short_path(path: str, max_parts: int = 3) -> str:
    """Shorten a path for display."""
    parts = Path(path).parts
    if len(parts) <= max_parts:
        return str(Path(*parts)) if parts else path
    return str(Path("...", *parts[-max_parts:]))


def _html_escape(text: str) -> str:
    """Minimal HTML escaping."""
    return (
        text.replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
    )
