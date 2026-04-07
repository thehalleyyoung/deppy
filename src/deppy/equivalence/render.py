"""Diagnostic rendering for equivalence results.

Provides multiple output formats for equivalence verdicts:
- Plain text (terminal)
- Structured JSON
- SARIF (Static Analysis Results Interchange Format)
- Detailed site-by-site comparison

Each renderer consumes an EquivalenceJudgment and produces formatted output.
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from typing import (
    Any,
    Dict,
    List,
    Optional,
)

from deppy.core._protocols import SiteId
from deppy.equivalence._protocols import (
    EquivalenceJudgment,
    EquivalenceObstruction,
    EquivalenceObstructionKind,
    EquivalenceVerdict,
    LocalEquivalenceJudgment,
)
from deppy.equivalence.obstruction import (
    ObstructionClassifier,
    ObstructionSummary,
    summarise_obstructions,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Terminal renderer
# ═══════════════════════════════════════════════════════════════════════════════


class EquivalenceTerminalRenderer:
    """Render equivalence results for terminal output."""

    VERDICT_SYMBOLS = {
        EquivalenceVerdict.EQUIVALENT: "✅",
        EquivalenceVerdict.INEQUIVALENT: "❌",
        EquivalenceVerdict.REFINED: "⊑",
        EquivalenceVerdict.UNKNOWN: "❓",
    }

    VERDICT_COLORS = {
        EquivalenceVerdict.EQUIVALENT: "\033[32m",  # green
        EquivalenceVerdict.INEQUIVALENT: "\033[31m",  # red
        EquivalenceVerdict.REFINED: "\033[33m",  # yellow
        EquivalenceVerdict.UNKNOWN: "\033[90m",  # grey
    }

    RESET = "\033[0m"

    def __init__(self, use_color: bool = True, verbose: bool = False) -> None:
        self._use_color = use_color
        self._verbose = verbose

    def render(self, judgment: EquivalenceJudgment) -> str:
        """Render the full equivalence verdict."""
        lines: List[str] = []

        # Header
        lines.append(self._header(judgment))
        lines.append("")

        # Program info
        lines.append(f"  Program f: {judgment.program_f.name} ({judgment.program_f.source_path})")
        lines.append(f"  Program g: {judgment.program_g.name} ({judgment.program_g.source_path})")
        lines.append("")

        # Verdict
        symbol = self.VERDICT_SYMBOLS.get(judgment.verdict, "?")
        color = self.VERDICT_COLORS.get(judgment.verdict, "") if self._use_color else ""
        reset = self.RESET if self._use_color else ""
        lines.append(f"  Verdict: {color}{symbol} {judgment.verdict.value}{reset}")
        lines.append(f"  Strength: {judgment.strength.value}")
        lines.append("")

        # Site-by-site results
        if judgment.local_judgments:
            lines.append("  Site-by-Site Analysis:")
            lines.append("  " + "─" * 60)

            for j in judgment.local_judgments.values():
                lines.append(self._render_local_judgment(j))

            lines.append("")

        # Obstructions
        if judgment.obstructions:
            lines.append(f"  Obstructions ({len(judgment.obstructions)}):")
            lines.append("  " + "─" * 60)

            for obs in judgment.obstructions:
                lines.append(self._render_obstruction(obs))

            lines.append("")

        # Cohomology
        if judgment.cohomology_class is not None:
            h1 = judgment.cohomology_class
            h1_status = "trivial" if h1.is_trivial else "non-trivial"
            lines.append(f"  H¹(U, Iso(Sem_f, Sem_g)): {h1_status}")
            if h1.obstruction_count > 0:
                lines.append(f"  Obstruction classes: {h1.obstruction_count}")
            lines.append("")

        # Natural transformation
        if judgment.natural_transformation is not None:
            nt = judgment.natural_transformation
            lines.append(f"  Natural transformation η: Sem_f ⇒ Sem_g")
            lines.append(f"    Natural: {'yes' if nt.is_natural else 'no'}")
            lines.append(f"    Isomorphism: {'yes' if nt.is_isomorphism else 'no'}")
            lines.append(f"    Components: {len(nt.components)}")
            lines.append("")

        # Timing
        if getattr(judgment, 'elapsed_seconds', None) is not None:
            lines.append(f"  Elapsed: {judgment.elapsed_seconds:.3f}s")

        return "\n".join(lines)

    def _header(self, judgment: EquivalenceJudgment) -> str:
        """Render the header line."""
        return "╔══════════════════════════════════════════════════════════════╗\n" \
               "║                 Sheaf Equivalence Checker                    ║\n" \
               "╚══════════════════════════════════════════════════════════════╝"

    def _render_local_judgment(self, j: LocalEquivalenceJudgment) -> str:
        """Render a single local judgment."""
        symbol = self.VERDICT_SYMBOLS.get(j.verdict, "?")
        fwd = "✓" if j.forward_holds else "✗" if j.forward_holds is False else "?"
        bwd = "✓" if j.backward_holds else "✗" if j.backward_holds is False else "?"

        line = f"    {symbol} {j.site_id.name} [{j.site_id.kind.value}]"
        line += f"  fwd:{fwd}  bwd:{bwd}"

        if self._verbose and j.explanation:
            line += f"\n      {j.explanation}"

        return line

    def _render_obstruction(self, obs: EquivalenceObstruction) -> str:
        """Render a single obstruction."""
        sites_str = ", ".join(s.name for s in obs.sites)
        return f"    [{obs.severity}] {obs.kind.value} at {sites_str}: {obs.explanation}"


# ═══════════════════════════════════════════════════════════════════════════════
# JSON renderer
# ═══════════════════════════════════════════════════════════════════════════════


class EquivalenceJsonRenderer:
    """Render equivalence results as JSON."""

    def render(self, judgment: EquivalenceJudgment) -> str:
        """Render as a JSON string."""
        data = self.to_dict(judgment)
        return json.dumps(data, indent=2, default=str)

    def to_dict(self, judgment: EquivalenceJudgment) -> Dict[str, Any]:
        """Convert judgment to a JSON-serialisable dict."""
        return {
            "verdict": judgment.verdict.value,
            "strength": judgment.strength.value,
            "program_f": {
                "name": judgment.program_f.name,
                "source_file": judgment.program_f.source_path,
            },
            "program_g": {
                "name": judgment.program_g.name,
                "source_file": judgment.program_g.source_path,
            },
            "local_judgments": [
                self._local_judgment_to_dict(j)
                for j in judgment.local_judgments
            ],
            "obstructions": [
                self._obstruction_to_dict(o)
                for o in judgment.obstructions
            ],
            "cohomology": self._cohomology_to_dict(judgment.cohomology_class),
            "elapsed_seconds": judgment.elapsed_seconds,
        }

    def _local_judgment_to_dict(self, j: LocalEquivalenceJudgment) -> Dict[str, Any]:
        return {
            "site_id": {"kind": j.site_id.kind.value, "name": j.site_id.name},
            "verdict": j.verdict.value,
            "forward_holds": j.forward_holds,
            "backward_holds": j.backward_holds,
            "explanation": j.explanation,
            "has_counterexample": j.counterexample is not None,
        }

    def _obstruction_to_dict(self, o: EquivalenceObstruction) -> Dict[str, Any]:
        return {
            "kind": o.kind.value,
            "sites": [{"kind": s.kind.value, "name": s.name} for s in o.sites],
            "explanation": o.explanation,
            "severity": o.severity,
        }

    def _cohomology_to_dict(self, h: Any) -> Optional[Dict[str, Any]]:
        if h is None:
            return None
        return {
            "degree": h.degree,
            "is_trivial": h.is_trivial,
            "obstruction_count": h.obstruction_count,
        }


# ═══════════════════════════════════════════════════════════════════════════════
# SARIF renderer
# ═══════════════════════════════════════════════════════════════════════════════


class EquivalenceSarifRenderer:
    """Export equivalence results in SARIF 2.1.0 format."""

    def export(
        self,
        judgment: EquivalenceJudgment,
        output_path: str,
    ) -> str:
        """Export to SARIF and return the path."""
        sarif = self._build_sarif(judgment)
        with open(output_path, "w") as f:
            json.dump(sarif, f, indent=2, default=str)
        return output_path

    def render(self, judgment: EquivalenceJudgment) -> str:
        """Render as SARIF JSON string."""
        sarif = self._build_sarif(judgment)
        return json.dumps(sarif, indent=2, default=str)

    def _build_sarif(self, judgment: EquivalenceJudgment) -> Dict[str, Any]:
        """Build the SARIF document."""
        results: List[Dict[str, Any]] = []

        # Add obstructions as results
        for obs in judgment.obstructions:
            results.append(self._obstruction_to_result(obs, judgment))

        # Add the verdict as a note
        results.append({
            "ruleId": "equiv/verdict",
            "level": self._verdict_to_level(judgment.verdict),
            "message": {
                "text": f"Equivalence verdict: {judgment.verdict.value}",
            },
        })

        return {
            "$schema": "https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json",
            "version": "2.1.0",
            "runs": [
                {
                    "tool": {
                        "driver": {
                            "name": "deppy-equiv",
                            "version": "0.1.0",
                            "informationUri": "https://github.com/deppy/equivalence",
                            "rules": self._build_rules(),
                        },
                    },
                    "results": results,
                },
            ],
        }

    def _obstruction_to_result(
        self,
        obs: EquivalenceObstruction,
        judgment: EquivalenceJudgment,
    ) -> Dict[str, Any]:
        """Convert an obstruction to a SARIF result."""
        locations: List[Dict[str, Any]] = []
        for site_id in obs.sites:
            if site_id.source_location is not None:
                file_path, line, col = site_id.source_location
                locations.append({
                    "physicalLocation": {
                        "artifactLocation": {"uri": file_path},
                        "region": {
                            "startLine": line,
                            "startColumn": col,
                        },
                    },
                })

        return {
            "ruleId": f"equiv/{obs.kind.value}",
            "level": "error" if obs.severity == "error" else "warning",
            "message": {"text": obs.explanation},
            "locations": locations,
        }

    def _verdict_to_level(self, verdict: EquivalenceVerdict) -> str:
        return {
            EquivalenceVerdict.EQUIVALENT: "none",
            EquivalenceVerdict.INEQUIVALENT: "error",
            EquivalenceVerdict.REFINED: "warning",
            EquivalenceVerdict.UNKNOWN: "note",
        }.get(verdict, "note")

    def _build_rules(self) -> List[Dict[str, Any]]:
        """Build SARIF rule definitions."""
        rules = []
        for kind in EquivalenceObstructionKind:
            rules.append({
                "id": f"equiv/{kind.value}",
                "shortDescription": {"text": kind.value.replace("_", " ").title()},
                "helpUri": "https://github.com/deppy/equivalence",
            })
        rules.append({
            "id": "equiv/verdict",
            "shortDescription": {"text": "Equivalence verdict"},
        })
        return rules


# ═══════════════════════════════════════════════════════════════════════════════
# Summary renderer (for pipeline)
# ═══════════════════════════════════════════════════════════════════════════════


class EquivalenceSummaryRenderer:
    """Render a concise summary of an equivalence pipeline result."""

    def render(
        self,
        summary: ObstructionSummary,
        verdict: EquivalenceVerdict,
    ) -> str:
        """Render a short summary."""
        lines: List[str] = []

        symbol = EquivalenceTerminalRenderer.VERDICT_SYMBOLS.get(verdict, "?")
        lines.append(f"{symbol} {verdict.value}")

        if summary.total_obstructions > 0:
            lines.append(f"  {summary.total_obstructions} obstruction(s)")
            for cat, count in sorted(summary.by_category.items()):
                lines.append(f"    {cat}: {count}")

        if summary.top_repairs:
            lines.append("  Suggested repairs:")
            for repair in summary.top_repairs[:3]:
                lines.append(f"    • {repair.description}")

        if not summary.cohomology_trivial:
            lines.append("  ⚠ H¹ non-trivial: local equivalences cannot glue")

        return "\n".join(lines)
