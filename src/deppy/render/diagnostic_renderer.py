"""Render error diagnostics with provenance chains.

DiagnosticRenderer produces human-readable error messages that trace
the chain of local sections leading to the error.  It supports terminal
colors for interactive use and plain text for CI pipelines.
"""

from __future__ import annotations

import os
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.core._protocols import (
    Cover,
    LocalSection,
    ObstructionData,
    SiteId,
    SiteKind,
    TrustLevel,
)


# ---------------------------------------------------------------------------
# Terminal colors
# ---------------------------------------------------------------------------

class _Colors:
    """ANSI terminal color codes."""

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

    BOLD_RED = "\033[1;31m"
    BOLD_GREEN = "\033[1;32m"
    BOLD_YELLOW = "\033[1;33m"
    BOLD_BLUE = "\033[1;34m"
    BOLD_CYAN = "\033[1;36m"


class _NoColors:
    """No-op color codes for plain text output."""

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
    BG_RED = ""
    BOLD_RED = ""
    BOLD_GREEN = ""
    BOLD_YELLOW = ""
    BOLD_BLUE = ""
    BOLD_CYAN = ""


def _detect_color_support() -> bool:
    """Detect whether the terminal supports colors."""
    if os.environ.get("NO_COLOR"):
        return False
    if os.environ.get("FORCE_COLOR"):
        return True
    term = os.environ.get("TERM", "")
    if "color" in term or "xterm" in term or "256" in term:
        return True
    try:
        return os.isatty(1)
    except Exception:
        return False


# ---------------------------------------------------------------------------
# Diagnostic data types
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class DiagnosticSeverity:
    """Severity levels for diagnostics."""

    ERROR: str = "error"
    WARNING: str = "warning"
    INFO: str = "info"
    HINT: str = "hint"


@dataclass
class Diagnostic:
    """A rendered diagnostic message.

    Attributes:
        severity: error, warning, info, or hint.
        message: The main diagnostic message.
        location: Optional file:line:col location string.
        obstruction: The underlying ObstructionData, if any.
        provenance_chain: Chain of sites that led to this error.
        related: Related diagnostics (notes, hints).
        code: A diagnostic code (e.g. 'E001').
    """

    severity: str = "error"
    message: str = ""
    location: str = ""
    obstruction: Optional[ObstructionData] = None
    provenance_chain: List[Tuple[SiteId, str]] = field(default_factory=list)
    related: List[Diagnostic] = field(default_factory=list)
    code: str = ""


def _site_id_to_location(site_id: SiteId) -> str:
    """Convert a SiteId to a location string."""
    if site_id.source_location is not None:
        loc = site_id.source_location
        return f"{loc[0]}:{loc[1]}:{loc[2]}"
    return str(site_id)


def _severity_color(severity: str, c: Any) -> str:
    """Get the color code for a severity level."""
    if severity == "error":
        return c.BOLD_RED
    elif severity == "warning":
        return c.BOLD_YELLOW
    elif severity == "info":
        return c.BOLD_BLUE
    elif severity == "hint":
        return c.BOLD_GREEN
    return c.WHITE


def _trust_to_str(trust: TrustLevel) -> str:
    """Convert trust level to a display string."""
    return trust.value.replace("_", " ")


# ---------------------------------------------------------------------------
# DiagnosticRenderer
# ---------------------------------------------------------------------------

class DiagnosticRenderer:
    """Render error diagnostics with provenance tracing.

    Produces human-readable error messages showing the chain of sections
    that led to a type error, with optional terminal colors.

    Usage::

        renderer = DiagnosticRenderer(use_color=True)
        for diag in diagnostics:
            print(renderer.render(diag))
    """

    def __init__(
        self,
        *,
        use_color: Optional[bool] = None,
        show_provenance: bool = True,
        show_trust: bool = True,
        max_chain_length: int = 10,
        context_lines: int = 2,
    ) -> None:
        if use_color is None:
            use_color = _detect_color_support()
        self._colors = _Colors() if use_color else _NoColors()
        self._show_provenance = show_provenance
        self._show_trust = show_trust
        self._max_chain_length = max_chain_length
        self._context_lines = context_lines

    def render(self, diagnostic: Diagnostic) -> str:
        """Render a complete diagnostic message."""
        c = self._colors
        lines: List[str] = []

        sev_color = _severity_color(diagnostic.severity, c)
        code_str = f"[{diagnostic.code}] " if diagnostic.code else ""

        header = (
            f"{sev_color}{diagnostic.severity}{c.RESET}: "
            f"{c.BOLD}{code_str}{diagnostic.message}{c.RESET}"
        )
        lines.append(header)

        if diagnostic.location:
            lines.append(
                f"  {c.CYAN}-->{c.RESET} {diagnostic.location}"
            )

        if self._show_provenance and diagnostic.provenance_chain:
            lines.append("")
            prov_lines = self.render_provenance_chain(
                diagnostic.provenance_chain
            )
            lines.append(prov_lines)

        if diagnostic.obstruction is not None:
            obs_lines = self._render_obstruction_detail(
                diagnostic.obstruction
            )
            lines.append("")
            lines.extend(obs_lines)

        for related in diagnostic.related:
            lines.append("")
            related_text = self._render_related(related)
            lines.append(related_text)

        return "\n".join(lines)

    def render_provenance_chain(
        self,
        chain: List[Tuple[SiteId, str]],
    ) -> str:
        """Render a provenance chain showing how an error was derived.

        Each entry in the chain is (site_id, description).
        """
        c = self._colors
        lines: List[str] = []

        display_chain = chain
        truncated = False
        if len(chain) > self._max_chain_length:
            display_chain = (
                chain[: self._max_chain_length // 2]
                + chain[-(self._max_chain_length // 2) :]
            )
            truncated = True

        lines.append(f"  {c.BOLD}Provenance chain:{c.RESET}")

        for i, (site_id, description) in enumerate(display_chain):
            loc_str = _site_id_to_location(site_id)
            kind_str = site_id.kind.value

            if i == 0:
                prefix = f"  {c.GREEN}origin{c.RESET}"
            elif i == len(display_chain) - 1:
                prefix = f"  {c.RED}error{c.RESET} "
            else:
                prefix = f"  {c.DIM}step {i}{c.RESET}"

            connector = "|" if i < len(display_chain) - 1 else "'"

            lines.append(
                f"  {connector}-- {prefix} at "
                f"{c.CYAN}{loc_str}{c.RESET} "
                f"({c.DIM}{kind_str}{c.RESET})"
            )
            if description:
                lines.append(f"  |   {c.DIM}{description}{c.RESET}")

            if truncated and i == self._max_chain_length // 2 - 1:
                skipped = len(chain) - self._max_chain_length
                lines.append(
                    f"  |   {c.DIM}... ({skipped} steps omitted){c.RESET}"
                )

        return "\n".join(lines)

    def render_error_location(
        self,
        location: str,
        message: str = "",
    ) -> str:
        """Render an error at a specific source location."""
        c = self._colors

        parts = location.split(":")
        if len(parts) >= 3:
            file_part = parts[0]
            line_part = parts[1]
            col_part = parts[2]
            loc_str = (
                f"{c.BOLD}{file_part}{c.RESET}"
                f":{c.BOLD_YELLOW}{line_part}{c.RESET}"
                f":{col_part}"
            )
        else:
            loc_str = location

        lines: List[str] = []
        lines.append(f"  {c.CYAN}-->{c.RESET} {loc_str}")
        if message:
            lines.append(f"       {c.RED}{message}{c.RESET}")

        return "\n".join(lines)

    def _render_obstruction_detail(
        self,
        obs: ObstructionData,
    ) -> List[str]:
        """Render detailed obstruction information."""
        c = self._colors
        lines: List[str] = []

        if obs.explanation:
            lines.append(
                f"  {c.BOLD}Explanation:{c.RESET} {obs.explanation}"
            )

        if obs.conflicting_overlaps:
            lines.append(f"  {c.BOLD}Conflicting sites:{c.RESET}")
            for a_id, b_id in obs.conflicting_overlaps:
                a_loc = _site_id_to_location(a_id)
                b_loc = _site_id_to_location(b_id)
                lines.append(
                    f"    {c.RED}conflict{c.RESET}: "
                    f"{c.CYAN}{a_loc}{c.RESET} vs "
                    f"{c.CYAN}{b_loc}{c.RESET}"
                )

        if obs.cohomology_class is not None:
            degree = obs.cohomology_class.degree
            is_trivial = obs.cohomology_class.is_trivial
            lines.append(
                f"  {c.DIM}H^{degree} class: "
                f"{'trivial' if is_trivial else 'non-trivial'}{c.RESET}"
            )

        return lines

    def _render_related(self, diagnostic: Diagnostic) -> str:
        """Render a related diagnostic (note, hint)."""
        c = self._colors
        sev_color = _severity_color(diagnostic.severity, c)

        lines: List[str] = []
        lines.append(
            f"  {sev_color}{diagnostic.severity}{c.RESET}: "
            f"{diagnostic.message}"
        )
        if diagnostic.location:
            lines.append(
                f"    {c.CYAN}-->{c.RESET} {diagnostic.location}"
            )
        return "\n".join(lines)

    def render_summary(
        self,
        diagnostics: List[Diagnostic],
    ) -> str:
        """Render a summary of all diagnostics."""
        c = self._colors

        errors = sum(1 for d in diagnostics if d.severity == "error")
        warnings = sum(1 for d in diagnostics if d.severity == "warning")
        infos = sum(1 for d in diagnostics if d.severity == "info")
        hints = sum(1 for d in diagnostics if d.severity == "hint")

        parts: List[str] = []
        if errors:
            parts.append(f"{c.BOLD_RED}{errors} error(s){c.RESET}")
        if warnings:
            parts.append(f"{c.BOLD_YELLOW}{warnings} warning(s){c.RESET}")
        if infos:
            parts.append(f"{c.BOLD_BLUE}{infos} info(s){c.RESET}")
        if hints:
            parts.append(f"{c.BOLD_GREEN}{hints} hint(s){c.RESET}")

        if not parts:
            return f"{c.BOLD_GREEN}No diagnostics.{c.RESET}"

        return f"Found {', '.join(parts)}."

    def from_obstruction(
        self,
        obs: ObstructionData,
        cover: Optional[Cover] = None,
        sections: Optional[Dict[SiteId, LocalSection]] = None,
    ) -> Diagnostic:
        """Create a Diagnostic from an ObstructionData."""
        if sections is None:
            sections = {}

        location = ""
        provenance_chain: List[Tuple[SiteId, str]] = []

        if obs.conflicting_overlaps:
            first_a, first_b = obs.conflicting_overlaps[0]
            location = _site_id_to_location(first_a)

            for a_id, b_id in obs.conflicting_overlaps:
                sec_a = sections.get(a_id)
                desc_a = ""
                if sec_a is not None:
                    desc_a = (
                        f"type={sec_a.carrier_type}, "
                        f"trust={_trust_to_str(sec_a.trust)}"
                    )
                provenance_chain.append((a_id, desc_a))

                sec_b = sections.get(b_id)
                desc_b = ""
                if sec_b is not None:
                    desc_b = (
                        f"type={sec_b.carrier_type}, "
                        f"trust={_trust_to_str(sec_b.trust)}"
                    )
                provenance_chain.append((b_id, desc_b))

        return Diagnostic(
            severity="error",
            message=obs.explanation or "Type conflict detected",
            location=location,
            obstruction=obs,
            provenance_chain=provenance_chain,
        )

    def render_all(
        self,
        diagnostics: List[Diagnostic],
    ) -> str:
        """Render all diagnostics with a summary."""
        parts: List[str] = []
        for diag in diagnostics:
            parts.append(self.render(diag))
        parts.append("")
        parts.append(self.render_summary(diagnostics))
        return "\n\n".join(parts)
