"""Render residual obstructions with explanations and resolution hints.

ResidualRenderer focuses on obstructions that remain after the frontier
search -- the "proof obligations" or "residual errors" that the user
must address.  It provides detailed explanations of *why* each residual
exists and *how* it might be resolved.
"""

from __future__ import annotations

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
# Residual display data
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ResidualDisplay:
    """Precomputed display data for a single residual.

    Attributes:
        obstruction: The underlying ObstructionData.
        explanation_text: Detailed explanation text.
        resolution_hints: List of hint strings.
        affected_sites: Sites involved in this residual.
        severity: 'critical', 'important', or 'minor'.
        index: 1-based index in the residual list.
    """

    _obstruction: ObstructionData
    _explanation_text: str
    _resolution_hints: List[str]
    _affected_sites: List[SiteId]
    _severity: str = "important"
    _index: int = 0

    @property
    def obstruction(self) -> ObstructionData:
        return self._obstruction

    @property
    def explanation_text(self) -> str:
        return self._explanation_text

    @property
    def resolution_hints(self) -> List[str]:
        return list(self._resolution_hints)

    @property
    def affected_sites(self) -> List[SiteId]:
        return list(self._affected_sites)

    @property
    def severity(self) -> str:
        return self._severity

    @property
    def index(self) -> int:
        return self._index


# ---------------------------------------------------------------------------
# Explanation generation
# ---------------------------------------------------------------------------

def _generate_explanation(
    obs: ObstructionData,
    sections: Optional[Dict[SiteId, LocalSection]] = None,
) -> str:
    """Generate a detailed explanation for a residual obstruction."""
    if sections is None:
        sections = {}

    lines: List[str] = []

    if obs.explanation:
        lines.append(obs.explanation)
    else:
        lines.append("A type conflict exists between overlapping sites.")

    if obs.conflicting_overlaps:
        lines.append("")
        lines.append("The conflict arises because:")

        for a_id, b_id in obs.conflicting_overlaps:
            sec_a = sections.get(a_id)
            sec_b = sections.get(b_id)

            a_desc = _describe_section(a_id, sec_a)
            b_desc = _describe_section(b_id, sec_b)

            lines.append(f"  - At {a_id.name}: {a_desc}")
            lines.append(f"    vs {b_id.name}: {b_desc}")

            if sec_a is not None and sec_b is not None:
                conflict_detail = _explain_conflict(sec_a, sec_b)
                if conflict_detail:
                    lines.append(f"    Specifically: {conflict_detail}")

    if obs.cohomology_class is not None:
        degree = obs.cohomology_class.degree
        lines.append("")
        lines.append(
            f"This is an H^{degree} obstruction class "
            f"in the sheaf cohomology."
        )
        if degree == 1:
            lines.append(
                "H^1 obstructions represent genuine type errors "
                "that cannot be resolved by adjusting the analysis parameters."
            )

    return "\n".join(lines)


def _describe_section(
    site_id: SiteId,
    section: Optional[LocalSection],
) -> str:
    """Describe a section at a site for display."""
    if section is None:
        return "(no section computed)"

    parts: List[str] = []

    carrier = section.carrier_type
    if carrier is not None:
        parts.append(f"type={repr(carrier)}")
    else:
        parts.append("type=unknown")

    parts.append(f"trust={section.trust.value}")

    if section.refinements:
        ref_keys = sorted(section.refinements.keys())[:3]
        refs_str = ", ".join(ref_keys)
        if len(section.refinements) > 3:
            refs_str += f" (+{len(section.refinements) - 3} more)"
        parts.append(f"refs=[{refs_str}]")

    return ", ".join(parts)


def _explain_conflict(
    sec_a: LocalSection,
    sec_b: LocalSection,
) -> str:
    """Explain why two sections conflict."""
    reasons: List[str] = []

    type_a = sec_a.carrier_type
    type_b = sec_b.carrier_type
    if type_a is not None and type_b is not None:
        if repr(type_a) != repr(type_b):
            reasons.append(
                f"carrier types differ: {repr(type_a)} vs {repr(type_b)}"
            )

    common_keys = set(sec_a.refinements.keys()) & set(sec_b.refinements.keys())
    for key in sorted(common_keys):
        va = sec_a.refinements[key]
        vb = sec_b.refinements[key]
        if va != vb:
            reasons.append(
                f"refinement '{key}' differs: {va!r} vs {vb!r}"
            )

    return "; ".join(reasons) if reasons else ""


# ---------------------------------------------------------------------------
# Resolution hint generation
# ---------------------------------------------------------------------------

def _generate_resolution_hints(
    obs: ObstructionData,
    sections: Optional[Dict[SiteId, LocalSection]] = None,
) -> List[str]:
    """Generate resolution hints for a residual obstruction."""
    if sections is None:
        sections = {}

    hints: List[str] = []
    explanation = obs.explanation.lower()

    # General hint based on classification
    if "guard" in explanation or "branch" in explanation:
        hints.append(
            "Add a type guard (isinstance check) to narrow the type "
            "on the relevant branch."
        )
    elif "none" in explanation or "optional" in explanation:
        hints.append(
            "Add a None check before using this value. "
            "Consider: 'if value is not None: ...'"
        )
    elif "bound" in explanation or "range" in explanation:
        hints.append(
            "Add bounds validation to ensure the value falls "
            "within the expected range."
        )
    elif "mismatch" in explanation or "incompatible" in explanation:
        hints.append(
            "Ensure types are consistent across all branches. "
            "Consider widening to a Union type or adding a type cast."
        )
    elif "shape" in explanation or "dimension" in explanation:
        hints.append(
            "Verify tensor shapes are compatible. "
            "Consider using reshape or assertion checks."
        )

    # Site-kind-specific hints
    site_kinds: Set[SiteKind] = set()
    for a_id, b_id in obs.conflicting_overlaps:
        site_kinds.add(a_id.kind)
        site_kinds.add(b_id.kind)

    if SiteKind.ARGUMENT_BOUNDARY in site_kinds:
        hints.append(
            "Add explicit type annotations to the function parameters."
        )
    if SiteKind.RETURN_OUTPUT_BOUNDARY in site_kinds:
        hints.append(
            "Ensure all return paths produce a consistent type."
        )
    if SiteKind.LOOP_HEADER_INVARIANT in site_kinds:
        hints.append(
            "Provide a loop invariant annotation to help the analyzer "
            "verify the loop body."
        )
    if SiteKind.PROOF in site_kinds:
        hints.append(
            "Provide a proof seed or theorem to discharge this "
            "verification condition."
        )

    # Trust-based hints
    for a_id, b_id in obs.conflicting_overlaps:
        sec = sections.get(a_id) or sections.get(b_id)
        if sec is not None and sec.trust == TrustLevel.RESIDUAL:
            hints.append(
                "This section has RESIDUAL trust. Add runtime checks "
                "or proofs to upgrade the trust level."
            )
            break

    if not hints:
        hints.append(
            "Review the conflicting type assignments and ensure "
            "they are consistent across the overlap region."
        )

    return hints


def _compute_severity(
    obs: ObstructionData,
    cover: Optional[Cover] = None,
) -> str:
    """Compute the severity of a residual obstruction."""
    if cover is not None:
        affected_sites: Set[SiteId] = set()
        for a_id, b_id in obs.conflicting_overlaps:
            affected_sites.add(a_id)
            affected_sites.add(b_id)

        if affected_sites & cover.output_boundary:
            return "critical"
        if affected_sites & cover.input_boundary:
            return "important"

    n_conflicts = len(obs.conflicting_overlaps)
    if n_conflicts >= 3:
        return "critical"
    if n_conflicts >= 1:
        return "important"
    return "minor"


# ---------------------------------------------------------------------------
# ResidualRenderer
# ---------------------------------------------------------------------------

class ResidualRenderer:
    """Render residual obstructions with explanations and hints.

    Produces human-readable output showing the remaining type errors,
    why they exist, and how they might be resolved.

    Usage::

        renderer = ResidualRenderer()
        output = renderer.render(residuals, sections=sections)
        print(output)
    """

    def __init__(
        self,
        *,
        show_hints: bool = True,
        show_cohomology: bool = True,
        max_hints_per_residual: int = 5,
        verbose: bool = False,
    ) -> None:
        self._show_hints = show_hints
        self._show_cohomology = show_cohomology
        self._max_hints = max_hints_per_residual
        self._verbose = verbose

    def render(
        self,
        residuals: List[ObstructionData],
        sections: Optional[Dict[SiteId, LocalSection]] = None,
        cover: Optional[Cover] = None,
    ) -> str:
        """Render all residual obstructions."""
        if not residuals:
            return "No residual obstructions. All type assignments are consistent."

        displays = self._prepare_displays(residuals, sections, cover)

        lines: List[str] = []
        lines.append(f"Residual Obstructions ({len(displays)} remaining):")
        lines.append("=" * 60)

        for disp in displays:
            lines.append("")
            lines.append(self._render_single(disp))

        lines.append("")
        lines.append(self._render_summary(displays))

        return "\n".join(lines)

    def render_explanation(
        self,
        residual: ObstructionData,
        sections: Optional[Dict[SiteId, LocalSection]] = None,
    ) -> str:
        """Render the explanation for a single residual."""
        return _generate_explanation(residual, sections)

    def render_resolution_hints(
        self,
        residual: ObstructionData,
        sections: Optional[Dict[SiteId, LocalSection]] = None,
    ) -> str:
        """Render the resolution hints for a single residual."""
        hints = _generate_resolution_hints(residual, sections)
        if not hints:
            return "No resolution hints available."

        lines: List[str] = ["Resolution hints:"]
        for i, hint in enumerate(hints[: self._max_hints], 1):
            lines.append(f"  {i}. {hint}")

        return "\n".join(lines)

    def _prepare_displays(
        self,
        residuals: List[ObstructionData],
        sections: Optional[Dict[SiteId, LocalSection]],
        cover: Optional[Cover],
    ) -> List[ResidualDisplay]:
        """Prepare display data for all residuals."""
        displays: List[ResidualDisplay] = []

        for i, obs in enumerate(residuals, 1):
            if obs.is_trivial:
                continue

            explanation = _generate_explanation(obs, sections)
            hints = _generate_resolution_hints(obs, sections)
            severity = _compute_severity(obs, cover)

            affected: List[SiteId] = []
            for a_id, b_id in obs.conflicting_overlaps:
                affected.append(a_id)
                affected.append(b_id)

            displays.append(ResidualDisplay(
                _obstruction=obs,
                _explanation_text=explanation,
                _resolution_hints=hints,
                _affected_sites=affected,
                _severity=severity,
                _index=i,
            ))

        displays.sort(
            key=lambda d: {"critical": 0, "important": 1, "minor": 2}.get(
                d.severity, 3
            )
        )

        return displays

    def _render_single(self, disp: ResidualDisplay) -> str:
        """Render a single residual display."""
        lines: List[str] = []

        severity_marker = {
            "critical": "***",
            "important": "**",
            "minor": "*",
        }.get(disp.severity, "*")

        lines.append(
            f"  {severity_marker} Residual #{disp.index} "
            f"[{disp.severity}]"
        )

        explanation_lines = disp.explanation_text.split("\n")
        for el in explanation_lines:
            lines.append(f"    {el}")

        if disp.affected_sites:
            sites_str = ", ".join(
                s.name for s in disp.affected_sites[:5]
            )
            if len(disp.affected_sites) > 5:
                sites_str += f" (+{len(disp.affected_sites) - 5} more)"
            lines.append(f"    Sites: {sites_str}")

        if self._show_hints and disp.resolution_hints:
            lines.append("    Hints:")
            for i, hint in enumerate(
                disp.resolution_hints[: self._max_hints], 1
            ):
                lines.append(f"      {i}. {hint}")

        return "\n".join(lines)

    def _render_summary(
        self,
        displays: List[ResidualDisplay],
    ) -> str:
        """Render a summary of all residuals."""
        total = len(displays)
        critical = sum(1 for d in displays if d.severity == "critical")
        important = sum(1 for d in displays if d.severity == "important")
        minor = sum(1 for d in displays if d.severity == "minor")

        parts: List[str] = [f"Summary: {total} residual(s)"]
        if critical:
            parts.append(f"{critical} critical")
        if important:
            parts.append(f"{important} important")
        if minor:
            parts.append(f"{minor} minor")

        return " | ".join(parts)
