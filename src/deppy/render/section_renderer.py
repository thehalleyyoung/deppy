"""Render local-site sections for debugging.

SectionRenderer provides formatted views of sections, sites, and
refinement details for use during development and debugging of the
sheaf-descent analysis pipeline.
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
    BoundarySection,
    Cover,
    GlobalSection,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.types.base import (
    AnyType,
    NeverType,
    TypeBase,
)
from deppy.types.refinement import (
    Predicate,
    QualifiedType,
    RefinementType,
)


# ---------------------------------------------------------------------------
# Formatting utilities
# ---------------------------------------------------------------------------

def _truncate(s: str, max_len: int = 60) -> str:
    """Truncate a string with ellipsis if too long."""
    if len(s) <= max_len:
        return s
    return s[: max_len - 3] + "..."


def _type_str(t: Any) -> str:
    """Format a type for display."""
    if t is None:
        return "None"
    if isinstance(t, TypeBase):
        return repr(t)
    return str(t)


def _trust_str(trust: TrustLevel) -> str:
    """Format a trust level for display."""
    return trust.value


def _kind_str(kind: SiteKind) -> str:
    """Format a site kind for display."""
    return kind.value


def _pad(s: str, width: int) -> str:
    """Pad a string to a given width."""
    if len(s) >= width:
        return s[:width]
    return s + " " * (width - len(s))


def _center(s: str, width: int) -> str:
    """Center a string in a field of given width."""
    if len(s) >= width:
        return s[:width]
    left = (width - len(s)) // 2
    right = width - len(s) - left
    return " " * left + s + " " * right


# ---------------------------------------------------------------------------
# SectionRenderer
# ---------------------------------------------------------------------------

class SectionRenderer:
    """Render local sections for debugging and inspection.

    Provides table, detail, and tree views of sections and covers.

    Usage::

        renderer = SectionRenderer()
        print(renderer.render(section))
        print(renderer.render_site_table(sections))
    """

    def __init__(
        self,
        *,
        max_refinement_width: int = 40,
        max_type_width: int = 30,
        show_provenance: bool = True,
        show_witnesses: bool = False,
    ) -> None:
        self._max_ref_width = max_refinement_width
        self._max_type_width = max_type_width
        self._show_provenance = show_provenance
        self._show_witnesses = show_witnesses

    def render(self, section: LocalSection) -> str:
        """Render a single section in detail."""
        lines: List[str] = []
        sid = section.site_id

        lines.append(f"Section: {sid}")
        lines.append(f"  Kind:    {_kind_str(sid.kind)}")
        lines.append(f"  Type:    {_type_str(section.carrier_type)}")
        lines.append(f"  Trust:   {_trust_str(section.trust)}")

        if sid.source_location is not None:
            loc = sid.source_location
            lines.append(f"  Source:  {loc[0]}:{loc[1]}:{loc[2]}")

        if self._show_provenance and section.provenance:
            lines.append(f"  Provenance: {section.provenance}")

        if section.refinements:
            lines.append("  Refinements:")
            for key, value in sorted(section.refinements.items()):
                val_str = _truncate(repr(value), self._max_ref_width)
                lines.append(f"    {key}: {val_str}")

        if self._show_witnesses and section.witnesses:
            lines.append("  Witnesses:")
            for key, value in sorted(section.witnesses.items()):
                val_str = _truncate(repr(value), self._max_ref_width)
                lines.append(f"    {key}: {val_str}")

        return "\n".join(lines)

    def render_site_table(
        self,
        sections: Dict[SiteId, LocalSection],
    ) -> str:
        """Render all sections as a formatted table.

        Columns: Site | Kind | Type | Trust | Refinements
        """
        if not sections:
            return "(no sections)"

        col_widths = {
            "site": 25,
            "kind": 22,
            "type": self._max_type_width,
            "trust": 14,
            "refs": self._max_ref_width,
        }

        header = (
            f"{_pad('Site', col_widths['site'])} | "
            f"{_pad('Kind', col_widths['kind'])} | "
            f"{_pad('Type', col_widths['type'])} | "
            f"{_pad('Trust', col_widths['trust'])} | "
            f"Refinements"
        )

        total_width = sum(col_widths.values()) + 12
        separator = "-" * total_width

        lines: List[str] = []
        lines.append(separator)
        lines.append(header)
        lines.append(separator)

        sorted_sections = sorted(
            sections.items(), key=lambda x: str(x[0])
        )

        for sid, sec in sorted_sections:
            site_str = _truncate(sid.name, col_widths["site"])
            kind_str = _truncate(_kind_str(sid.kind), col_widths["kind"])
            type_str = _truncate(
                _type_str(sec.carrier_type), col_widths["type"]
            )
            trust_str = _truncate(
                _trust_str(sec.trust), col_widths["trust"]
            )
            refs_str = _format_refs_short(sec.refinements, self._max_ref_width)

            row = (
                f"{_pad(site_str, col_widths['site'])} | "
                f"{_pad(kind_str, col_widths['kind'])} | "
                f"{_pad(type_str, col_widths['type'])} | "
                f"{_pad(trust_str, col_widths['trust'])} | "
                f"{refs_str}"
            )
            lines.append(row)

        lines.append(separator)
        lines.append(f"Total: {len(sections)} sections")

        return "\n".join(lines)

    def render_refinement_detail(
        self,
        refinements: Dict[str, Any],
    ) -> str:
        """Render refinement details in a verbose format."""
        if not refinements:
            return "(no refinements)"

        lines: List[str] = []
        lines.append(f"Refinements ({len(refinements)} entries):")

        for key, value in sorted(refinements.items()):
            lines.append(f"  {key}:")

            if isinstance(value, Predicate):
                lines.append(f"    type:  Predicate")
                lines.append(f"    value: {repr(value)}")
                fv = value.free_vars()
                if fv:
                    lines.append(f"    free_vars: {', '.join(sorted(fv))}")
            elif isinstance(value, bool):
                lines.append(f"    type:  bool")
                lines.append(f"    value: {value}")
            elif isinstance(value, (int, float)):
                lines.append(f"    type:  {type(value).__name__}")
                lines.append(f"    value: {value}")
            elif isinstance(value, str):
                lines.append(f"    type:  str")
                lines.append(f"    value: {value!r}")
            elif isinstance(value, (list, tuple)):
                lines.append(f"    type:  {type(value).__name__}")
                lines.append(f"    value: {_truncate(repr(value), 60)}")
                lines.append(f"    length: {len(value)}")
            elif isinstance(value, dict):
                lines.append(f"    type:  dict")
                lines.append(f"    keys:  {list(value.keys())}")
            else:
                lines.append(f"    type:  {type(value).__name__}")
                lines.append(f"    value: {_truncate(repr(value), 60)}")

        return "\n".join(lines)

    def render_cover(
        self,
        cover: Cover,
        sections: Optional[Dict[SiteId, LocalSection]] = None,
    ) -> str:
        """Render a cover with its topology and optional sections."""
        lines: List[str] = []
        lines.append("Cover:")
        lines.append(f"  Sites:     {len(cover.sites)}")
        lines.append(f"  Morphisms: {len(cover.morphisms)}")
        lines.append(f"  Overlaps:  {len(cover.overlaps)}")
        lines.append(f"  Input boundary:  {len(cover.input_boundary)} sites")
        lines.append(f"  Output boundary: {len(cover.output_boundary)} sites")
        lines.append(f"  Error sites:     {len(cover.error_sites)}")

        if cover.input_boundary:
            lines.append("\n  Input boundary sites:")
            for sid in sorted(cover.input_boundary, key=str):
                lines.append(f"    - {sid}")

        if cover.output_boundary:
            lines.append("\n  Output boundary sites:")
            for sid in sorted(cover.output_boundary, key=str):
                lines.append(f"    - {sid}")

        if cover.morphisms:
            lines.append("\n  Morphisms:")
            for m in cover.morphisms:
                lines.append(f"    {m.source} -> {m.target}")

        if cover.overlaps:
            lines.append("\n  Overlaps:")
            for a, b in cover.overlaps:
                lines.append(f"    {a} <-> {b}")

        if sections:
            lines.append("\n  Sections:")
            lines.append(self.render_site_table(sections))

        return "\n".join(lines)

    def render_global_section(
        self,
        gs: GlobalSection,
    ) -> str:
        """Render a global section with its boundaries."""
        lines: List[str] = []
        lines.append("Global Section:")
        lines.append(
            f"  Local sections: {len(gs.local_sections)}"
        )

        if gs.input_section is not None:
            lines.append(
                f"  Input boundary:  "
                f"{len(gs.input_section.boundary_sites)} sites"
            )
        if gs.output_section is not None:
            lines.append(
                f"  Output boundary: "
                f"{len(gs.output_section.boundary_sites)} sites"
            )

        lines.append("\n  All sections:")
        lines.append(self.render_site_table(gs.local_sections))

        return "\n".join(lines)

    def render_boundary(
        self,
        boundary: BoundarySection,
    ) -> str:
        """Render a boundary section."""
        kind = "Input" if boundary.is_input else "Output"
        lines: List[str] = []
        lines.append(f"{kind} Boundary ({len(boundary.boundary_sites)} sites):")

        for sid, sec in sorted(
            boundary.boundary_sites.items(), key=lambda x: str(x[0])
        ):
            type_str = _type_str(sec.carrier_type)
            trust_str = _trust_str(sec.trust)
            lines.append(
                f"  {sid.name}: {type_str} [{trust_str}]"
            )
            if sec.refinements:
                refs_str = _format_refs_short(sec.refinements, 50)
                lines.append(f"    refs: {refs_str}")

        return "\n".join(lines)

    def render_comparison(
        self,
        sec_a: LocalSection,
        sec_b: LocalSection,
    ) -> str:
        """Render a side-by-side comparison of two sections."""
        lines: List[str] = []
        lines.append("Section Comparison:")
        lines.append(f"  Left:  {sec_a.site_id}")
        lines.append(f"  Right: {sec_b.site_id}")
        lines.append("")

        fields = [
            ("Type", _type_str(sec_a.carrier_type), _type_str(sec_b.carrier_type)),
            ("Trust", _trust_str(sec_a.trust), _trust_str(sec_b.trust)),
            ("Provenance", sec_a.provenance or "-", sec_b.provenance or "-"),
        ]

        for label, va, vb in fields:
            match = "=" if va == vb else "!"
            lines.append(f"  {label:12s}: {va:30s} {match} {vb}")

        all_keys = sorted(
            set(sec_a.refinements.keys()) | set(sec_b.refinements.keys())
        )
        if all_keys:
            lines.append("  Refinements:")
            for key in all_keys:
                va = repr(sec_a.refinements.get(key, "-"))
                vb = repr(sec_b.refinements.get(key, "-"))
                match = "=" if va == vb else "!"
                lines.append(f"    {key:20s}: {va:20s} {match} {vb}")

        return "\n".join(lines)


def _format_refs_short(
    refinements: Dict[str, Any],
    max_width: int,
) -> str:
    """Format refinements as a short inline string."""
    if not refinements:
        return "-"
    parts: List[str] = []
    for key, value in sorted(refinements.items()):
        if key.startswith("_"):
            continue
        if isinstance(value, bool):
            parts.append(key if value else f"!{key}")
        else:
            parts.append(f"{key}={_truncate(repr(value), 15)}")
    result = ", ".join(parts)
    return _truncate(result, max_width)
