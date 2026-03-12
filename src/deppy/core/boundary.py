"""Boundary extraction and BoundarySection construction.

Provides:
- InputBoundaryBuilder: extract input boundary from a Cover
- OutputBoundaryBuilder: extract output boundary from a Cover
- BoundarySectionFactory: create BoundarySection from LocalSections
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Set

from deppy.core._protocols import (
    BoundarySection,
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
)


class InputBoundaryBuilder:
    """Extract the input boundary from a Cover.

    The input boundary consists of sites through which information
    flows into the covered region — typically argument boundaries
    and external call results.
    """

    # Site kinds that are naturally input-facing
    INPUT_KINDS: Set[SiteKind] = {
        SiteKind.ARGUMENT_BOUNDARY,
        SiteKind.LOOP_HEADER_INVARIANT,
    }

    @staticmethod
    def extract(cover: Cover) -> Set[SiteId]:
        """Extract input boundary site ids from a cover.

        Uses the explicitly marked input_boundary if available,
        otherwise infers from site kinds.
        """
        if cover.input_boundary:
            return set(cover.input_boundary)

        result: Set[SiteId] = set()
        for sid, site in cover.sites.items():
            if sid.kind in InputBoundaryBuilder.INPUT_KINDS:
                result.add(sid)
        return result

    @staticmethod
    def build_section(
        cover: Cover, sections: Dict[SiteId, LocalSection]
    ) -> BoundarySection:
        """Build an input BoundarySection from the cover and sections."""
        input_ids = InputBoundaryBuilder.extract(cover)
        boundary_sections = {
            sid: sections[sid] for sid in input_ids if sid in sections
        }
        return BoundarySection(boundary_sites=boundary_sections, is_input=True)


class OutputBoundaryBuilder:
    """Extract the output boundary from a Cover.

    The output boundary consists of sites through which information
    flows out — typically return output boundaries and error sites.
    """

    OUTPUT_KINDS: Set[SiteKind] = {
        SiteKind.RETURN_OUTPUT_BOUNDARY,
        SiteKind.ERROR,
        SiteKind.MODULE_SUMMARY,
    }

    @staticmethod
    def extract(cover: Cover) -> Set[SiteId]:
        """Extract output boundary site ids from a cover.

        Uses the explicitly marked output_boundary if available,
        otherwise infers from site kinds.
        """
        if cover.output_boundary:
            return set(cover.output_boundary)

        result: Set[SiteId] = set()
        for sid, site in cover.sites.items():
            if sid.kind in OutputBoundaryBuilder.OUTPUT_KINDS:
                result.add(sid)
        return result

    @staticmethod
    def build_section(
        cover: Cover, sections: Dict[SiteId, LocalSection]
    ) -> BoundarySection:
        """Build an output BoundarySection from the cover and sections."""
        output_ids = OutputBoundaryBuilder.extract(cover)
        boundary_sections = {
            sid: sections[sid] for sid in output_ids if sid in sections
        }
        return BoundarySection(boundary_sites=boundary_sections, is_input=False)


class BoundarySectionFactory:
    """Create BoundarySection from a collection of LocalSections.

    Supports both explicit site-id sets and automatic inference from
    site kinds.
    """

    @staticmethod
    def create(
        sections: Dict[SiteId, LocalSection],
        boundary_ids: Optional[Set[SiteId]] = None,
        is_input: bool = True,
    ) -> BoundarySection:
        """Create a BoundarySection.

        Args:
            sections: All available local sections.
            boundary_ids: Explicit set of site ids for the boundary.
                         If None, includes all sections.
            is_input: Whether this is an input boundary.
        """
        if boundary_ids is not None:
            filtered = {
                sid: sec for sid, sec in sections.items() if sid in boundary_ids
            }
        else:
            filtered = dict(sections)
        return BoundarySection(boundary_sites=filtered, is_input=is_input)

    @staticmethod
    def from_cover(
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
        is_input: bool = True,
    ) -> BoundarySection:
        """Create a BoundarySection from a cover, using the cover's boundary annotations."""
        if is_input:
            return InputBoundaryBuilder.build_section(cover, sections)
        return OutputBoundaryBuilder.build_section(cover, sections)
