"""Interprocedural protocols: Kan extensions, profunctors, section transport."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Protocol, runtime_checkable

from deppy.core._protocols import (
    BoundarySection, Cover, GlobalSection, LocalSection, SiteId,
)


@dataclass
class CallSiteSummary:
    """Callee boundary + selected interior sections + provenance."""
    callee_name: str
    boundary_section: BoundarySection
    interior_sections: Dict[SiteId, LocalSection] = field(default_factory=dict)
    provenance: Optional[str] = None


@dataclass
class KanExtensionResult:
    """Result of a Kan extension computation.
    Left Kan: Lan_i T_f(s) = colim_{(i down s)} T_f  (forward).
    Right Kan: Ran_i T_g(s) = lim_{(s down i)} T_g   (backward).
    """
    site_id: SiteId
    section: LocalSection
    is_left: bool = True  # Left Kan (forward) or Right Kan (backward)


@runtime_checkable
class SectionTransport(Protocol):
    """Transport sections across call boundaries."""
    def import_at_call(
        self, callee_summary: CallSiteSummary, call_site: SiteId,
        actual_to_formal: Dict[str, str],
    ) -> Dict[SiteId, LocalSection]: ...

    def pullback_errors(
        self, callee_summary: CallSiteSummary, caller_cover: Cover,
    ) -> List[Any]: ...


@runtime_checkable
class Profunctor(Protocol):
    """Profunctor P: A^op x B -> Lat for module interfaces."""
    def apply(self, source: SiteId, target: SiteId) -> Any: ...
    def compose(self, other: "Profunctor") -> "Profunctor": ...
