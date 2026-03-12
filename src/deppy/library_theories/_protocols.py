"""Library theory protocols: theory packs as cover factories."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Protocol, Set, runtime_checkable

from deppy.core._protocols import (
    Cover, LocalSection, SiteId, SiteKind, TrustLevel,
)


@dataclass
class ViabilityPredicate:
    """Local viability predicate for an error-sensitive site.
    Describes when the site is safe (operation can proceed without error).
    """
    site_id: SiteId
    predicate: Any
    explanation_template: str = ""


@dataclass
class TransportDeclaration:
    """Declares how facts transport across site boundaries."""
    source_site: SiteId
    target_site: SiteId
    transport_map: Any = None


@runtime_checkable
class SiteConstructor(Protocol):
    """Creates sites for a theory pack."""
    def construct_sites(self, ast_node: Any, context: Any) -> List[Any]: ...
    def site_kinds(self) -> Set[SiteKind]: ...


@runtime_checkable
class LocalSolverAdapter(Protocol):
    """Pack-specific local solver for site families."""
    def solve_local(self, site_id: SiteId, section: LocalSection) -> LocalSection: ...
    def can_solve(self, site_id: SiteId) -> bool: ...


@runtime_checkable
class TheoryPack(Protocol):
    """A theory pack as a cover factory (not atom factory).

    Each pack exports: site constructors, viability predicates,
    forward summarizers, local solver adapters, transport declarations.
    """
    @property
    def name(self) -> str: ...

    def site_constructors(self) -> List[SiteConstructor]: ...
    def viability_predicates(self, cover: Cover) -> List[ViabilityPredicate]: ...
    def forward_summarize(self, section: LocalSection) -> LocalSection: ...
    def backward_pullback(self, viability: ViabilityPredicate) -> Any: ...
    def local_solver(self) -> LocalSolverAdapter: ...
    def transport_declarations(self) -> List[TransportDeclaration]: ...


@dataclass
class PackRegistry:
    """Registry of active theory packs."""
    packs: Dict[str, TheoryPack] = field(default_factory=dict)

    def register(self, pack: TheoryPack) -> None:
        self.packs[pack.name] = pack

    def get(self, name: str) -> Optional[TheoryPack]:
        return self.packs.get(name)

    def active_packs(self) -> List[TheoryPack]:
        return list(self.packs.values())
