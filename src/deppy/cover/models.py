from __future__ import annotations

from dataclasses import dataclass, field
from typing import Tuple

from deppy.core._protocols import SiteId


@dataclass(frozen=True)
class AffectedStalk:
    """A site-level locality record for incremental cover analysis."""

    site_id: SiteId
    distance: int
    source_lines: Tuple[int, ...] = ()
    matched_lines: Tuple[int, ...] = ()
    incoming: Tuple[SiteId, ...] = ()
    outgoing: Tuple[SiteId, ...] = ()
    overlaps: Tuple[SiteId, ...] = ()
    reasons: Tuple[str, ...] = ()

    @property
    def is_seed(self) -> bool:
        return bool(self.matched_lines)


@dataclass(frozen=True)
class AffectedStalkReport:
    """Deterministic summary of changed-line impact over a cover."""

    changed_lines: Tuple[int, ...] = ()
    seed_sites: Tuple[SiteId, ...] = ()
    stalks: Tuple[AffectedStalk, ...] = ()
    unmatched_lines: Tuple[int, ...] = ()
    warnings: Tuple[str, ...] = ()

    @property
    def affected_site_ids(self) -> Tuple[SiteId, ...]:
        return tuple(stalk.site_id for stalk in self.stalks)

    @property
    def requires_full_reanalysis(self) -> bool:
        return bool(self.changed_lines) and not bool(self.seed_sites)
