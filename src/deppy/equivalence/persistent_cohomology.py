"""Persistent Čech cohomology over cover refinement filtrations.

This module computes how H¹ obstructions appear and disappear as the
cover is refined from coarse (whole-function sites) to fine (SSA-level
sites).  The persistence of an obstruction across refinement levels
provides a principled confidence score:

    confidence(obstruction) = (death_level - birth_level) / n_levels

An obstruction that persists across all levels is robust (confidence 1.0);
one that appears only at the finest grain is likely an artifact (low
confidence).

Mathematical structure
---------------------
A *filtration* is a sequence of covers

    U₀ ⊂ U₁ ⊂ ⋯ ⊂ Uₖ

where each Uᵢ refines the previous one.  At each level i we compute
the Čech cohomology H¹(Uᵢ, F).  The refinement maps induce
homomorphisms on cohomology:

    H¹(U₀) ← H¹(U₁) ← ⋯ ← H¹(Uₖ)

(Note: refinement goes from coarse to fine, so the map direction is
reversed by the contravariance of Čech cohomology.)

An obstruction class α ∈ H¹(Uᵢ) is *born* at level i if its image
under the refinement map from level i−1 was zero.  It *dies* at
level j if its image first becomes zero at level j.

The *barcode* of each obstruction records [birth, death).

Usage
-----
    from deppy.equivalence.persistent_cohomology import (
        CoverFiltration, PersistentCohomologyComputer,
    )

    # Build a filtration of covers
    filtration = CoverFiltration()
    filtration.add_level("function", sites_coarse, overlaps_coarse, judgments_coarse)
    filtration.add_level("branch", sites_medium, overlaps_medium, judgments_medium)
    filtration.add_level("ssa", sites_fine, overlaps_fine, judgments_fine)

    # Compute persistence
    computer = PersistentCohomologyComputer(filtration)
    result = computer.compute()

    for bar in result.barcodes:
        print(f"Obstruction {bar.representative}: "
              f"born at {bar.birth_level}, dies at {bar.death_level}, "
              f"confidence={bar.confidence:.2f}")
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Optional,
    Set,
    Tuple,
)

from deppy.core._protocols import SiteId
from deppy.equivalence._protocols import LocalEquivalenceJudgment
from deppy.equivalence.cohomology import (
    CechCohomologyComputer,
    CechCohomologyResult,
    CochainElement,
    CohomologyGroup,
    _gf2_rank,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Filtration level
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class FiltrationLevel:
    """One level of a cover refinement filtration.

    Stores the cover data (sites, overlaps, judgments) and the
    computed cohomology at this level.
    """
    name: str
    index: int
    sites: List[SiteId]
    overlaps: List[Tuple[SiteId, SiteId]]
    judgments: Dict[SiteId, LocalEquivalenceJudgment]
    cohomology: Optional[CechCohomologyResult] = None
    h1_rank: int = 0
    obstruction_keys: Set[Tuple[SiteId, ...]] = field(default_factory=set)


# ═══════════════════════════════════════════════════════════════════════════════
# Barcode: birth–death interval for a persistent obstruction
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class PersistenceBarcode:
    """Birth–death interval for a persistent H¹ obstruction.

    The confidence score is:
        (death_level - birth_level) / n_levels

    A barcode that spans [0, n_levels) has confidence 1.0 (robust).
    A barcode that spans [k, k+1) has confidence 1/n_levels (ephemeral).
    """
    representative: str
    birth_level: int
    death_level: int  # exclusive: the first level where this obstruction vanishes
    birth_name: str
    death_name: str  # name of the level where it dies (or "∞" if persistent)
    n_levels: int
    obstruction_key: Tuple[SiteId, ...]

    @property
    def confidence(self) -> float:
        """Persistence-based confidence score in [0, 1]."""
        if self.n_levels <= 1:
            return 1.0
        return (self.death_level - self.birth_level) / self.n_levels

    @property
    def is_persistent(self) -> bool:
        """True if this obstruction survives to the finest level."""
        return self.death_level >= self.n_levels

    @property
    def lifespan(self) -> int:
        """Number of levels this obstruction spans."""
        return self.death_level - self.birth_level


# ═══════════════════════════════════════════════════════════════════════════════
# Cover filtration
# ═══════════════════════════════════════════════════════════════════════════════


class CoverFiltration:
    """A sequence of cover refinement levels.

    Levels are added from coarsest to finest.  Each level contains
    sites, overlaps, and local equivalence judgments.
    """

    def __init__(self) -> None:
        self._levels: List[FiltrationLevel] = []

    def add_level(
        self,
        name: str,
        sites: List[SiteId],
        overlaps: List[Tuple[SiteId, SiteId]],
        judgments: Dict[SiteId, LocalEquivalenceJudgment],
    ) -> None:
        """Add a refinement level (coarsest first)."""
        level = FiltrationLevel(
            name=name,
            index=len(self._levels),
            sites=sites,
            overlaps=overlaps,
            judgments=judgments,
        )
        self._levels.append(level)

    @property
    def levels(self) -> List[FiltrationLevel]:
        return list(self._levels)

    @property
    def n_levels(self) -> int:
        return len(self._levels)

    def add_level_from_cover(
        self,
        name: str,
        sites: List[SiteId],
        overlaps: List[Tuple[SiteId, SiteId]],
        judgments: Dict[SiteId, LocalEquivalenceJudgment],
        *,
        refinement_map: Optional[Dict[SiteId, SiteId]] = None,
    ) -> None:
        """Add a level with an explicit refinement map to the previous level.

        The refinement_map sends each fine site to its coarse counterpart.
        """
        self.add_level(name, sites, overlaps, judgments)
        # Store the refinement map on the level for later use
        if refinement_map is not None:
            self._levels[-1]._refinement_map = refinement_map  # type: ignore


# ═══════════════════════════════════════════════════════════════════════════════
# Persistent cohomology result
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class PersistentCohomologyResult:
    """Result of persistent H¹ computation across a cover filtration.

    The main output is the set of barcodes, each representing a
    persistent obstruction with a confidence score.
    """
    levels: List[FiltrationLevel]
    barcodes: List[PersistenceBarcode]
    h1_ranks: List[int]  # H¹ rank at each level

    @property
    def n_persistent(self) -> int:
        """Number of obstructions that persist to the finest level."""
        return sum(1 for b in self.barcodes if b.is_persistent)

    @property
    def max_confidence(self) -> float:
        """Confidence of the most persistent obstruction."""
        if not self.barcodes:
            return 0.0
        return max(b.confidence for b in self.barcodes)

    @property
    def stable_obstruction_count(self) -> int:
        """Number of obstructions with confidence > 0.5."""
        return sum(1 for b in self.barcodes if b.confidence > 0.5)

    def confidence_for_verdict(self) -> float:
        """Overall confidence that the obstruction is real.

        Returns:
            0.0 if no obstructions at any level
            max(barcode confidences) otherwise
        """
        return self.max_confidence


# ═══════════════════════════════════════════════════════════════════════════════
# Persistent cohomology computer
# ═══════════════════════════════════════════════════════════════════════════════


class PersistentCohomologyComputer:
    """Compute persistent H¹ across a cover refinement filtration.

    Algorithm:
    1. At each filtration level, compute Čech H¹.
    2. Track which obstruction keys appear/disappear across levels.
    3. Build barcodes for each obstruction tracking its birth/death.

    The tracking uses obstruction key similarity: an obstruction at
    level i "continues" to level i+1 if there exists an obstruction
    at level i+1 whose site set intersects.
    """

    def __init__(self, filtration: CoverFiltration) -> None:
        self._filtration = filtration

    def compute(self) -> PersistentCohomologyResult:
        """Run persistent cohomology computation."""
        levels = self._filtration.levels
        n = len(levels)

        if n == 0:
            return PersistentCohomologyResult(
                levels=[], barcodes=[], h1_ranks=[],
            )

        # Step 1: Compute cohomology at each level
        for level in levels:
            cohom = CechCohomologyComputer(
                judgments=level.judgments,
                overlaps=level.overlaps,
            )
            level.cohomology = cohom.compute()
            level.h1_rank = level.cohomology.h1.rank
            level.obstruction_keys = set(
                level.cohomology.h1.quotient.keys()
            )
            # When GF(2) rank detects obstructions but quotient is empty
            # (the naive key-equality quotient missed them), create synthetic
            # obstruction keys from the overlap structure.
            if level.h1_rank > len(level.obstruction_keys):
                for i in range(level.h1_rank - len(level.obstruction_keys)):
                    # Use overlaps as proxy keys for the unrepresented cycles
                    if i < len(level.overlaps):
                        a, b = level.overlaps[i]
                        level.obstruction_keys.add((a, b))
                    else:
                        # Fallback: use site list
                        if level.sites:
                            level.obstruction_keys.add(
                                tuple(level.sites[:min(2, len(level.sites))])
                            )

        h1_ranks = [lev.h1_rank for lev in levels]

        # Step 2: Track obstruction persistence across levels
        # Each obstruction at each level gets a representative string
        # and we track whether it "matches" an obstruction at the next level
        # via site-set intersection.

        # Active barcodes: list of (birth_level, birth_name, representative, key_set)
        active: List[Tuple[int, str, str, Set[SiteId]]] = []
        finished: List[PersistenceBarcode] = []

        for level in levels:
            new_keys = level.obstruction_keys
            # Build site sets for current level's obstructions
            current_obstructions: List[Tuple[Tuple[SiteId, ...], Set[SiteId]]] = []
            for key in new_keys:
                sites = set(key)
                current_obstructions.append((key, sites))

            # Match active barcodes to current obstructions
            matched_active: Set[int] = set()
            matched_current: Set[int] = set()

            for a_idx, (birth, bname, rep, a_sites) in enumerate(active):
                best_overlap = -1
                best_c_idx = -1
                for c_idx, (c_key, c_sites) in enumerate(current_obstructions):
                    if c_idx in matched_current:
                        continue
                    overlap = len(a_sites & c_sites)
                    if overlap > best_overlap:
                        best_overlap = overlap
                        best_c_idx = c_idx

                if best_c_idx >= 0 and best_overlap > 0:
                    # Continue the barcode: update site set
                    matched_active.add(a_idx)
                    matched_current.add(best_c_idx)
                    c_key, c_sites = current_obstructions[best_c_idx]
                    active[a_idx] = (birth, bname, rep, c_sites)

            # Close unmatched active barcodes
            new_active = []
            for a_idx, (birth, bname, rep, a_sites) in enumerate(active):
                if a_idx not in matched_active:
                    finished.append(PersistenceBarcode(
                        representative=rep,
                        birth_level=birth,
                        death_level=level.index,
                        birth_name=bname,
                        death_name=level.name,
                        n_levels=n,
                        obstruction_key=tuple(a_sites),
                    ))
                else:
                    new_active.append((birth, bname, rep, a_sites))

            # Open new barcodes for unmatched current obstructions
            for c_idx, (c_key, c_sites) in enumerate(current_obstructions):
                if c_idx not in matched_current:
                    rep_str = " ∩ ".join(
                        s.name for s in sorted(c_key, key=lambda s: s.name)
                    ) if c_key else f"obs@{level.name}"
                    new_active.append((
                        level.index, level.name, rep_str, c_sites,
                    ))

            active = new_active

        # Close remaining active barcodes (persistent to the end)
        for birth, bname, rep, a_sites in active:
            finished.append(PersistenceBarcode(
                representative=rep,
                birth_level=birth,
                death_level=n,  # past the last level = persistent
                birth_name=bname,
                death_name="∞",
                n_levels=n,
                obstruction_key=tuple(a_sites),
            ))

        # Sort by confidence (descending)
        finished.sort(key=lambda b: -b.confidence)

        return PersistentCohomologyResult(
            levels=levels,
            barcodes=finished,
            h1_ranks=h1_ranks,
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Convenience: auto-filtration from a single set of judgments
# ═══════════════════════════════════════════════════════════════════════════════


def auto_filtration_from_judgments(
    judgments: Dict[SiteId, LocalEquivalenceJudgment],
    overlaps: List[Tuple[SiteId, SiteId]],
) -> CoverFiltration:
    """Build a 3-level filtration from a flat set of judgments.

    Level 0 (coarse): group sites by SiteKind
    Level 1 (medium): original sites, original overlaps
    Level 2 (fine):   original sites, all-pairs overlaps

    This is useful when you have a single analysis result and want
    to compute persistence without manually constructing a filtration.
    """
    from deppy.core._protocols import SiteKind

    filtration = CoverFiltration()
    all_sites = list(judgments.keys())

    if not all_sites:
        return filtration

    # Level 0: coarse — one site per SiteKind
    kind_groups: Dict[SiteKind, List[SiteId]] = {}
    for s in all_sites:
        kind_groups.setdefault(s.kind, []).append(s)

    coarse_sites = [group[0] for group in kind_groups.values()]
    coarse_overlaps = [
        (a, b)
        for i, a in enumerate(coarse_sites)
        for b in coarse_sites[i + 1:]
    ]
    coarse_judgments = {s: judgments[s] for s in coarse_sites if s in judgments}

    filtration.add_level("coarse", coarse_sites, coarse_overlaps, coarse_judgments)

    # Level 1: medium — all original sites and overlaps
    filtration.add_level("medium", all_sites, overlaps, judgments)

    # Level 2: fine — all-pairs overlaps (maximum connectivity)
    fine_overlaps = [
        (a, b)
        for i, a in enumerate(all_sites)
        for b in all_sites[i + 1:]
    ]
    filtration.add_level("fine", all_sites, fine_overlaps, judgments)

    return filtration
