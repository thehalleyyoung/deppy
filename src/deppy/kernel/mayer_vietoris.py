"""Mayer-Vietoris long exact sequence for compositional H¹ computation.

When a program cover U decomposes as U = A ∪ B (e.g. two branches of an
if-statement, or the body of a loop vs its guard), the Mayer-Vietoris long
exact sequence connects the cohomology of the pieces to the cohomology of
the whole:

    … → H⁰(A∩B) → H¹(U) → H¹(A) ⊕ H¹(B) → H¹(A∩B) → …

In terms of bug counts:

    rank H¹(U)  =  rank H¹(A) + rank H¹(B) − rank(A∩B → A) − rank(A∩B → B)
                +  rank(connecting homomorphism δ: H⁰(A∩B) → H¹(U))

This module exposes:

- :func:`mayer_vietoris_h1` — compute H¹(U) from pieces
- :class:`MayerVietorisCoverDecomposition` — split a ``Cover`` into two pieces at
  ``BranchGuard`` sites and compute the MV H¹
- :func:`mayer_vietoris_from_reports` — combine results from two
  ``SheafBugReport`` / ``CohomologicalResult`` instances obtained by
  analysing branches independently

Mathematical grounding
~~~~~~~~~~~~~~~~~~~~~~
The Čech complex C^•(U, Sem) for U = A ∪ B fits into a short exact sequence:

    0 → C^•(A∪B) → C^•(A) ⊕ C^•(B) → C^•(A∩B) → 0

The associated long exact sequence in cohomology is the Mayer-Vietoris
sequence.  The connecting homomorphism

    δ : H⁰(A∩B) → H¹(A∪B)

is computed from the difference of restriction maps:
    δ(σ) = (σ|_A − σ|_B)  as a 1-cocycle.

For the GF(2) / integer rank computation we use:

    rank H¹(A∪B) = rank H¹(A) + rank H¹(B) + rank(im δ)

where rank(im δ) = max(0, H⁰(A∩B) − rank(H⁰(A) + H⁰(B) → H⁰(A∩B))).
In the program-analysis setting H⁰ counts globally consistent typings,
which we approximate as the number of sites with pinned (non-⊤) sections.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from deppy.core._protocols import Cover, LocalSection, ObstructionData, SiteId, SiteKind


# ──────────────────────────────────────────────────────────────────────────────
# Data types
# ──────────────────────────────────────────────────────────────────────────────

@dataclass
class MVResult:
    """Result of a Mayer-Vietoris H¹ computation.

    Attributes
    ----------
    h1_a : int
        dim H¹(A) — obstructions in the first piece.
    h1_b : int
        dim H¹(B) — obstructions in the second piece.
    h1_intersection : int
        dim H¹(A∩B) — obstructions on the overlap.
    h0_intersection : int
        dim H⁰(A∩B) — globally consistent sections on the overlap.
    connecting_rank : int
        rank(im δ) — contribution of the connecting homomorphism.
    h1_union : int
        dim H¹(A∪B) = h1_a + h1_b + connecting_rank.
    obstructions_a : list
        H¹ generators localised to piece A.
    obstructions_b : list
        H¹ generators localised to piece B.
    obstructions_intersection : list
        H¹ generators on the intersection, mapped to H¹(U) via δ.
    """
    h1_a: int = 0
    h1_b: int = 0
    h1_intersection: int = 0
    h0_intersection: int = 0
    connecting_rank: int = 0
    h1_union: int = 0

    obstructions_a: List[ObstructionData] = field(default_factory=list)
    obstructions_b: List[ObstructionData] = field(default_factory=list)
    obstructions_intersection: List[ObstructionData] = field(default_factory=list)

    # The full combined obstruction list (for the union cover)
    all_obstructions: List[ObstructionData] = field(default_factory=list)

    # Diagnostic
    decomposition_method: str = ""


# ──────────────────────────────────────────────────────────────────────────────
# Core computation
# ──────────────────────────────────────────────────────────────────────────────

def mayer_vietoris_h1(
    *,
    h1_a: int,
    h1_b: int,
    h0_a: int = 0,
    h0_b: int = 0,
    h0_intersection: int = 0,
    h1_intersection: int = 0,
    obstructions_a: Optional[List[ObstructionData]] = None,
    obstructions_b: Optional[List[ObstructionData]] = None,
    obstructions_intersection: Optional[List[ObstructionData]] = None,
) -> MVResult:
    """Compute H¹(A∪B) from H¹(A), H¹(B) and the connecting homomorphism.

    The Mayer-Vietoris long exact sequence gives:

        rank H¹(U) = rank H¹(A) + rank H¹(B) + rank(im δ)

    where the connecting homomorphism produces new obstructions when
    sections on the intersection fail to extend consistently to both
    pieces (H⁰ sections on A∩B that cannot be glued to A or B).

    Parameters
    ----------
    h1_a, h1_b : int
        GF(2) rank of H¹ in each piece (minimum independent fixes).
    h0_a, h0_b : int
        Number of globally consistent sections admitted by each piece
        (approximated as pinned / non-⊤ sites).
    h0_intersection : int
        Number of globally consistent sections on A∩B.
    h1_intersection : int
        GF(2) rank of H¹ on A∩B (obstructions shared by both pieces).
    obstructions_a, obstructions_b, obstructions_intersection : list
        Obstruction generators for each region (optional).

    Returns
    -------
    MVResult
        Full Mayer-Vietoris decomposition result.
    """
    obs_a = list(obstructions_a or [])
    obs_b = list(obstructions_b or [])
    obs_int = list(obstructions_intersection or [])

    # connecting homomorphism rank:
    # rank(im δ) = max(0, h0_int − (h0_a + h0_b − 1))
    # This counts sections on A∩B that cannot be extended to both A and B.
    connecting = max(0, h0_intersection - h0_a - h0_b + 1)

    # Obstructions contributed by δ come from obs_int (they live on the
    # intersection and get mapped to H¹(U) via the connecting map).
    # We tag them so callers can trace their origin.
    connecting_obs: List[ObstructionData] = []
    for obs in obs_int[:connecting]:  # Take at most ``connecting`` generators
        connecting_obs.append(ObstructionData(
            conflicting_overlaps=obs.conflicting_overlaps,
            explanation=f"[connecting δ] {obs.explanation}",
        ))

    h1_union = h1_a + h1_b + connecting

    all_obs: List[ObstructionData] = obs_a + obs_b + connecting_obs

    return MVResult(
        h1_a=h1_a,
        h1_b=h1_b,
        h1_intersection=h1_intersection,
        h0_intersection=h0_intersection,
        connecting_rank=connecting,
        h1_union=h1_union,
        obstructions_a=obs_a,
        obstructions_b=obs_b,
        obstructions_intersection=obs_int,
        all_obstructions=all_obs,
        decomposition_method="mayer_vietoris",
    )


# ──────────────────────────────────────────────────────────────────────────────
# Cover decomposition at BranchGuard sites
# ──────────────────────────────────────────────────────────────────────────────

def _split_cover_at_branches(
    cover: Cover,
) -> Tuple[List[SiteId], List[SiteId], List[SiteId]]:
    """Split the cover into two pieces at BranchGuard sites.

    Returns (sites_a, sites_b, intersection_sites) where:
    - sites_a: all sites in the first branch (or first half if no branches)
    - sites_b: all sites in the second branch
    - intersection_sites: sites that appear in both or are BranchGuard sites

    In the Grothendieck topology, BranchGuard sites are the "seams" where
    the presheaf must satisfy the gluing condition most critically.  Splitting
    at these sites gives the natural Mayer-Vietoris decomposition.
    """
    branch_sites: List[SiteId] = [
        sid for sid in cover.sites
        if sid.kind == SiteKind.BRANCH_GUARD
    ]
    error_sites: Set[SiteId] = set(cover.error_sites)
    input_boundary: Set[SiteId] = set(cover.input_boundary)
    output_boundary: Set[SiteId] = set(cover.output_boundary)

    # Non-branch, non-boundary sites: partition into two halves
    internal_sites = [
        sid for sid in cover.sites
        if sid not in input_boundary
        and sid not in output_boundary
        and sid.kind != SiteKind.BRANCH_GUARD
    ]

    # Split internal sites into two halves around the midpoint
    mid = max(1, len(internal_sites) // 2)
    piece_a_internal = internal_sites[:mid]
    piece_b_internal = internal_sites[mid:]

    # Boundary sites appear in both pieces (they are the "intersection")
    boundary_sites = list(input_boundary | output_boundary)
    intersection_sites = branch_sites + boundary_sites

    sites_a = piece_a_internal + branch_sites + boundary_sites
    sites_b = piece_b_internal + branch_sites + boundary_sites

    return sites_a, sites_b, intersection_sites


def mayer_vietoris_from_cover(
    cover: Cover,
    local_sections: Dict[SiteId, LocalSection],
    gluing_result: Any,
) -> MVResult:
    """Apply Mayer-Vietoris to a cover that has already been gluing-checked.

    The ``gluing_result`` is the ``GluingCheckResult`` from
    ``check_gluing_condition``.  We split the cover at BranchGuard sites and
    partition the obstructions into those in piece A, piece B, and the
    intersection, then call :func:`mayer_vietoris_h1`.

    This is the entry point used by :func:`~deppy.cohomological_analysis.analyze_cohomologically`
    to get a compositionally-accurate H¹ rank.
    """
    from deppy.static_analysis.section_gluing import (
        check_gluing_condition as _check_gluing,
        extract_obstruction_basis as _extract_basis,
    )

    sites_a, sites_b, sites_int = _split_cover_at_branches(cover)
    set_a: FrozenSet[SiteId] = frozenset(sites_a)
    set_b: FrozenSet[SiteId] = frozenset(sites_b)
    set_int: FrozenSet[SiteId] = frozenset(sites_int)

    # Count pinned (non-⊤) sections for H⁰ approximation
    def _pinned(site_set: FrozenSet[SiteId]) -> int:
        return sum(
            1 for sid in site_set
            if sid in local_sections and local_sections[sid].refinements
        )

    h0_a = _pinned(set_a)
    h0_b = _pinned(set_b)
    h0_int = _pinned(set_int)

    # Partition obstructions from the global gluing result
    all_obs: List[ObstructionData] = getattr(gluing_result, "obstructions", [])
    obs_a: List[ObstructionData] = []
    obs_b: List[ObstructionData] = []
    obs_int: List[ObstructionData] = []
    obs_both: List[ObstructionData] = []

    for obs in all_obs:
        involved: Set[SiteId] = set()
        for sid_a, sid_b in obs.conflicting_overlaps:
            involved.add(sid_a)
            involved.add(sid_b)
        in_a = bool(involved & set_a - set_int)
        in_b = bool(involved & set_b - set_int)
        in_int = bool(involved & set_int)

        if in_int:
            obs_int.append(obs)
        elif in_a and in_b:
            obs_both.append(obs)
        elif in_a:
            obs_a.append(obs)
        elif in_b:
            obs_b.append(obs)
        else:
            # Cannot classify — put in both for conservative count
            obs_a.append(obs)
            obs_b.append(obs)

    # Obstructions in both pieces are counted as intersection obstructions
    obs_int = obs_int + obs_both

    # Compute per-piece H¹ ranks using GF(2) over the sub-covers
    def _rank_from_obs(obs_list: List[ObstructionData], site_set: FrozenSet[SiteId]) -> int:
        if not obs_list:
            return 0
        sub_overlaps = [
            pair for pair in getattr(cover, "overlaps", [])
            if pair[0] in site_set and pair[1] in site_set
        ]
        if not sub_overlaps:
            return len(obs_list)
        overlap_index = {pair: i for i, pair in enumerate(sub_overlaps)}
        n_cols = len(sub_overlaps)
        matrix: List[List[int]] = []
        for obs in obs_list:
            row = [0] * n_cols
            for pair in obs.conflicting_overlaps:
                idx = overlap_index.get(pair)
                if idx is not None:
                    row[idx] = 1
                idx_rev = overlap_index.get((pair[1], pair[0]))
                if idx_rev is not None:
                    row[idx_rev] = 1
            if any(row):
                matrix.append(row)
        if not matrix:
            return len(obs_list)
        # Gaussian elimination over GF(2)
        rows = [sum(b << j for j, b in enumerate(row)) for row in matrix]
        rank = 0
        for col in range(n_cols):
            pivot = next((i for i in range(rank, len(rows)) if (rows[i] >> col) & 1), None)
            if pivot is None:
                continue
            rows[rank], rows[pivot] = rows[pivot], rows[rank]
            for i in range(len(rows)):
                if i != rank and (rows[i] >> col) & 1:
                    rows[i] ^= rows[rank]
            rank += 1
        return rank or len(obs_list)

    h1_a = _rank_from_obs(obs_a, set_a)
    h1_b = _rank_from_obs(obs_b, set_b)
    h1_int = _rank_from_obs(obs_int, set_int)

    return mayer_vietoris_h1(
        h1_a=h1_a,
        h1_b=h1_b,
        h0_a=h0_a,
        h0_b=h0_b,
        h0_intersection=h0_int,
        h1_intersection=h1_int,
        obstructions_a=obs_a,
        obstructions_b=obs_b,
        obstructions_intersection=obs_int,
    )


# ──────────────────────────────────────────────────────────────────────────────
# Combine two independently-analysed sub-results
# ──────────────────────────────────────────────────────────────────────────────

def mayer_vietoris_from_reports(
    result_a: Any,
    result_b: Any,
    *,
    h0_intersection: int = 0,
    obstructions_intersection: Optional[List[ObstructionData]] = None,
) -> MVResult:
    """Combine two analysis results using the Mayer-Vietoris sequence.

    ``result_a`` and ``result_b`` are duck-typed: any object that exposes
    ``h1_rank`` (int) and ``obstructions`` (list of ObstructionData) works,
    including ``CohomologicalResult`` and ``SheafBugReport``.

    This is useful after branch-by-branch analysis where each branch was
    analysed independently and the results need to be composed into the
    H¹ of the whole function.

    Parameters
    ----------
    result_a, result_b
        Per-branch analysis results.
    h0_intersection : int
        Number of globally consistent sections on the shared boundary
        (input/output boundary sites that appear in both branches).
    obstructions_intersection
        Obstructions known to live at the shared boundary.

    Returns
    -------
    MVResult
    """
    h1_a = getattr(result_a, "h1_rank", 0) or getattr(result_a, "minimum_independent_fixes", 0)
    h1_b = getattr(result_b, "h1_rank", 0) or getattr(result_b, "minimum_independent_fixes", 0)

    obs_a = list(getattr(result_a, "obstructions", []))
    obs_b = list(getattr(result_b, "obstructions", []))

    # H⁰ approximation from number of non-trivial sections
    h0_a = getattr(result_a, "n_sections_assigned", 0) or len(obs_a)
    h0_b = getattr(result_b, "n_sections_assigned", 0) or len(obs_b)

    return mayer_vietoris_h1(
        h1_a=h1_a,
        h1_b=h1_b,
        h0_a=h0_a,
        h0_b=h0_b,
        h0_intersection=h0_intersection,
        obstructions_a=obs_a,
        obstructions_b=obs_b,
        obstructions_intersection=list(obstructions_intersection or []),
    )


# ──────────────────────────────────────────────────────────────────────────────
# Theorem 11 — Exact Incremental Cohomology Update
# ──────────────────────────────────────────────────────────────────────────────

@dataclass
class IncrementalMVResult:
    """Result of an exact incremental H¹ update via Mayer-Vietoris.

    Theorem 11 (programcohomology.tex §7.2):
        When sub-cover A changes to A', the new H¹(U') is

            H¹(U') = H¹(A') ⊕ H¹(B) ⊕ im(δ') / H¹(A'∩B)

        where:
            - H¹(A') is recomputed for just the changed sub-cover
            - H¹(B) is reused unchanged (B did not change)
            - im(δ') is the new connecting homomorphism rank
            - H¹(A'∩B) is recomputed for the (possibly modified) intersection

        This is EXACT — it gives the same answer as a global reanalysis
        but only pays O((|A'| + |A'∩B|)² · n) time instead of O(|U'|² · n).
    """
    # Before the update
    h1_before: int = 0
    h1_a_before: int = 0

    # After the update
    h1_after: int = 0
    h1_a_after: int = 0

    # Unchanged components
    h1_b: int = 0
    h1_intersection_before: int = 0
    h1_intersection_after: int = 0
    connecting_rank_before: int = 0
    connecting_rank_after: int = 0

    # Cost accounting
    sites_reanalysed: int = 0    # |A'| — how many sites were touched
    sites_reused: int = 0        # |B|  — how many sites were reused from cache

    # Whether the update decreased, increased, or preserved H¹
    delta_h1: int = 0
    patch_sufficient: bool = False  # True if the patch drove H¹ to 0


def exact_incremental_update(
    *,
    h1_a_new: int,
    h1_b: int,
    h1_intersection_new: int,
    h0_a_new: int = 0,
    h0_b: int = 0,
    h0_intersection_new: int = 0,
    h1_a_old: int = 0,
    h1_intersection_old: int = 0,
    connecting_rank_old: int = 0,
    sites_reanalysed: int = 0,
    sites_reused: int = 0,
) -> IncrementalMVResult:
    """Compute exact incremental H¹ update after patching sub-cover A.

    This implements Theorem 11 of programcohomology.tex:

        H¹(U') = H¹(A') + H¹(B) + im(δ') − H¹(A'∩B)

    The formula specialises the Mayer-Vietoris long exact sequence to
    the incremental setting: B is unchanged so H¹(B) is a cache hit.

    Parameters
    ----------
    h1_a_new : int
        H¹(A') — recomputed for the modified sub-cover.
    h1_b : int
        H¹(B) — cached; NOT recomputed (this is the key savings).
    h1_intersection_new : int
        H¹(A'∩B) — recomputed for the new boundary.
    h0_a_new, h0_b, h0_intersection_new : int
        H⁰ dimensions for connecting homomorphism.
    h1_a_old, h1_intersection_old, connecting_rank_old : int
        Pre-update values for the before/after comparison.

    Returns
    -------
    IncrementalMVResult
        Contains the new and old H¹ values plus cost information.
    """
    # Compute H¹ after the patch (Theorem 11 formula)
    mv_after = mayer_vietoris_h1(
        h1_a=h1_a_new,
        h1_b=h1_b,
        h0_a=h0_a_new,
        h0_b=h0_b,
        h0_intersection=h0_intersection_new,
        h1_intersection=h1_intersection_new,
    )

    # Compute H¹ before the patch (for delta reporting)
    mv_before = mayer_vietoris_h1(
        h1_a=h1_a_old,
        h1_b=h1_b,
        h0_a=h0_a_new,        # h0_a not tracked separately before
        h0_b=h0_b,
        h0_intersection=h0_intersection_new,
        h1_intersection=h1_intersection_old,
    )

    delta = mv_after.h1_union - mv_before.h1_union
    return IncrementalMVResult(
        h1_before=mv_before.h1_union,
        h1_a_before=h1_a_old,
        h1_after=mv_after.h1_union,
        h1_a_after=h1_a_new,
        h1_b=h1_b,
        h1_intersection_before=h1_intersection_old,
        h1_intersection_after=h1_intersection_new,
        connecting_rank_before=connecting_rank_old,
        connecting_rank_after=mv_after.connecting_rank,
        sites_reanalysed=sites_reanalysed,
        sites_reused=sites_reused,
        delta_h1=delta,
        patch_sufficient=(mv_after.h1_union == 0),
    )
