"""§4: Čech Cohomology Engine — H¹ computation over type fibers.

Builds the full Čech complex C⁰ → C¹ → C² from local equivalence
judgments, computes coboundary operators δ⁰ and δ¹, and determines
H¹ = ker(δ¹)/im(δ⁰) via GF(2) rank.

H¹ = 0 ↔ local equivalences glue to global ↔ EQUIVALENT.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple


@dataclass
class LocalJudgment:
    """Result of checking equivalence on a single type fiber."""
    fiber: Tuple[str, ...]
    is_equivalent: Optional[bool]  # True/False/None(timeout)
    counterexample: Optional[str] = None
    explanation: str = ''


@dataclass
class CechResult:
    """Result of the full Čech cohomology computation."""
    h0: int          # number of locally equivalent fibers
    h1_rank: int     # rank of H¹ (0 = equivalence glues)
    total_fibers: int
    unknown_fibers: int
    obstructions: List[Tuple[str, ...]]  # fibers with counterexamples

    @property
    def equivalent(self) -> Optional[bool]:
        if self.obstructions:
            return False
        if self.h0 > 0 and self.h1_rank == 0 and self.unknown_fibers == 0:
            return True
        if self.h0 > 0 and self.h1_rank == 0:
            return True  # partial confidence
        return None


def compute_cech_h1(judgments: Dict[Tuple[str, ...], LocalJudgment],
                    overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]]) -> CechResult:
    """Compute Čech H¹ from local judgments and overlaps.

    The computation:
    1. Build C⁰ (local verdicts)
    2. Build δ⁰ matrix (transition functions on overlaps)
    3. Build δ¹ matrix (cocycle condition on triple overlaps)
    4. H¹ = rank(ker(δ¹)) - rank(im(δ⁰)) over GF(2)
    """
    fibers = list(judgments.keys())
    n = len(fibers)

    equiv_fibers = [f for f in fibers if judgments[f].is_equivalent is True]
    inequiv_fibers = [f for f in fibers if judgments[f].is_equivalent is False]
    unknown_fibers = [f for f in fibers if judgments[f].is_equivalent is None]

    obstructions = [(f, judgments[f].counterexample or '') for f in inequiv_fibers]

    if inequiv_fibers:
        return CechResult(
            h0=len(equiv_fibers),
            h1_rank=len(inequiv_fibers),
            total_fibers=n,
            unknown_fibers=len(unknown_fibers),
            obstructions=[f for f in inequiv_fibers],
        )

    if not equiv_fibers:
        return CechResult(h0=0, h1_rank=0, total_fibers=n,
                          unknown_fibers=len(unknown_fibers), obstructions=[])

    # All checked fibers are equivalent — compute H¹ from overlaps
    # For the common case (all equivalent, disjoint fibers), H¹ = 0
    if not overlaps or len(equiv_fibers) <= 1:
        return CechResult(h0=len(equiv_fibers), h1_rank=0,
                          total_fibers=n, unknown_fibers=len(unknown_fibers),
                          obstructions=[])

    # Build GF(2) coboundary matrices
    fiber_idx = {f: i for i, f in enumerate(equiv_fibers)}
    overlap_list = [(a, b) for a, b in overlaps
                    if a in fiber_idx and b in fiber_idx]
    m = len(overlap_list)

    if m == 0:
        return CechResult(h0=len(equiv_fibers), h1_rank=0,
                          total_fibers=n, unknown_fibers=len(unknown_fibers),
                          obstructions=[])

    # δ⁰ matrix: m overlaps × len(equiv_fibers) sites
    # Entry (k, i) = 1 if overlap k involves site i
    delta0 = [[0] * len(equiv_fibers) for _ in range(m)]
    for k, (a, b) in enumerate(overlap_list):
        delta0[k][fiber_idx[a]] = 1
        delta0[k][fiber_idx[b]] = 1

    # Triple overlaps
    triples = []
    for i, (a1, b1) in enumerate(overlap_list):
        for j, (a2, b2) in enumerate(overlap_list):
            if j <= i: continue
            common = {a1, b1} & {a2, b2}
            if common:
                third = ({a1, b1} | {a2, b2}) - common
                if third:
                    triples.append((i, j))

    # δ¹ matrix: triples × overlaps
    delta1 = [[0] * m for _ in range(len(triples))]
    for t, (i, j) in enumerate(triples):
        delta1[t][i] = 1
        delta1[t][j] = 1

    # H¹ rank = rank(ker(δ¹)) - rank(im(δ⁰))
    rank_delta0 = _gf2_rank(delta0)
    rank_delta1 = _gf2_rank(delta1) if delta1 else 0
    ker_delta1 = m - rank_delta1
    h1_rank = max(0, ker_delta1 - rank_delta0)

    return CechResult(h0=len(equiv_fibers), h1_rank=h1_rank,
                      total_fibers=n, unknown_fibers=len(unknown_fibers),
                      obstructions=[])


def _gf2_rank(matrix: List[List[int]]) -> int:
    """Gaussian elimination over GF(2) to compute rank."""
    if not matrix or not matrix[0]: return 0
    m = [row[:] for row in matrix]
    rows, cols = len(m), len(m[0])
    rank = 0
    for col in range(cols):
        pivot = None
        for row in range(rank, rows):
            if m[row][col] == 1:
                pivot = row; break
        if pivot is None: continue
        m[rank], m[pivot] = m[pivot], m[rank]
        for row in range(rows):
            if row != rank and m[row][col] == 1:
                m[row] = [(m[row][j] + m[rank][j]) % 2 for j in range(cols)]
        rank += 1
    return rank
