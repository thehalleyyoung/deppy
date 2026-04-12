"""High-level applications of computational motives.

All program analysis tasks reduce to operations on motives:

1. Equivalence:   M(f) ≅ M(g)           — are f and g the same program?
2. Bug detection:  H¹(M(f)) ≠ 0          — does f have type obstructions?
3. Spec checking:  M(impl) refines M(spec) — does impl satisfy spec?
4. Similarity:    d(M(f), M(g))          — how similar are f and g?
5. Refactoring:   M(before) ≅ M(after)   — did refactoring preserve semantics?
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Tuple

from deppy.motive.motive import Motive
from deppy.motive.extractor import motive_of
from deppy.motive.isomorphism import MotiveIsomorphismSolver


@dataclass(frozen=True)
class EquivalenceResult:
    """Result of an equivalence check between two programs."""
    equivalent: Optional[bool]
    explanation: str
    motive_f: Optional[Motive] = None
    motive_g: Optional[Motive] = None

    @property
    def is_conclusive(self) -> bool:
        return self.equivalent is not None


@dataclass(frozen=True)
class BugDetectionResult:
    """Result of bug detection via cohomological analysis."""
    has_obstruction: bool
    h1_rank: int
    h2_rank: int
    obstructions: Tuple[str, ...] = ()
    explanation: str = ""


@dataclass(frozen=True)
class SimilarityResult:
    """Result of motive similarity computation."""
    distance: float
    explanation: str


def check_equivalence(source_f: str, source_g: str,
                      func_name_f: Optional[str] = None,
                      func_name_g: Optional[str] = None,
                      timeout_ms: int = 5000) -> EquivalenceResult:
    """Check if two programs are equivalent via motive isomorphism.

    This is the primary application of computational motives.

    Args:
        source_f: Source code of first program
        source_g: Source code of second program
        func_name_f: Name of function in first program (auto-detected if None)
        func_name_g: Name of function in second program (auto-detected if None)
        timeout_ms: Z3 solver timeout in milliseconds

    Returns:
        EquivalenceResult with verdict and explanation
    """
    mf = motive_of(source_f, func_name_f)
    mg = motive_of(source_g, func_name_g)

    if mf is None or mg is None:
        return EquivalenceResult(
            equivalent=None,
            explanation="Failed to extract motive",
            motive_f=mf, motive_g=mg,
        )

    solver = MotiveIsomorphismSolver(timeout_ms=timeout_ms)
    result, explanation = solver.check(mf, mg)

    return EquivalenceResult(
        equivalent=result,
        explanation=explanation,
        motive_f=mf, motive_g=mg,
    )


def detect_bugs(source: str, func_name: Optional[str] = None) -> BugDetectionResult:
    """Detect potential bugs via cohomological analysis.

    H¹ ≠ 0 means there are type obstructions — places where the
    program's local type assignments don't agree globally.  These
    are potential bugs (or intentional polymorphism).

    H² ≠ 0 means there are higher coherence failures — places where
    the cocycle condition fails on triangles.
    """
    m = motive_of(source, func_name)
    if m is None:
        return BugDetectionResult(
            has_obstruction=False, h1_rank=0, h2_rank=0,
            explanation="Failed to extract motive",
        )

    obs_strs = m.cohomology.h1.generators
    return BugDetectionResult(
        has_obstruction=(m.h1 > 0 or m.h2 > 0),
        h1_rank=m.h1,
        h2_rank=m.h2,
        obstructions=obs_strs,
        explanation=(f"H¹={m.h1}, H²={m.h2}. "
                    f"{'Type obstructions detected.' if m.h1 > 0 else 'No obstructions.'} "
                    f"{'Coherence failures.' if m.h2 > 0 else ''}"),
    )


def compute_similarity(source_f: str, source_g: str,
                       func_name_f: Optional[str] = None,
                       func_name_g: Optional[str] = None) -> SimilarityResult:
    """Compute similarity between two programs via motive distance."""
    mf = motive_of(source_f, func_name_f)
    mg = motive_of(source_g, func_name_g)

    if mf is None or mg is None:
        return SimilarityResult(distance=float('inf'), explanation="Failed to extract motive")

    d = mf.distance(mg)
    return SimilarityResult(
        distance=d,
        explanation=(f"Motive distance={d:.2f}. "
                    f"H⁰={mf.h0}/{mg.h0}, H¹={mf.h1}/{mg.h1}, "
                    f"ops={mf.op_count}/{mg.op_count}"),
    )
