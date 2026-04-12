"""The Motive — universal invariant of a program.

The computational motive M(f) of a program f is a tuple:

    M(f) = (Σ, G, H, K, T, π₁, Gal, χ, EF)

where:
    Σ   = algebraic signature (typed operations with refinements/effects)
    G   = data flow category (how operations compose)
    H   = cohomological data (H⁰, H¹, H² from Čech complex)
    K   = K-theory invariant (resource classification)
    T   = tropical invariant (complexity profile)
    π₁  = fundamental groupoid (loop structure)
    Gal = Galois invariant (symmetry group order)
    χ   = representation character (sort-lattice action)
    EF  = Ehrenfeucht-Fraïssé depth (FO expressivity)

The motive is a *universal* invariant: all other invariants of f
can be derived from M(f).  Two programs are equivalent iff their
motives are isomorphic in the motive category.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import FrozenSet, List, Tuple

from deppy.motive.sorts import Sort
from deppy.motive.operations import TypedOp, FlowEdge, Refinement
from deppy.motive.category import DataFlowCategory
from deppy.motive.cohomology import CohomologyData
from deppy.motive.invariants import (
    KTheoryInvariant,
    TropicalInvariant,
    FundamentalGroupoid,
    GaloisInvariant,
    RepresentationCharacter,
    EFDepth,
)


@dataclass
class Motive:
    """The computational motive of a program — its universal invariant.

    This is the central object of the theory.  All program analysis
    tasks (equivalence, bug detection, spec verification, similarity)
    reduce to operations on motives.
    """

    # ── Σ: Algebraic signature ──────────────────────────────────
    operations: List[TypedOp] = field(default_factory=list)

    # ── G: Data flow category ───────────────────────────────────
    flow_edges: List[FlowEdge] = field(default_factory=list)
    num_blocks: int = 0
    category: DataFlowCategory = field(default_factory=DataFlowCategory)

    # ── H: Cohomological data ───────────────────────────────────
    cohomology: CohomologyData = field(default=None)  # type: ignore[assignment]

    # ── K: K-theory invariant ───────────────────────────────────
    k_theory: KTheoryInvariant = field(default_factory=KTheoryInvariant)

    # ── T: Tropical invariant ───────────────────────────────────
    tropical: TropicalInvariant = field(default_factory=TropicalInvariant)

    # ── π₁: Fundamental groupoid ────────────────────────────────
    groupoid: FundamentalGroupoid = field(default_factory=FundamentalGroupoid)

    # ── Gal: Galois invariant ───────────────────────────────────
    galois: GaloisInvariant = field(default_factory=GaloisInvariant)

    # ── χ: Representation character ─────────────────────────────
    character: RepresentationCharacter = field(default_factory=RepresentationCharacter)

    # ── EF: Ehrenfeucht-Fraïssé depth ───────────────────────────
    ef_depth: EFDepth = field(default_factory=EFDepth)

    # ── Σ-type data (from dependent type theory) ────────────────
    input_sorts: Tuple[Sort, ...] = ()
    output_sort: Sort = Sort.TOP
    global_refinements: FrozenSet[Refinement] = frozenset()
    has_recursion: bool = False
    has_iteration: bool = False
    loop_depth: int = 0
    num_branches: int = 0

    # ── Concrete content fingerprints ─────────────────────────
    # These capture concrete details that abstract operations miss.
    # Two programs with identical op structure but different constants,
    # attribute accesses, or argument orderings are NOT equivalent.
    constant_fingerprint: FrozenSet[Tuple] = frozenset()   # multiset of (sort, hash(value))
    attribute_fingerprint: Tuple[str, ...] = ()            # ordered attribute accesses
    name_reference_fingerprint: FrozenSet[str] = frozenset()  # referenced external names
    argument_order_fingerprint: Tuple = ()                  # how params flow to operations

    def __post_init__(self) -> None:
        if self.cohomology is None:
            from deppy.motive.cohomology import CohomologyGroup
            self.cohomology = CohomologyData(
                h0=CohomologyGroup(0, 1),
                h1=CohomologyGroup(1, 0),
                h2=CohomologyGroup(2, 0),
            )

    # ── Convenience accessors ───────────────────────────────────

    @property
    def h0(self) -> int:
        return self.cohomology.h0.rank

    @property
    def h1(self) -> int:
        return self.cohomology.h1.rank

    @property
    def h2(self) -> int:
        return self.cohomology.h2.rank

    @property
    def is_sheaf(self) -> bool:
        """True if the type presheaf is a sheaf (H¹ = 0)."""
        return self.cohomology.is_sheaf

    @property
    def op_count(self) -> int:
        return len(self.operations)

    # ── Necessary conditions for isomorphism ────────────────────
    # NOTE: Most pre-filters have moved into the multi-level Z3 solver
    # (isomorphism.py). Only the hardest necessary conditions remain
    # here for backward compatibility. The solver's _check_pi_type
    # is the authoritative check.

    def necessary_conditions_met(self, other: Motive) -> Tuple[bool, str]:
        """Check necessary conditions for motive isomorphism.

        These are cheap pre-filters. The Z3 solver has its own
        multi-level checks; this is kept for direct motive comparison.
        """
        # Arity
        if len(self.input_sorts) != len(other.input_sorts):
            return False, f"arity {len(self.input_sorts)} ≠ {len(other.input_sorts)}"

        # Output sort
        from deppy.motive.sorts import sorts_compatible
        if not sorts_compatible(self.output_sort, other.output_sort):
            return False, f"output {self.output_sort.name} ≇ {other.output_sort.name}"

        # Cohomological
        if self.h1 != other.h1:
            return False, f"H¹ rank {self.h1} ≠ {other.h1}"

        # Argument order fingerprint — only reject when same iteration pattern
        if self.argument_order_fingerprint and other.argument_order_fingerprint:
            same_pattern = (
                (self.has_recursion == other.has_recursion) and
                (self.has_iteration == other.has_iteration)
            )
            if same_pattern:
                if self.argument_order_fingerprint != other.argument_order_fingerprint:
                    return False, "argument order fingerprint mismatch"

        return True, ""

    def soft_fingerprints_match(self, other: Motive) -> bool:
        """Post-Z3 soft check: do concrete fingerprints agree?

        Used to disambiguate when Z3 says SAT but programs might differ
        in concrete content (str vs repr, different constants, etc.).
        """
        if self.constant_fingerprint and other.constant_fingerprint:
            if self.constant_fingerprint != other.constant_fingerprint:
                return False
        if self.attribute_fingerprint and other.attribute_fingerprint:
            if self.attribute_fingerprint != other.attribute_fingerprint:
                return False
        return True

    # ── Distance in the motive category ─────────────────────────

    def distance(self, other: Motive) -> float:
        """Distance between two motives in the motive category.

        Combines distances from all invariants with weights.
        """
        from deppy.motive.cohomology import CechCohomology

        d_coh = CechCohomology.cohomology_distance(self.cohomology, other.cohomology)
        d_k = self.k_theory.distance(other.k_theory)
        d_trop = self.tropical.distance(other.tropical)

        return d_coh * 3.0 + d_k * 2.0 + d_trop * 1.0
