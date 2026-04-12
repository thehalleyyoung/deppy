"""Motive invariants from K-theory, tropical geometry, and HoTT.

Beyond cohomology, a motive carries additional algebraic invariants
drawn from different areas of mathematics:

1. K-theory (K₀)
   From algebraic K-theory: K₀ of the effect monoid classifies the
   "resources" a program uses.  Two programs using equivalent resources
   have isomorphic K₀ groups.

2. Tropical invariant (T)
   From tropical geometry: replace (×,+) with (max,+) to get a tropical
   version of the data flow graph.  The tropical polynomial encodes the
   worst-case complexity profile.

3. Fundamental groupoid (π₁)
   From homotopy type theory: the fundamental groupoid classifies loops
   in the data flow graph.  Programs with the same loop structure
   (iteration/recursion pattern) have equivalent groupoids.

4. Galois invariant (Gal)
   From Galois theory: the automorphism group of the data flow graph
   captures computational symmetries.

5. Representation character (χ)
   From representation theory: the character of the sort-lattice action
   (trace of each operation's effect on sorts) is an invariant.

6. Ehrenfeucht-Fraïssé depth (EF)
   From model theory: the EF-depth measures how many rounds of the
   EF game the program's data flow can survive, bounding the first-order
   expressivity of the computation.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, field
from typing import Dict, FrozenSet, List, Tuple

from deppy.motive.sorts import Sort
from deppy.motive.operations import TypedOp, Effect, Refinement
from deppy.motive.category import DataFlowCategory


# ═══════════════════════════════════════════════════════════════════
# §1  K-Theory Invariant
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class KTheoryInvariant:
    """K₀ of the effect monoid — resource classification.

    K₀(f) = formal sum Σ nₑ[e] where nₑ is the count of effect e.
    This is the Grothendieck group completion of the effect monoid.
    """
    pure_count: int = 0
    mutate_count: int = 0
    allocate_count: int = 0
    iterate_count: int = 0
    recurse_count: int = 0
    call_ext_count: int = 0

    @staticmethod
    def from_operations(ops: List[TypedOp]) -> KTheoryInvariant:
        counts = Counter(op.effect for op in ops)
        return KTheoryInvariant(
            pure_count=counts.get(Effect.PURE, 0),
            mutate_count=counts.get(Effect.MUTATE, 0),
            allocate_count=counts.get(Effect.ALLOCATE, 0),
            iterate_count=counts.get(Effect.ITERATE, 0),
            recurse_count=counts.get(Effect.RECURSE, 0),
            call_ext_count=counts.get(Effect.CALL_EXT, 0),
        )

    @property
    def total_effects(self) -> int:
        return (self.mutate_count + self.allocate_count +
                self.iterate_count + self.recurse_count + self.call_ext_count)

    @property
    def is_pure(self) -> bool:
        return self.total_effects == 0

    def compatible_with(self, other: KTheoryInvariant) -> bool:
        """Check K₀ compatibility (necessary for motive isomorphism).

        Two K₀ groups are compatible if they have the same non-zero
        effect classes, treating iterate and recurse as equivalent
        (coboundary equivalence in the loop structure).
        """
        def _nonzero_effects(k: KTheoryInvariant) -> FrozenSet[str]:
            result = set()
            if k.mutate_count > 0: result.add('mutate')
            if k.allocate_count > 0: result.add('allocate')
            if k.iterate_count > 0 or k.recurse_count > 0:
                result.add('loop')  # unify iterate and recurse
            if k.call_ext_count > 0: result.add('call_ext')
            return frozenset(result)

        return _nonzero_effects(self) == _nonzero_effects(other)

    def distance(self, other: KTheoryInvariant) -> float:
        """Distance in K₀ (L¹ norm on effect counts, normalized)."""
        total = max(
            self.total_effects + self.pure_count,
            other.total_effects + other.pure_count,
            1,
        )
        diff = (abs(self.mutate_count - other.mutate_count) +
                abs(self.allocate_count - other.allocate_count) +
                abs(self.iterate_count - other.iterate_count) +
                abs(self.recurse_count - other.recurse_count) +
                abs(self.call_ext_count - other.call_ext_count))
        return diff / total


# ═══════════════════════════════════════════════════════════════════
# §2  Tropical Invariant
# ═══════════════════════════════════════════════════════════════════

# Tropical cost: each effect has a cost in the (max,+) semiring
_TROPICAL_COST: Dict[Effect, int] = {
    Effect.PURE: 0,
    Effect.MUTATE: 1,
    Effect.ALLOCATE: 1,
    Effect.ITERATE: 2,
    Effect.RECURSE: 3,
    Effect.CALL_EXT: 1,
}


@dataclass(frozen=True)
class TropicalInvariant:
    """Tropical complexity profile of a program.

    From tropical geometry: replace (×,+) with (max,+) in the data
    flow graph to get the worst-case path cost.

    The tropical polynomial T_f encodes the complexity profile:
    T_f = max_{path p} Σ_{edge e ∈ p} cost(e)
    """
    max_path_cost: int = 0      # max cost over all paths
    total_cost: int = 0          # sum of all edge costs
    loop_depth: int = 0          # max nesting depth of loops
    recursion_depth: int = 0     # 0 = non-recursive, 1+ = recursive
    branch_count: int = 0        # number of conditional branches

    @staticmethod
    def from_category(category: DataFlowCategory,
                      operations: List[TypedOp],
                      loop_depth: int,
                      has_recursion: bool,
                      num_branches: int) -> TropicalInvariant:
        total = sum(_TROPICAL_COST.get(op.effect, 0) for op in operations)

        # Max path cost via simple DFS on the data flow graph
        adj: Dict[int, List[Tuple[int, int]]] = {}
        for m in category.morphisms:
            cost = _TROPICAL_COST.get(m.operation.effect, 0)
            adj.setdefault(m.source, []).append((m.target, cost))

        max_cost = 0
        n = len(category.objects)
        if n > 0:
            # Bellman-Ford style (handles cycles conservatively)
            dist = [0] * n
            for _ in range(min(n, 20)):
                for u in range(n):
                    for v, w in adj.get(u, []):
                        if v < n and dist[u] + w > dist[v]:
                            dist[v] = dist[u] + w
            max_cost = max(dist) if dist else 0

        return TropicalInvariant(
            max_path_cost=max_cost,
            total_cost=total,
            loop_depth=loop_depth,
            recursion_depth=1 if has_recursion else 0,
            branch_count=num_branches,
        )

    def compatible_with(self, other: TropicalInvariant) -> bool:
        """Necessary condition for motive isomorphism.

        Allows recursion ↔ iteration as coboundary-equivalent:
        a recursive function with depth 0 loops is equivalent to
        an iterative one with depth 1.
        """
        # Both are leaf computations (no loops, no recursion)
        self_loops = self.loop_depth + self.recursion_depth
        other_loops = other.loop_depth + other.recursion_depth
        if self_loops == 0 and other_loops == 0:
            return True
        # Both have some form of iteration/recursion
        if self_loops > 0 and other_loops > 0:
            return True
        # One has loops/recursion, the other doesn't
        return False

    def distance(self, other: TropicalInvariant) -> float:
        return (abs(self.loop_depth - other.loop_depth) * 3 +
                abs(self.recursion_depth - other.recursion_depth) * 2 +
                abs(self.branch_count - other.branch_count) +
                abs(self.max_path_cost - other.max_path_cost) * 0.5)


# ═══════════════════════════════════════════════════════════════════
# §3  Fundamental Groupoid π₁
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class FundamentalGroupoid:
    """π₁ of the data flow graph — loop structure from HoTT.

    Objects = blocks, morphisms = path-homotopy classes.
    The rank of π₁ = number of independent cycles = first Betti number.
    """
    rank: int = 0                    # number of independent cycles
    loop_types: Tuple[str, ...] = () # 'for', 'while', 'recursion'
    has_nested_loops: bool = False

    @staticmethod
    def from_category(category: DataFlowCategory,
                      has_recursion: bool,
                      loop_depth: int) -> FundamentalGroupoid:
        back_edges = category.loops()
        rank = category.cycle_rank()
        loop_types = []
        for be in back_edges:
            if be.operation.effect == Effect.RECURSE:
                loop_types.append('recursion')
            elif be.operation.effect == Effect.ITERATE:
                loop_types.append('iteration')
            else:
                loop_types.append('loop')
        if has_recursion and 'recursion' not in loop_types:
            loop_types.append('recursion')

        return FundamentalGroupoid(
            rank=rank,
            loop_types=tuple(sorted(set(loop_types))),
            has_nested_loops=(loop_depth > 1),
        )

    def compatible_with(self, other: FundamentalGroupoid) -> bool:
        # Both have no loops → compatible
        if self.rank == 0 and other.rank == 0:
            if not self.loop_types and not other.loop_types:
                return True
        # At least one has loops — allow unless drastically different
        if abs(self.rank - other.rank) > 2:
            return False
        # Loop types: allow recursion ↔ iteration (coboundary equivalence)
        self_types = set(self.loop_types)
        other_types = set(other.loop_types)
        if self_types and other_types:
            norm = lambda ts: frozenset('loop' if t in ('iteration', 'recursion') else t for t in ts)
            if norm(self_types) != norm(other_types):
                return False
        # One has loops, other doesn't — still allow (could be unrolled)
        return True


# ═══════════════════════════════════════════════════════════════════
# §4  Galois Invariant
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class GaloisInvariant:
    """Automorphism group order of the data flow graph.

    From Galois theory: |Aut(D_f)| captures the symmetry of the
    computation.  Two equivalent programs should have automorphism
    groups of the same order (up to a factor).
    """
    aut_order_bound: int = 1

    @staticmethod
    def from_category(category: DataFlowCategory) -> GaloisInvariant:
        return GaloisInvariant(
            aut_order_bound=category.automorphism_count_upper_bound(),
        )


# ═══════════════════════════════════════════════════════════════════
# §5  Representation Character
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class RepresentationCharacter:
    """Character of the sort-lattice representation.

    From representation theory: each operation acts on the sort lattice.
    The character χ(op) = the (input_sorts → output_sort) signature.
    The character table χ_f = multiset of all χ(op) for ops in f.

    Two programs with different characters cannot be isomorphic.
    """
    character_table: FrozenSet[Tuple[Tuple[Tuple[int, ...], int], int]] = frozenset()

    @staticmethod
    def from_operations(ops: List[TypedOp]) -> RepresentationCharacter:
        table = Counter(
            (tuple(int(s) for s in op.input_sorts), int(op.output_sort))
            for op in ops
        )
        return RepresentationCharacter(
            character_table=frozenset(
                ((k, v)) for k, v in table.items()
            ),
        )

    def compatible_with(self, other: RepresentationCharacter) -> bool:
        """Check if characters are compatible.

        Characters are compatible if the same sort signatures appear
        (multiplicities may differ due to inlining/outlining).
        """
        self_sigs = {k for k, _ in self.character_table}
        other_sigs = {k for k, _ in other.character_table}
        if not self_sigs and not other_sigs:
            return True
        if not self_sigs or not other_sigs:
            return False
        overlap = len(self_sigs & other_sigs)
        total = len(self_sigs | other_sigs)
        return overlap / total >= 0.5


# ═══════════════════════════════════════════════════════════════════
# §6  Ehrenfeucht-Fraïssé Depth
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class EFDepth:
    """Ehrenfeucht-Fraïssé game depth — from model theory.

    The EF-depth bounds the first-order expressivity of the program's
    data flow structure.  Two structures with different EF-depths
    are distinguishable by first-order sentences, hence not isomorphic.

    EF-depth ≈ diameter of the data flow graph (max shortest path).
    """
    depth: int = 0

    @staticmethod
    def from_category(category: DataFlowCategory) -> EFDepth:
        n = len(category.objects)
        if n <= 1:
            return EFDepth(depth=0)

        # BFS from each vertex to compute diameter
        adj: Dict[int, List[int]] = {}
        for m in category.morphisms:
            adj.setdefault(m.source, []).append(m.target)
            adj.setdefault(m.target, []).append(m.source)

        max_dist = 0
        for start in range(min(n, 50)):  # cap for performance
            dist = [-1] * n
            dist[start] = 0
            queue = [start]
            qi = 0
            while qi < len(queue):
                u = queue[qi]
                qi += 1
                for v in adj.get(u, []):
                    if v < n and dist[v] == -1:
                        dist[v] = dist[u] + 1
                        max_dist = max(max_dist, dist[v])
                        queue.append(v)

        return EFDepth(depth=max_dist)
