"""MotivePresheaf — the type presheaf over the nerve complex.

A presheaf F: N(C)^op → FinSet assigns to each simplex of the nerve
its type fiber.  This is the central mathematical object of the
computational motive theory.

For a program with data flow category C:

    F(vertex v)     = TypeFiber at v
    F(edge e: u→v)  = restriction map Fiber(v) → Fiber(u)

The presheaf encodes the dependent type structure of the program:
each program point has a fiber (the local type) and the restriction
maps express how types transform along operations.

The sheaf condition (gluing axiom) says: sections that agree on
overlaps can be glued into a global section.  The obstruction to
gluing is measured by H¹ of the Čech complex.

When H¹ = 0, the presheaf IS a sheaf, and the program has a
globally consistent type assignment.  When H¹ ≠ 0, there are
type mismatches — potential bugs or intentional polymorphism.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from deppy.motive.sorts import Sort, sorts_compatible
from deppy.motive.fiber import TypeFiber, FiberMorphism
from deppy.motive.category import DataFlowCategory
from deppy.motive.nerve import NerveComplex, Simplex0, Simplex1, Simplex2


@dataclass
class PresheafSection:
    """A section of the type presheaf over a subset of the nerve.

    In the Čech complex, a 0-cochain is a choice of section (TypeFiber)
    for each vertex in the cover.  A 1-cochain is a choice of section
    for each edge.
    """
    vertex_fibers: Dict[int, TypeFiber] = field(default_factory=dict)
    edge_fibers: Dict[Tuple[int, int], TypeFiber] = field(default_factory=dict)
    fiber_morphisms: List[FiberMorphism] = field(default_factory=list)


class MotivePresheaf:
    """The type presheaf over the nerve of a data flow category.

    Provides:
    1. Section assignment at each vertex and edge
    2. Restriction maps along morphisms
    3. Gluing/compatibility checks
    4. Čech cochain groups C⁰, C¹
    """

    def __init__(self, category: DataFlowCategory,
                 nerve: NerveComplex) -> None:
        self._cat = category
        self._nerve = nerve
        self._sections = PresheafSection()
        self._build()

    def _build(self) -> None:
        """Build the presheaf by assigning fibers from the category."""
        # Vertex fibers come from the category objects
        for i, obj in enumerate(self._cat.objects):
            self._sections.vertex_fibers[i] = obj.fiber

        # Edge fibers come from restriction along morphisms
        for m in self._cat.morphisms:
            if (0 <= m.source < len(self._cat.objects) and
                    0 <= m.target < len(self._cat.objects)):
                src_fiber = self._cat.objects[m.source].fiber
                tgt_fiber = self._cat.objects[m.target].fiber
                # The edge fiber is the "intersection" of the two fibers
                edge_fiber = src_fiber.join(tgt_fiber)
                self._sections.edge_fibers[(m.source, m.target)] = edge_fiber
                self._sections.fiber_morphisms.append(
                    FiberMorphism.from_operation(src_fiber, tgt_fiber, m.operation)
                )

    # ── Presheaf evaluation ──

    def fiber_at(self, vertex: int) -> TypeFiber:
        """F(vertex) — the type fiber at a vertex."""
        return self._sections.vertex_fibers.get(vertex, TypeFiber.empty())

    def fiber_along(self, source: int, target: int) -> TypeFiber:
        """F(edge) — the restriction fiber along an edge."""
        return self._sections.edge_fibers.get((source, target), TypeFiber.empty())

    # ── Cochain groups ──

    def cochains_0(self) -> Dict[int, TypeFiber]:
        """C⁰(U, F) = product of fibers over all vertices."""
        return dict(self._sections.vertex_fibers)

    def cochains_1(self) -> Dict[Tuple[int, int], TypeFiber]:
        """C¹(U, F) = product of fibers over all edges."""
        return dict(self._sections.edge_fibers)

    # ── Coboundary δ⁰ ──

    def coboundary_0(self) -> List[Tuple[Tuple[int, int], Optional[str]]]:
        """δ⁰: C⁰ → C¹ — check if vertex fibers agree along edges.

        For each edge e: u→v, computes (δ⁰σ)(e) = σ(v) - σ(u).
        Returns list of (edge, obstruction) where obstruction is None
        if the fibers agree, or a description of the mismatch.
        """
        results = []
        for s1 in self._nerve.dim1:
            fiber_src = self.fiber_at(s1.source)
            fiber_tgt = self.fiber_at(s1.target)
            obstruction = fiber_src.obstruction_with(fiber_tgt)
            results.append(((s1.source, s1.target), obstruction))
        return results

    # ── Cocycle condition on 2-simplices ──

    def cocycle_check(self) -> List[Tuple[Simplex2, bool]]:
        """Check the cocycle condition on all 2-simplices.

        For a triangle A→B→C, the cocycle condition says:
            F(A→C) = F(B→C) ∘ F(A→B)

        This is the coherence condition for the presheaf.
        Failures contribute to H² (higher obstructions).
        """
        results = []
        for tri in self._nerve.dim2:
            fiber_a = self.fiber_at(tri.vertex_a)
            fiber_b = self.fiber_at(tri.vertex_b)
            fiber_c = self.fiber_at(tri.vertex_c)
            # Check: A agrees with B, B agrees with C, A agrees with C
            ab_ok = fiber_a.agrees_with(fiber_b)
            bc_ok = fiber_b.agrees_with(fiber_c)
            ac_ok = fiber_a.agrees_with(fiber_c)
            # Cocycle: if AB and BC agree, then AC must agree
            cocycle = not (ab_ok and bc_ok) or ac_ok
            results.append((tri, cocycle))
        return results

    # ── Global sections ──

    def global_sections(self) -> List[Sort]:
        """H⁰ = ker(δ⁰) — sorts that extend to global sections.

        A sort s gives a global section if every vertex fiber contains
        a compatible sort.
        """
        all_sorts = set()
        for fiber in self._sections.vertex_fibers.values():
            all_sorts.update(fiber.sort_set)
        if not all_sorts:
            all_sorts = {Sort.TOP}

        global_sorts = []
        for s in all_sorts:
            is_global = True
            for fiber in self._sections.vertex_fibers.values():
                if not any(sorts_compatible(s, fs) for fs in fiber.sort_set):
                    is_global = False
                    break
            if is_global:
                global_sorts.append(s)
        return global_sorts

    # ── Obstruction classes ──

    def obstructions(self) -> List[str]:
        """H¹ generators — independent type obstructions along edges."""
        obs = []
        for (edge, obstruction) in self.coboundary_0():
            if obstruction is not None:
                obs.append(f"δ⁰ non-zero at {edge}: {obstruction}")
        return obs

    @property
    def is_sheaf(self) -> bool:
        """True if the presheaf satisfies the sheaf condition (H¹ = 0)."""
        return all(obs is None for _, obs in self.coboundary_0())
