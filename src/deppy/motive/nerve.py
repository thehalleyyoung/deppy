"""NerveComplex — the simplicial structure of a data flow category.

From algebraic topology, the nerve of a category C is a simplicial set N(C):

    N₀ = Ob(C)                          — objects (0-simplices / vertices)
    N₁ = Mor(C)                          — morphisms (1-simplices / edges)
    N₂ = {(f,g) | cod(f) = dom(g)}       — composable pairs (2-simplices / triangles)
    Nₖ = composable k-tuples             — higher simplices

Face maps dᵢ : Nₖ → Nₖ₋₁:
    d₀(f₁,...,fₖ) = (f₂,...,fₖ)          — drop first
    dₖ(f₁,...,fₖ) = (f₁,...,fₖ₋₁)       — drop last
    dᵢ(f₁,...,fₖ) = (...,fᵢ∘fᵢ₊₁,...)   — compose at i

Degeneracy maps sᵢ : Nₖ → Nₖ₊₁:
    sᵢ(f₁,...,fₖ) = (...,fᵢ,id,fᵢ₊₁,...) — insert identity at i

The nerve is the topological space on which we define the type presheaf
and compute Čech cohomology.  Its topology encodes the computational
structure of the program.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, FrozenSet, List, Optional, Set, Tuple

from deppy.motive.category import DataFlowCategory, CategoryMorphism


@dataclass(frozen=True)
class Simplex0:
    """A 0-simplex (vertex) — an object in the data flow category."""
    index: int


@dataclass(frozen=True)
class Simplex1:
    """A 1-simplex (edge) — a morphism in the data flow category."""
    source: int
    target: int
    morphism_index: int


@dataclass(frozen=True)
class Simplex2:
    """A 2-simplex (triangle) — a composable pair of morphisms.

    Represents f: A→B, g: B→C with composition g∘f: A→C.
    The cocycle condition on 2-simplices is the coherence check
    for the type presheaf.
    """
    vertex_a: int
    vertex_b: int
    vertex_c: int
    edge_ab: int   # morphism index for A→B
    edge_bc: int   # morphism index for B→C
    # The third edge A→C is the composition (virtual)


@dataclass(frozen=True)
class Simplex3:
    """A 3-simplex (tetrahedron) — a composable triple.

    Higher coherence: for f: A→B, g: B→C, h: C→D,
    the tetrahedron encodes associativity of composition.
    """
    vertices: Tuple[int, int, int, int]
    edges: Tuple[int, int, int]   # morphism indices


class NerveComplex:
    """The nerve of a data flow category as a simplicial complex.

    Provides:
    1. Simplices at each dimension (0, 1, 2, 3)
    2. Face maps (boundary operators)
    3. Euler characteristic computation
    4. Betti number computation (ranks of homology groups)
    """

    def __init__(self, category: DataFlowCategory) -> None:
        self._cat = category
        self._simplices_0: List[Simplex0] = []
        self._simplices_1: List[Simplex1] = []
        self._simplices_2: List[Simplex2] = []
        self._simplices_3: List[Simplex3] = []
        self._build()

    def _build(self) -> None:
        """Build all simplices from the category."""
        # 0-simplices: objects
        for i in range(len(self._cat.objects)):
            self._simplices_0.append(Simplex0(index=i))

        # 1-simplices: morphisms
        for i, m in enumerate(self._cat.morphisms):
            self._simplices_1.append(Simplex1(
                source=m.source, target=m.target, morphism_index=i,
            ))

        # 2-simplices: composable pairs
        # For each pair (f: A→B, g: B→C), create a triangle
        target_map: Dict[int, List[int]] = {}
        for i, m in enumerate(self._cat.morphisms):
            target_map.setdefault(m.target, []).append(i)

        source_map: Dict[int, List[int]] = {}
        for i, m in enumerate(self._cat.morphisms):
            source_map.setdefault(m.source, []).append(i)

        for mid_vertex in range(len(self._cat.objects)):
            incoming = target_map.get(mid_vertex, [])
            outgoing = source_map.get(mid_vertex, [])
            for f_idx in incoming:
                f = self._cat.morphisms[f_idx]
                for g_idx in outgoing:
                    g = self._cat.morphisms[g_idx]
                    self._simplices_2.append(Simplex2(
                        vertex_a=f.source,
                        vertex_b=mid_vertex,
                        vertex_c=g.target,
                        edge_ab=f_idx,
                        edge_bc=g_idx,
                    ))

        # 3-simplices: composable triples (limited for performance)
        if len(self._simplices_2) < 500:
            for tri in self._simplices_2:
                outgoing_c = source_map.get(tri.vertex_c, [])
                for h_idx in outgoing_c:
                    h = self._cat.morphisms[h_idx]
                    self._simplices_3.append(Simplex3(
                        vertices=(tri.vertex_a, tri.vertex_b, tri.vertex_c, h.target),
                        edges=(tri.edge_ab, tri.edge_bc, h_idx),
                    ))

    # ── Accessors ──

    @property
    def dim0(self) -> List[Simplex0]:
        return self._simplices_0

    @property
    def dim1(self) -> List[Simplex1]:
        return self._simplices_1

    @property
    def dim2(self) -> List[Simplex2]:
        return self._simplices_2

    @property
    def dim3(self) -> List[Simplex3]:
        return self._simplices_3

    # ── Topological invariants ──

    @property
    def euler_characteristic(self) -> int:
        """Euler characteristic χ = |N₀| - |N₁| + |N₂| - |N₃| + ..."""
        return (len(self._simplices_0)
                - len(self._simplices_1)
                + len(self._simplices_2)
                - len(self._simplices_3))

    @property
    def betti_0(self) -> int:
        """β₀ = number of connected components (= π₀ rank)."""
        return self._cat.connected_components()

    @property
    def betti_1(self) -> int:
        """β₁ = rank of H₁ = cycle rank of the graph.

        From algebraic topology: β₁ = |edges| - |vertices| + components.
        """
        return self._cat.cycle_rank()

    @property
    def dimension(self) -> int:
        """Maximum dimension of any simplex present."""
        if self._simplices_3:
            return 3
        if self._simplices_2:
            return 2
        if self._simplices_1:
            return 1
        if self._simplices_0:
            return 0
        return -1

    # ── Face maps ──

    def face_0_of_1(self, s: Simplex1) -> Simplex0:
        """d₀: N₁ → N₀ — target of the edge."""
        return Simplex0(index=s.target)

    def face_1_of_1(self, s: Simplex1) -> Simplex0:
        """d₁: N₁ → N₀ — source of the edge."""
        return Simplex0(index=s.source)

    def faces_of_2(self, s: Simplex2) -> Tuple[Simplex1, Simplex1, Simplex1]:
        """d₀, d₁, d₂: N₂ → N₁ — faces of a triangle.

        d₀ = edge B→C (drop first vertex)
        d₁ = edge A→C (composition, virtual)
        d₂ = edge A→B (drop last vertex)
        """
        return (
            Simplex1(source=s.vertex_b, target=s.vertex_c, morphism_index=s.edge_bc),
            Simplex1(source=s.vertex_a, target=s.vertex_c, morphism_index=-1),
            Simplex1(source=s.vertex_a, target=s.vertex_b, morphism_index=s.edge_ab),
        )

    # ── Boundary operator ──

    def boundary_matrix_1(self) -> Dict[Tuple[int, int], int]:
        """∂₁: C₁ → C₀ — the boundary operator on 1-chains.

        Returns a sparse matrix {(edge_idx, vertex_idx): ±1}.
        ∂₁(e) = target(e) - source(e).
        """
        matrix: Dict[Tuple[int, int], int] = {}
        for i, s in enumerate(self._simplices_1):
            matrix[(i, s.target)] = matrix.get((i, s.target), 0) + 1
            matrix[(i, s.source)] = matrix.get((i, s.source), 0) - 1
        return matrix

    def coboundary_matrix_0(self) -> Dict[Tuple[int, int], int]:
        """δ⁰: C⁰ → C¹ — the coboundary operator on 0-cochains.

        Dual of ∂₁.  (δ⁰σ)(e) = σ(target(e)) - σ(source(e)).
        This is the operator whose kernel is H⁰.
        """
        matrix: Dict[Tuple[int, int], int] = {}
        for i, s in enumerate(self._simplices_1):
            matrix[(i, s.target)] = matrix.get((i, s.target), 0) + 1
            matrix[(i, s.source)] = matrix.get((i, s.source), 0) - 1
        return matrix
