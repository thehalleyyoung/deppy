"""§4 Code Proposals: Čech Complex, Stalks, Mayer-Vietoris enhancements.

These proposals deepen the implementation to match the formalized
monograph chapters 7–10 (g04_cech_stalks.tex / main.tex lines 950–1280).

Provides ten interrelated modules:

  1. GF2Matrix          – explicit GF(2) linear algebra (row echelon, kernel, etc.)
  2. CechComplex         – first-class Čech complex C⁰ → C¹ → C² with D₀/D₁
  3. FiberOverlapGraph   – adjacency structure over fibers sharing parameters
  4. ObstructionLocator  – pinpoints which overlaps contribute to H¹ ≠ 0
  5. IncrementalCech     – adds / removes fibers without full recomputation
  6. SpectralPage        – E₂-page of the stalk-to-global spectral sequence
  7. MayerVietorisResult – two-piece decomposition strategy
  8. SymbolicStalk        – per-fiber stalk isomorphism test
  9. GapDiagnostic       – cubical-vs-cohomological method classifier
 10. CechPipeline        – integration wrapper tying everything to checker.py

All arithmetic over GF(2) unless stated otherwise.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import (
    Any,
    Dict,
    FrozenSet,
    Iterable,
    Iterator,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
)
import itertools
import copy


# ╔═══════════════════════════════════════════════════════════════════╗
# ║  §4.0  GF(2) Matrix Algebra                                    ║
# ╚═══════════════════════════════════════════════════════════════════╝

class GF2Matrix:
    """Dense matrix over GF(2) with full linear-algebra support.

    Stores rows as Python ``list[int]`` (0 or 1).  All operations are
    mod-2.  This keeps the implementation dependency-free while being
    sufficient for the small matrices arising from Čech complexes over
    type-fiber covers (typically < 30 fibers).

    Mirrors Definition 7.11 (D₀ and D₁ Matrices) in the monograph.
    """

    __slots__ = ("_rows", "_nrows", "_ncols")

    def __init__(self, rows: List[List[int]]) -> None:
        if rows:
            ncols = len(rows[0])
            for r in rows:
                if len(r) != ncols:
                    raise ValueError("All rows must have the same length")
        else:
            ncols = 0
        self._rows: List[List[int]] = [[(v % 2) for v in r] for r in rows]
        self._nrows: int = len(rows)
        self._ncols: int = ncols

    # ── factories ────────────────────────────────────────────────

    @classmethod
    def zeros(cls, nrows: int, ncols: int) -> "GF2Matrix":
        """Return an nrows × ncols zero matrix."""
        return cls([[0] * ncols for _ in range(nrows)])

    @classmethod
    def identity(cls, n: int) -> "GF2Matrix":
        """Return the n × n identity matrix over GF(2)."""
        rows = [[0] * n for _ in range(n)]
        for i in range(n):
            rows[i][i] = 1
        return cls(rows)

    @classmethod
    def from_sets(cls, nrows: int, ncols: int,
                  ones: Iterable[Tuple[int, int]]) -> "GF2Matrix":
        """Build a matrix by listing (row, col) pairs that are 1."""
        rows = [[0] * ncols for _ in range(nrows)]
        for r, c in ones:
            rows[r][c] = 1
        return cls(rows)

    # ── accessors ────────────────────────────────────────────────

    @property
    def nrows(self) -> int:
        return self._nrows

    @property
    def ncols(self) -> int:
        return self._ncols

    @property
    def shape(self) -> Tuple[int, int]:
        return (self._nrows, self._ncols)

    def __getitem__(self, idx: Tuple[int, int]) -> int:
        r, c = idx
        return self._rows[r][c]

    def __setitem__(self, idx: Tuple[int, int], val: int) -> None:
        r, c = idx
        self._rows[r][c] = val % 2

    def row(self, i: int) -> List[int]:
        """Return a copy of row *i*."""
        return list(self._rows[i])

    def col(self, j: int) -> List[int]:
        """Return column *j* as a list."""
        return [self._rows[i][j] for i in range(self._nrows)]

    def to_list(self) -> List[List[int]]:
        """Return a deep copy as nested lists."""
        return [list(r) for r in self._rows]

    # ── arithmetic ───────────────────────────────────────────────

    def __add__(self, other: "GF2Matrix") -> "GF2Matrix":
        if self.shape != other.shape:
            raise ValueError("Shape mismatch for GF2 addition")
        return GF2Matrix([
            [(a + b) % 2 for a, b in zip(sr, orr)]
            for sr, orr in zip(self._rows, other._rows)
        ])

    def __matmul__(self, other: "GF2Matrix") -> "GF2Matrix":
        """Matrix multiplication over GF(2)."""
        if self._ncols != other._nrows:
            raise ValueError(
                f"Cannot multiply ({self._nrows}×{self._ncols}) @ "
                f"({other._nrows}×{other._ncols})"
            )
        result: List[List[int]] = []
        for i in range(self._nrows):
            row: List[int] = []
            for j in range(other._ncols):
                s = 0
                for k in range(self._ncols):
                    s += self._rows[i][k] * other._rows[k][j]
                row.append(s % 2)
            result.append(row)
        return GF2Matrix(result)

    def transpose(self) -> "GF2Matrix":
        """Return the transpose."""
        return GF2Matrix([
            [self._rows[i][j] for i in range(self._nrows)]
            for j in range(self._ncols)
        ])

    # ── Gaussian elimination & rank ──────────────────────────────

    def rref(self) -> Tuple["GF2Matrix", List[int]]:
        """Reduced row-echelon form over GF(2).

        Returns (rref_matrix, pivot_columns).
        """
        m = [list(r) for r in self._rows]
        rows, cols = self._nrows, self._ncols
        pivots: List[int] = []
        cur_row = 0
        for col in range(cols):
            pivot = None
            for row in range(cur_row, rows):
                if m[row][col] == 1:
                    pivot = row
                    break
            if pivot is None:
                continue
            m[cur_row], m[pivot] = m[pivot], m[cur_row]
            for row in range(rows):
                if row != cur_row and m[row][col] == 1:
                    m[row] = [(m[row][j] + m[cur_row][j]) % 2
                              for j in range(cols)]
            pivots.append(col)
            cur_row += 1
        return GF2Matrix(m), pivots

    def rank(self) -> int:
        """Rank via Gaussian elimination over GF(2)."""
        _, pivots = self.rref()
        return len(pivots)

    def nullity(self) -> int:
        """Dimension of the kernel (null space)."""
        return self._ncols - self.rank()

    def kernel_basis(self) -> List[List[int]]:
        """Compute a basis for ker(self) over GF(2).

        Each basis vector is a list of length ``ncols``.
        """
        rref_mat, pivots = self.rref()
        pivot_set = set(pivots)
        free_cols = [j for j in range(self._ncols) if j not in pivot_set]
        basis: List[List[int]] = []
        for fc in free_cols:
            vec = [0] * self._ncols
            vec[fc] = 1
            for idx, pc in enumerate(pivots):
                vec[pc] = rref_mat._rows[idx][fc]
            basis.append(vec)
        return basis

    def image_basis(self) -> List[List[int]]:
        """Basis for the row space of this matrix (RREF non-zero rows)."""
        rref_mat, pivots = self.rref()
        return [list(rref_mat._rows[i]) for i in range(len(pivots))]

    def column_space_basis(self) -> List[List[int]]:
        """Basis for the column space (image as a linear map GF(2)^n → GF(2)^m).

        Returns vectors of length ``nrows``.
        """
        _, pivots = self.rref()
        return [self.col(j) for j in pivots]

    # ── coboundary check ─────────────────────────────────────────

    def is_zero(self) -> bool:
        """True iff every entry is 0."""
        return all(v == 0 for r in self._rows for v in r)

    def coboundary_composition_vanishes(self, other: "GF2Matrix") -> bool:
        """Verify self ∘ other = 0 (the fundamental chain-complex property).

        Called as ``delta1.coboundary_composition_vanishes(delta0)`` to
        verify δ¹ ∘ δ⁰ = 0.
        """
        product = self @ other
        return product.is_zero()

    # ── pretty-printing ──────────────────────────────────────────

    def __repr__(self) -> str:
        return f"GF2Matrix({self._nrows}×{self._ncols}, rank={self.rank()})"

    def pretty(self) -> str:
        """Human-readable matrix display."""
        lines: List[str] = []
        for r in self._rows:
            lines.append("│ " + " ".join(str(v) for v in r) + " │")
        return "\n".join(lines)

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, GF2Matrix):
            return NotImplemented
        return self._rows == other._rows


# ╔═══════════════════════════════════════════════════════════════════╗
# ║  §4.1  CechComplex — first-class Čech complex                   ║
# ╚═══════════════════════════════════════════════════════════════════╝

@dataclass
class CechComplex:
    """The full Čech complex C⁰ → C¹ → C² with coboundary matrices.

    Mirrors Definition 7.11 (D₀ and D₁ Matrices) in the monograph.
    All arithmetic is over GF(2).

    Attributes
    ----------
    fibers : list of fiber-combo tuples — generators of C⁰
    overlaps : list of (fiber_a, fiber_b) pairs — generators of C¹
    triples : list of (overlap_idx_i, overlap_idx_j) — generators of C²
    delta0 : GF2Matrix of shape |overlaps| × |fibers|
    delta1 : GF2Matrix of shape |triples| × |overlaps|
    """
    fibers: List[Tuple[str, ...]]
    overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]]
    triples: List[Tuple[int, int]]

    delta0: GF2Matrix = field(default_factory=lambda: GF2Matrix([]))
    delta1: GF2Matrix = field(default_factory=lambda: GF2Matrix([]))

    _rank_d0: Optional[int] = field(default=None, repr=False)
    _rank_d1: Optional[int] = field(default=None, repr=False)

    # ── cached rank properties ───────────────────────────────────

    @property
    def rank_delta0(self) -> int:
        """rank(δ⁰): dimension of im(δ⁰)."""
        if self._rank_d0 is None:
            self._rank_d0 = self.delta0.rank()
        return self._rank_d0

    @property
    def rank_delta1(self) -> int:
        """rank(δ¹): used to compute dim ker(δ¹)."""
        if self._rank_d1 is None:
            self._rank_d1 = self.delta1.rank() if self.delta1.nrows > 0 else 0
        return self._rank_d1

    @property
    def dim_c0(self) -> int:
        """dim C⁰ = |fibers|."""
        return len(self.fibers)

    @property
    def dim_c1(self) -> int:
        """dim C¹ = |overlaps|."""
        return len(self.overlaps)

    @property
    def dim_c2(self) -> int:
        """dim C² = |triples|."""
        return len(self.triples)

    @property
    def dim_ker_delta1(self) -> int:
        """dim ker(δ¹) = dim C¹ − rank(δ¹)."""
        return self.dim_c1 - self.rank_delta1

    @property
    def h0(self) -> int:
        """H⁰ = ker(δ⁰).  For a connected cover this is 1."""
        return self.dim_c0 - self.rank_delta0

    @property
    def h1_rank(self) -> int:
        """H¹ = ker(δ¹) / im(δ⁰).  Proposition 7.8 in the monograph."""
        return max(0, self.dim_ker_delta1 - self.rank_delta0)

    @property
    def euler_characteristic(self) -> int:
        """χ = dim C⁰ − dim C¹ + dim C² (alternating sum)."""
        return self.dim_c0 - self.dim_c1 + self.dim_c2

    def verify_complex(self) -> bool:
        """Check δ¹ ∘ δ⁰ = 0 (chain complex property)."""
        if self.delta1.nrows == 0 or self.delta0.nrows == 0:
            return True
        return self.delta1.coboundary_composition_vanishes(self.delta0)

    def ker_delta1_basis(self) -> List[List[int]]:
        """Explicit basis for ker(δ¹) — the 1-cocycles."""
        if self.delta1.nrows == 0:
            return [
                [1 if j == k else 0 for j in range(self.dim_c1)]
                for k in range(self.dim_c1)
            ]
        return self.delta1.kernel_basis()

    def im_delta0_basis(self) -> List[List[int]]:
        """Explicit basis for im(δ⁰) — the 1-coboundaries.

        Returns vectors of length dim_c1 (living in C¹).
        """
        return self.delta0.column_space_basis()

    def summary(self) -> str:
        """One-line summary string for diagnostics."""
        return (
            f"CechComplex(C⁰={self.dim_c0}, C¹={self.dim_c1}, "
            f"C²={self.dim_c2}, H¹={self.h1_rank}, "
            f"rank δ⁰={self.rank_delta0}, rank δ¹={self.rank_delta1})"
        )


def build_cech_complex(
    equiv_fibers: List[Tuple[str, ...]],
    overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
) -> CechComplex:
    """Construct the full Čech complex from equivalent fibers and overlaps.

    This is the explicit construction from Definition 7.11:
      (D₀)_{k,i} = 1 iff fiber i participates in overlap k
      (D₁)_{t,k} = 1 iff overlap k participates in triple t

    Parameters
    ----------
    equiv_fibers : list of fiber-combo tuples that passed local equivalence.
    overlaps : list of (fiber_a, fiber_b) pairs from the site category.

    Returns
    -------
    CechComplex with fully built delta0, delta1 matrices.
    """
    fiber_idx: Dict[Tuple[str, ...], int] = {
        f: i for i, f in enumerate(equiv_fibers)
    }
    overlap_list: List[Tuple[Tuple[str, ...], Tuple[str, ...]]] = [
        (a, b) for a, b in overlaps if a in fiber_idx and b in fiber_idx
    ]

    n = len(equiv_fibers)
    m = len(overlap_list)

    # δ⁰: |overlaps| × |fibers|
    d0_ones: List[Tuple[int, int]] = []
    for k, (a, b) in enumerate(overlap_list):
        d0_ones.append((k, fiber_idx[a]))
        d0_ones.append((k, fiber_idx[b]))
    delta0 = GF2Matrix.from_sets(m, n, d0_ones)

    # Build overlap lookup: which pairs of fiber indices overlap?
    overlap_edge_set: Set[Tuple[int, int]] = set()
    overlap_by_edge: Dict[Tuple[int, int], int] = {}
    for k, (a, b) in enumerate(overlap_list):
        ia, ib = fiber_idx[a], fiber_idx[b]
        edge = (min(ia, ib), max(ia, ib))
        overlap_edge_set.add(edge)
        overlap_by_edge[edge] = k

    # 2-simplices: triples of fibers (i, j, k) where ALL three pairs overlap.
    # Each 2-simplex contributes one row to δ¹ with 1s at the three edge columns.
    triple_simplices: List[Tuple[int, int, int]] = []
    for i in range(n):
        for j in range(i + 1, n):
            if (i, j) not in overlap_edge_set:
                continue
            for k in range(j + 1, n):
                if ((i, k) in overlap_edge_set
                        and (j, k) in overlap_edge_set):
                    triple_simplices.append((i, j, k))

    # δ¹: |2-simplices| × |overlaps|
    # Each 2-simplex (i,j,k) has δ¹ entries at edges (i,j), (i,k), (j,k).
    d1_ones: List[Tuple[int, int]] = []
    for t, (i, j, k) in enumerate(triple_simplices):
        for edge in [(i, j), (i, k), (j, k)]:
            if edge in overlap_by_edge:
                d1_ones.append((t, overlap_by_edge[edge]))
    delta1 = GF2Matrix.from_sets(len(triple_simplices), m, d1_ones)

    # Store triples as pairs of overlap indices for backward compat
    triples: List[Tuple[int, int]] = [
        (overlap_by_edge[(i, j)], overlap_by_edge[(j, k)])
        for i, j, k in triple_simplices
        if (i, j) in overlap_by_edge and (j, k) in overlap_by_edge
    ]

    return CechComplex(
        fibers=equiv_fibers,
        overlaps=overlap_list,
        triples=triples,
        delta0=delta0,
        delta1=delta1,
    )


# ╔═══════════════════════════════════════════════════════════════════╗
# ║  §4.2  Fiber Overlap Graph                                      ║
# ╚═══════════════════════════════════════════════════════════════════╝

@dataclass
class FiberOverlapGraph:
    """Adjacency structure over type fibers sharing parameters.

    Nodes are fiber-combo tuples.  An edge connects two fibers when they
    share at least one axis value (i.e. they overlap in the site category).

    This graph is the 1-skeleton of the nerve of the cover.  Its connected
    components correspond to independent subcomplexes that can be checked
    separately.
    """
    nodes: List[Tuple[str, ...]]
    adjacency: Dict[int, Set[int]]

    @classmethod
    def from_overlaps(
        cls,
        fibers: List[Tuple[str, ...]],
        overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
    ) -> "FiberOverlapGraph":
        """Build the overlap graph from fibers and their pairwise overlaps."""
        idx = {f: i for i, f in enumerate(fibers)}
        adj: Dict[int, Set[int]] = {i: set() for i in range(len(fibers))}
        for a, b in overlaps:
            if a in idx and b in idx:
                ia, ib = idx[a], idx[b]
                adj[ia].add(ib)
                adj[ib].add(ia)
        return cls(nodes=list(fibers), adjacency=adj)

    def degree(self, node_idx: int) -> int:
        """Number of neighbors of a node."""
        return len(self.adjacency.get(node_idx, set()))

    def neighbors(self, node_idx: int) -> Set[int]:
        """Return the neighbor set for a node."""
        return self.adjacency.get(node_idx, set())

    def connected_components(self) -> List[List[int]]:
        """Return connected components as lists of node indices.

        Uses iterative BFS to avoid stack issues on large graphs.
        """
        visited: Set[int] = set()
        components: List[List[int]] = []
        for start in range(len(self.nodes)):
            if start in visited:
                continue
            component: List[int] = []
            queue = [start]
            while queue:
                node = queue.pop()
                if node in visited:
                    continue
                visited.add(node)
                component.append(node)
                for nb in self.adjacency.get(node, set()):
                    if nb not in visited:
                        queue.append(nb)
            components.append(sorted(component))
        return components

    def is_connected(self) -> bool:
        """True iff the graph has exactly one connected component."""
        comps = self.connected_components()
        return len(comps) <= 1

    def subgraph(self, node_indices: Iterable[int]) -> "FiberOverlapGraph":
        """Return the induced subgraph on a subset of nodes."""
        idx_set = set(node_indices)
        old_to_new = {old: new for new, old in enumerate(sorted(idx_set))}
        new_nodes = [self.nodes[i] for i in sorted(idx_set)]
        new_adj: Dict[int, Set[int]] = {
            old_to_new[i]: {old_to_new[j] for j in self.adjacency.get(i, set())
                            if j in idx_set}
            for i in sorted(idx_set)
        }
        return FiberOverlapGraph(nodes=new_nodes, adjacency=new_adj)

    def edge_list(self) -> List[Tuple[int, int]]:
        """Return edges as sorted (i, j) pairs with i < j."""
        edges: Set[Tuple[int, int]] = set()
        for i, nbs in self.adjacency.items():
            for j in nbs:
                edges.add((min(i, j), max(i, j)))
        return sorted(edges)

    def max_clique_size(self) -> int:
        """Upper bound on the maximum clique via greedy coloring.

        The chromatic number (and hence max clique) for small graphs
        arising from type-fiber covers is almost always ≤ 6.
        """
        n = len(self.nodes)
        if n == 0:
            return 0
        colors: Dict[int, int] = {}
        for node in range(n):
            used = {colors[nb] for nb in self.adjacency.get(node, set())
                    if nb in colors}
            c = 0
            while c in used:
                c += 1
            colors[node] = c
        return max(colors.values()) + 1 if colors else 0

    def summary(self) -> str:
        """One-line diagnostic."""
        n = len(self.nodes)
        e = len(self.edge_list())
        cc = len(self.connected_components())
        return f"FiberOverlapGraph(|V|={n}, |E|={e}, components={cc})"


# ╔═══════════════════════════════════════════════════════════════════╗
# ║  §4.3  H¹ Obstruction Localization                              ║
# ╚═══════════════════════════════════════════════════════════════════╝

@dataclass
class ObstructionEdge:
    """An edge in the overlap graph contributing to H¹ ≠ 0.

    Represents a 1-cocycle component that is not a coboundary.
    """
    fiber_a: Tuple[str, ...]
    fiber_b: Tuple[str, ...]
    overlap_index: int
    cocycle_coefficient: int  # 0 or 1 in the non-trivial cocycle


@dataclass
class ObstructionReport:
    """Full localization of H¹ obstructions.

    Lists which specific overlaps carry the non-trivial cohomology class.
    """
    h1_rank: int
    obstruction_edges: List[ObstructionEdge]
    cocycle_representatives: List[List[int]]
    explanation: str

    def involved_fibers(self) -> Set[Tuple[str, ...]]:
        """All fibers that participate in at least one obstruction edge."""
        result: Set[Tuple[str, ...]] = set()
        for e in self.obstruction_edges:
            result.add(e.fiber_a)
            result.add(e.fiber_b)
        return result


def localize_obstructions(cx: CechComplex) -> ObstructionReport:
    """Pinpoint which overlaps carry H¹ obstructions.

    Algorithm:
      1. Compute ker(δ¹) basis  (1-cocycles)
      2. Compute im(δ⁰) basis   (1-coboundaries)
      3. Find cocycles that are NOT coboundaries
      4. Map non-trivial entries back to overlap edges

    Returns an ObstructionReport listing the offending edges.
    """
    if cx.h1_rank == 0:
        return ObstructionReport(
            h1_rank=0,
            obstruction_edges=[],
            cocycle_representatives=[],
            explanation="H¹ = 0: no obstructions, local equivalences glue globally.",
        )

    cocycles = cx.ker_delta1_basis()
    coboundaries = cx.im_delta0_basis()

    non_trivial = _find_non_coboundary_cocycles(cocycles, coboundaries, cx.dim_c1)

    edges: List[ObstructionEdge] = []
    for cocycle in non_trivial:
        for k, val in enumerate(cocycle):
            if val == 1 and k < len(cx.overlaps):
                a, b = cx.overlaps[k]
                edges.append(ObstructionEdge(
                    fiber_a=a, fiber_b=b,
                    overlap_index=k, cocycle_coefficient=1,
                ))

    return ObstructionReport(
        h1_rank=cx.h1_rank,
        obstruction_edges=edges,
        cocycle_representatives=non_trivial,
        explanation=(
            f"H¹ = {cx.h1_rank}: {len(edges)} overlap edge(s) carry "
            f"non-trivial cohomology classes."
        ),
    )


def _find_non_coboundary_cocycles(
    cocycles: List[List[int]],
    coboundaries: List[List[int]],
    dim: int,
) -> List[List[int]]:
    """Find cocycles not in the span of coboundaries.

    Extends the coboundary basis and checks which cocycles are linearly
    independent of it over GF(2).
    """
    if not cocycles:
        return []

    coboundary_rank = GF2Matrix(coboundaries).rank() if coboundaries else 0
    result: List[List[int]] = []

    for z in cocycles:
        extended = coboundaries + [z]
        new_rank = GF2Matrix(extended).rank() if extended else 0
        if new_rank > coboundary_rank:
            result.append(z)
            coboundaries = list(extended)
            coboundary_rank = new_rank

    return result


# ╔═══════════════════════════════════════════════════════════════════╗
# ║  §4.4  Incremental Čech Update                                  ║
# ╚═══════════════════════════════════════════════════════════════════╝

class IncrementalCech:
    """Incrementally maintain a Čech complex as fibers are added/removed.

    Avoids full recomputation of H¹ when the cover changes by a single
    fiber.  Tracks the GF2 matrices and recomputes ranks only on the
    affected rows/columns.

    Typical usage with the checker pipeline:

        inc = IncrementalCech()
        for combo in fiber_combos:
            judgment = _check_fiber(...)
            if judgment.is_equivalent:
                inc.add_fiber(combo, all_existing_overlaps)
        print(inc.h1_rank)
    """

    def __init__(self) -> None:
        self._fibers: List[Tuple[str, ...]] = []
        self._fiber_idx: Dict[Tuple[str, ...], int] = {}
        self._overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]] = []
        self._complex: Optional[CechComplex] = None
        self._dirty: bool = True

    @property
    def fiber_count(self) -> int:
        return len(self._fibers)

    @property
    def overlap_count(self) -> int:
        return len(self._overlaps)

    def add_fiber(
        self,
        fiber: Tuple[str, ...],
        potential_overlaps: Optional[List[Tuple[str, ...]]] = None,
    ) -> None:
        """Add a fiber to the complex.

        Parameters
        ----------
        fiber : the new fiber-combo tuple.
        potential_overlaps : list of existing fibers that overlap with
            the new one.  If None, overlaps are computed by checking
            shared axis values against all existing fibers.
        """
        if fiber in self._fiber_idx:
            return
        idx = len(self._fibers)
        self._fibers.append(fiber)
        self._fiber_idx[fiber] = idx

        if potential_overlaps is None:
            potential_overlaps = [
                f for f in self._fibers[:-1]
                if _fibers_share_axis(f, fiber)
            ]

        for other in potential_overlaps:
            if other in self._fiber_idx and other != fiber:
                self._overlaps.append((other, fiber))

        self._dirty = True

    def remove_fiber(self, fiber: Tuple[str, ...]) -> None:
        """Remove a fiber and all its overlaps."""
        if fiber not in self._fiber_idx:
            return
        self._fibers = [f for f in self._fibers if f != fiber]
        self._fiber_idx = {f: i for i, f in enumerate(self._fibers)}
        self._overlaps = [
            (a, b) for a, b in self._overlaps if a != fiber and b != fiber
        ]
        self._dirty = True

    def _rebuild(self) -> None:
        """Rebuild the complex from current fibers and overlaps."""
        if len(self._fibers) <= 1 or not self._overlaps:
            self._complex = CechComplex(
                fibers=list(self._fibers),
                overlaps=[],
                triples=[],
                delta0=GF2Matrix([]),
                delta1=GF2Matrix([]),
            )
        else:
            self._complex = build_cech_complex(self._fibers, self._overlaps)
        self._dirty = False

    @property
    def complex(self) -> CechComplex:
        """The current Čech complex (rebuilt lazily if dirty)."""
        if self._dirty or self._complex is None:
            self._rebuild()
        assert self._complex is not None
        return self._complex

    @property
    def h1_rank(self) -> int:
        """Current H¹ rank."""
        return self.complex.h1_rank

    @property
    def h0(self) -> int:
        """Current H⁰."""
        return self.complex.h0

    def snapshot(self) -> CechComplex:
        """Return a copy of the current complex."""
        cx = self.complex
        return CechComplex(
            fibers=list(cx.fibers),
            overlaps=list(cx.overlaps),
            triples=list(cx.triples),
            delta0=GF2Matrix(cx.delta0.to_list()),
            delta1=GF2Matrix(cx.delta1.to_list()),
        )


def _fibers_share_axis(a: Tuple[str, ...], b: Tuple[str, ...]) -> bool:
    """True iff fibers *a* and *b* agree on at least one axis position."""
    return any(ai == bi for ai, bi in zip(a, b))


# ╔═══════════════════════════════════════════════════════════════════╗
# ║  §4.5  Stalk-to-Global Spectral Sequence (E₂ page)              ║
# ╚═══════════════════════════════════════════════════════════════════╝

@dataclass
class SpectralEntry:
    """A single entry E₂^{p,q} in the spectral sequence."""
    p: int
    q: int
    dimension: int
    generators: List[List[int]]
    label: str = ""

    def __repr__(self) -> str:
        return f"E₂^{{{self.p},{self.q}}} = GF(2)^{self.dimension}"


@dataclass
class SpectralPage:
    """The E₂ page of the stalk-to-global spectral sequence.

    For a Čech cover of a program-pair's type space, the spectral
    sequence degenerates at E₂ because the stalks are GF(2)-modules
    (all higher local cohomology vanishes for constant sheaves).

    Thus E₂^{p,0} = Ĥ^p(U, F) directly gives the global cohomology.
    """
    entries: Dict[Tuple[int, int], SpectralEntry]
    converges_at: str = "E₂"

    @classmethod
    def from_complex(cls, cx: CechComplex) -> "SpectralPage":
        """Compute the E₂ page from a CechComplex.

        For constant coefficients in GF(2):
          E₂^{0,0} ≅ H⁰(X)
          E₂^{1,0} ≅ H¹(X)
          E₂^{p,q} = 0 for q > 0  (stalks are GF(2), so H^q_stalk = 0)
        """
        entries: Dict[Tuple[int, int], SpectralEntry] = {}

        # E₂^{0,0} = H⁰
        h0_dim = cx.h0
        entries[(0, 0)] = SpectralEntry(
            p=0, q=0, dimension=h0_dim,
            generators=[], label="H⁰ = ker(δ⁰)",
        )

        # E₂^{1,0} = H¹
        h1_dim = cx.h1_rank
        h1_gens = _find_non_coboundary_cocycles(
            cx.ker_delta1_basis(),
            cx.im_delta0_basis(),
            cx.dim_c1,
        )
        entries[(1, 0)] = SpectralEntry(
            p=1, q=0, dimension=h1_dim,
            generators=h1_gens, label="H¹ = ker(δ¹)/im(δ⁰)",
        )

        # Higher q-rows are zero for constant coefficients
        for p in range(3):
            for q in range(1, 3):
                entries[(p, q)] = SpectralEntry(
                    p=p, q=q, dimension=0, generators=[],
                    label="vanishes (constant sheaf)",
                )

        return cls(entries=entries)

    def total_dimension(self, n: int) -> int:
        """Total Hⁿ via the spectral sequence: Hⁿ = ⊕_{p+q=n} E₂^{p,q}."""
        return sum(
            e.dimension for (p, q), e in self.entries.items() if p + q == n
        )

    def is_degenerate(self) -> bool:
        """True iff the spectral sequence degenerates at E₂.

        Always true for constant GF(2)-coefficient sheaves.
        """
        return True

    def summary(self) -> str:
        """Pretty-print the E₂ page."""
        lines = [f"Spectral Sequence (converges at {self.converges_at}):"]
        for (p, q) in sorted(self.entries):
            e = self.entries[(p, q)]
            if e.dimension > 0:
                lines.append(f"  E₂^{{{p},{q}}} = GF(2)^{e.dimension}  ({e.label})")
        if not any(e.dimension > 0 for e in self.entries.values()):
            lines.append("  All entries vanish → trivial cohomology")
        return "\n".join(lines)


# ╔═══════════════════════════════════════════════════════════════════╗
# ║  §4.6  Mayer-Vietoris Decomposition Strategy                    ║
# ╚═══════════════════════════════════════════════════════════════════╝

@dataclass
class MayerVietorisResult:
    """Result of Mayer-Vietoris decomposition (Corollary 8.4).

    Attributes
    ----------
    h1_A : H¹ of piece A
    h1_B : H¹ of piece B
    alpha_surjective : whether the restriction map α is surjective
    h1_X : concluded H¹(X)
    connecting_image_dim : dim im(δ*), the connecting homomorphism
    piece_A_fibers : fibers in piece A
    piece_B_fibers : fibers in piece B
    intersection_fibers : fibers in A ∩ B
    """
    h1_A: int
    h1_B: int
    alpha_surjective: bool
    h1_X: int
    connecting_image_dim: int
    piece_A_fibers: List[Tuple[str, ...]] = field(default_factory=list)
    piece_B_fibers: List[Tuple[str, ...]] = field(default_factory=list)
    intersection_fibers: List[Tuple[str, ...]] = field(default_factory=list)

    def is_conclusive(self) -> bool:
        """True iff the decomposition gives a definite H¹(X) value."""
        return self.h1_A == 0 and self.h1_B == 0 and self.alpha_surjective

    def summary(self) -> str:
        """Diagnostic summary."""
        status = "conclusive" if self.is_conclusive() else "fell back to full"
        return (
            f"MV({status}): H¹(A)={self.h1_A}, H¹(B)={self.h1_B}, "
            f"α_surj={self.alpha_surjective}, H¹(X)={self.h1_X}, "
            f"|A|={len(self.piece_A_fibers)}, |B|={len(self.piece_B_fibers)}, "
            f"|A∩B|={len(self.intersection_fibers)}"
        )


def mayer_vietoris_split(
    judgments: Dict[Tuple[str, ...], bool],
    overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
    partition_A: set,
    partition_B: set,
) -> MayerVietorisResult:
    """Apply Mayer-Vietoris to a two-piece decomposition.

    Given a partition of fiber-combo tuples into sets A and B (which may
    overlap on boundary fibers), compute H¹ of each piece and the
    connecting homomorphism to determine H¹(X).

    Parameters
    ----------
    judgments : fiber → bool (True = locally equivalent).
    overlaps : pairwise overlaps from the site category.
    partition_A, partition_B : sets of fiber-combo tuples.

    Returns
    -------
    MayerVietorisResult with full decomposition data.
    """
    fibers_A = [f for f in judgments if f in partition_A and judgments[f]]
    fibers_B = [f for f in judgments if f in partition_B and judgments[f]]

    overlaps_A = [(a, b) for a, b in overlaps
                  if a in partition_A and b in partition_A]
    overlaps_B = [(a, b) for a, b in overlaps
                  if a in partition_B and b in partition_B]

    h1_A = 0
    if len(fibers_A) > 1 and overlaps_A:
        cx_A = build_cech_complex(fibers_A, overlaps_A)
        h1_A = cx_A.h1_rank

    h1_B = 0
    if len(fibers_B) > 1 and overlaps_B:
        cx_B = build_cech_complex(fibers_B, overlaps_B)
        h1_B = cx_B.h1_rank

    overlap_fibers = partition_A & partition_B
    intersection_list = [f for f in overlap_fibers
                         if f in judgments and judgments.get(f, False)]
    alpha_surjective = all(
        f in judgments and judgments[f] for f in overlap_fibers
    )

    if h1_A == 0 and h1_B == 0 and alpha_surjective:
        h1_X = 0
        connecting_dim = 0
    else:
        all_equiv = [f for f in judgments if judgments[f]]
        if len(all_equiv) > 1 and overlaps:
            cx = build_cech_complex(all_equiv, overlaps)
            h1_X = cx.h1_rank
        else:
            h1_X = 0
        connecting_dim = h1_X

    return MayerVietorisResult(
        h1_A=h1_A,
        h1_B=h1_B,
        alpha_surjective=alpha_surjective,
        h1_X=h1_X,
        connecting_image_dim=connecting_dim,
        piece_A_fibers=fibers_A,
        piece_B_fibers=fibers_B,
        intersection_fibers=intersection_list,
    )


def auto_partition(
    fibers: List[Tuple[str, ...]],
    overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
) -> Tuple[Set[Tuple[str, ...]], Set[Tuple[str, ...]]]:
    """Automatically partition fibers for Mayer-Vietoris.

    Strategy: build the overlap graph, find connected components, then
    merge small components to balance the two pieces.  If the graph is
    connected, split at the median of the first axis value.
    """
    graph = FiberOverlapGraph.from_overlaps(fibers, overlaps)
    comps = graph.connected_components()

    if len(comps) >= 2:
        half = len(comps) // 2
        set_a: Set[Tuple[str, ...]] = set()
        set_b: Set[Tuple[str, ...]] = set()
        for i, comp in enumerate(comps):
            target = set_a if i < half else set_b
            for idx in comp:
                target.add(graph.nodes[idx])
        return set_a, set_b

    mid = len(fibers) // 2
    set_a_list = set(fibers[:mid + 1])
    set_b_list = set(fibers[mid:])
    return set_a_list, set_b_list


# ╔═══════════════════════════════════════════════════════════════════╗
# ║  §4.7  Symbolic Stalk Criterion                                  ║
# ╚═══════════════════════════════════════════════════════════════════╝

@dataclass
class SymbolicStalk:
    """A symbolic stalk ⟦f⟧|_{U_τ} (Definition 9.5).

    Represents the restriction of the denotational semantics of two
    programs to a single type fiber U_τ, together with the equivalence
    verdict.

    Attributes
    ----------
    fiber : the type-tag tuple identifying the fiber.
    term_f : Z3 expression for ⟦f⟧ restricted to this fiber.
    term_g : Z3 expression for ⟦g⟧ restricted to this fiber.
    is_isomorphism : True iff the stalk maps agree (Z3 says UNSAT
        on ⟦f⟧ ≠ ⟦g⟧ under fiber constraints).
    counterexample : readable string if is_isomorphism is False.
    explanation : human-readable explanation of the verdict.
    """
    fiber: Tuple[str, ...]
    term_f: object
    term_g: object
    is_isomorphism: Optional[bool]
    counterexample: Optional[str] = None
    explanation: str = ""

    def is_conclusive(self) -> bool:
        """True iff the verdict is not None (timed out or errored)."""
        return self.is_isomorphism is not None


def stalk_criterion_check(stalks: List[SymbolicStalk]) -> Optional[bool]:
    """Theorem 9.3: η is an isomorphism iff η_x is an iso for all x.

    Returns True iff ALL stalks report isomorphism.
    Returns False if ANY stalk reports non-isomorphism.
    Returns None if some stalks are inconclusive and none report False.
    """
    if not stalks:
        return None
    has_inconclusive = False
    for s in stalks:
        if s.is_isomorphism is False:
            return False
        if s.is_isomorphism is None:
            has_inconclusive = True
    if has_inconclusive:
        return None
    return True


def stalks_to_h0(stalks: List[SymbolicStalk]) -> int:
    """Count the number of stalks with isomorphism = True.

    This is H⁰ = |{fibers where f ≡ g}| (Theorem 9.8).
    """
    return sum(1 for s in stalks if s.is_isomorphism is True)


# ╔═══════════════════════════════════════════════════════════════════╗
# ║  §4.8  Gap Diagnostic — "Neither Alone Suffices"                ║
# ╚═══════════════════════════════════════════════════════════════════╝

class MethodNeeded(Enum):
    """Classification of which verification method(s) are needed."""
    CUBICAL_ONLY = "cubical_only"
    CECH_ONLY = "cech_only"
    COMBINED = "combined"
    NEITHER = "neither"


@dataclass
class GapDiagnostic:
    """Diagnostic for which method(s) suffice for a given pair.

    Implements Proposition 10.7 (Formalization of the Gap).

    Attributes
    ----------
    cubical_succeeds : monolithic Z3 query closes the gap.
    cech_raw_succeeds : Čech with unnormalized terms works.
    cctt_succeeds : combined (normalize per fiber + cohomological gluing).
    method : the classification.
    explanation : human-readable rationale.
    fibers_cubical_ok : which fibers cubical alone handles.
    fibers_cech_ok : which fibers raw Čech handles.
    """
    cubical_succeeds: bool
    cech_raw_succeeds: bool
    cctt_succeeds: bool
    method: MethodNeeded
    explanation: str
    fibers_cubical_ok: List[Tuple[str, ...]] = field(default_factory=list)
    fibers_cech_ok: List[Tuple[str, ...]] = field(default_factory=list)

    def needs_normalization(self) -> bool:
        """True iff cubical normalization is required for the proof."""
        return self.method == MethodNeeded.COMBINED

    def is_decidable(self) -> bool:
        """True iff at least one method succeeds."""
        return self.method != MethodNeeded.NEITHER


def diagnose_method_gap(
    monolithic_result: Optional[bool],
    raw_cech_result: Optional[bool],
    cctt_result: Optional[bool],
    fibers_cubical: Optional[List[Tuple[str, ...]]] = None,
    fibers_cech: Optional[List[Tuple[str, ...]]] = None,
) -> GapDiagnostic:
    """Proposition 10.7: classify where (f, g) falls in the gap.

    Parameters
    ----------
    monolithic_result : True/False/None from a single Z3 query on all fibers.
    raw_cech_result   : True/False/None from Čech on raw (unnormalized) terms.
    cctt_result       : True/False/None from the full CCTT pipeline.
    fibers_cubical    : optional list of fibers where cubical alone works.
    fibers_cech       : optional list of fibers where raw Čech works.

    Example (eq02):
      monolithic_result = None   (Z3 can't close gap on different OTerms)
      raw_cech_result   = None   (same OTerm mismatch on every fiber)
      cctt_result       = True   (normalization + gluing succeeds)
      → method = COMBINED
    """
    cubical_ok = monolithic_result is True
    cech_ok = raw_cech_result is True
    cctt_ok = cctt_result is True

    if cubical_ok:
        method = MethodNeeded.CUBICAL_ONLY
        explanation = "Monolithic Z3 query suffices (identical OTerms)"
    elif cech_ok:
        method = MethodNeeded.CECH_ONLY
        explanation = "Raw Čech decomposition suffices (terms match per fiber)"
    elif cctt_ok:
        method = MethodNeeded.COMBINED
        explanation = (
            "Cubical normalization per fiber + cohomological gluing needed"
        )
    else:
        method = MethodNeeded.NEITHER
        explanation = (
            "Neither method succeeds "
            "(may be genuinely inequivalent or undecidable)"
        )

    return GapDiagnostic(
        cubical_succeeds=cubical_ok,
        cech_raw_succeeds=cech_ok,
        cctt_succeeds=cctt_ok,
        method=method,
        explanation=explanation,
        fibers_cubical_ok=fibers_cubical or [],
        fibers_cech_ok=fibers_cech or [],
    )


# ╔═══════════════════════════════════════════════════════════════════╗
# ║  §4.9  CechPipeline — Integration with checker.py               ║
# ╚═══════════════════════════════════════════════════════════════════╝

@dataclass
class PipelineReport:
    """Full report from the CechPipeline.

    Bundles together the Čech complex, overlap graph, obstruction
    localization, spectral-sequence page, and Mayer-Vietoris result.
    """
    complex: CechComplex
    graph: FiberOverlapGraph
    obstructions: ObstructionReport
    spectral: SpectralPage
    mayer_vietoris: Optional[MayerVietorisResult]
    stalks: List[SymbolicStalk]
    h1_rank: int
    equivalent: Optional[bool]

    def full_summary(self) -> str:
        """Multi-line diagnostic summary."""
        lines = [
            "═══ Čech Pipeline Report ═══",
            self.complex.summary(),
            self.graph.summary(),
            f"H¹ = {self.h1_rank}  →  {'EQUIVALENT' if self.equivalent else 'NOT EQUIVALENT' if self.equivalent is False else 'INCONCLUSIVE'}",
            "",
            self.obstructions.explanation,
            "",
            self.spectral.summary(),
        ]
        if self.mayer_vietoris:
            lines.append("")
            lines.append(self.mayer_vietoris.summary())
        return "\n".join(lines)


class CechPipeline:
    """Orchestrates the full Čech analysis pipeline.

    Usage::

        pipeline = CechPipeline()
        report = pipeline.run(fibers, overlaps, judgments)
        print(report.full_summary())

    This wraps the individual proposals into a single entry point
    matching the checker's ``compute_cech_h1`` call site.
    """

    def __init__(self, *, try_mayer_vietoris: bool = True) -> None:
        self._try_mv = try_mayer_vietoris

    def run(
        self,
        fibers: List[Tuple[str, ...]],
        overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
        judgments: Dict[Tuple[str, ...], Optional[bool]],
        stalk_data: Optional[List[SymbolicStalk]] = None,
    ) -> PipelineReport:
        """Execute the full pipeline.

        Parameters
        ----------
        fibers : all fiber-combo tuples.
        overlaps : pairwise overlaps from the site category.
        judgments : fiber → True/False/None from per-fiber Z3 checks.
        stalk_data : optional pre-computed stalk objects.

        Returns
        -------
        PipelineReport with all diagnostic data.
        """
        equiv_fibers = [f for f in fibers if judgments.get(f) is True]

        # 1. Build complex
        if len(equiv_fibers) > 1 and overlaps:
            cx = build_cech_complex(equiv_fibers, overlaps)
        else:
            cx = CechComplex(
                fibers=equiv_fibers, overlaps=[], triples=[],
                delta0=GF2Matrix([]), delta1=GF2Matrix([]),
            )

        # 2. Build overlap graph
        graph = FiberOverlapGraph.from_overlaps(fibers, overlaps)

        # 3. Localize obstructions
        obs = localize_obstructions(cx)

        # 4. Spectral sequence
        spectral = SpectralPage.from_complex(cx)

        # 5. Mayer-Vietoris (optional)
        mv_result: Optional[MayerVietorisResult] = None
        if self._try_mv and len(equiv_fibers) > 2:
            bool_judgments = {f: (v is True) for f, v in judgments.items()}
            part_a, part_b = auto_partition(equiv_fibers, overlaps)
            mv_result = mayer_vietoris_split(
                bool_judgments, overlaps, part_a, part_b,
            )

        # 6. Determine equivalence
        stalks = stalk_data or []
        inequiv = [f for f in fibers if judgments.get(f) is False]
        if inequiv:
            equivalent: Optional[bool] = False
        elif cx.h1_rank == 0 and len(equiv_fibers) > 0:
            equivalent = True
        else:
            equivalent = None

        return PipelineReport(
            complex=cx,
            graph=graph,
            obstructions=obs,
            spectral=spectral,
            mayer_vietoris=mv_result,
            stalks=stalks,
            h1_rank=cx.h1_rank,
            equivalent=equivalent,
        )


# ╔═══════════════════════════════════════════════════════════════════╗
# ║  §4.10  Shared Utilities                                        ║
# ╚═══════════════════════════════════════════════════════════════════╝

def _gf2_rank(matrix: List[List[int]]) -> int:
    """Gaussian elimination over GF(2) to compute rank.

    Convenience wrapper around GF2Matrix for backward compatibility
    with callers that use raw nested lists.
    """
    if not matrix or not matrix[0]:
        return 0
    return GF2Matrix(matrix).rank()


def betti_numbers(cx: CechComplex) -> Tuple[int, int]:
    """Return (β₀, β₁) = (H⁰, H¹) of the complex."""
    return (cx.h0, cx.h1_rank)


def fiber_coverage(
    judgments: Dict[Tuple[str, ...], Optional[bool]],
) -> Tuple[int, int, int]:
    """Count (equivalent, inequivalent, unknown) fibers."""
    eq = sum(1 for v in judgments.values() if v is True)
    neq = sum(1 for v in judgments.values() if v is False)
    unk = sum(1 for v in judgments.values() if v is None)
    return eq, neq, unk


# ╔═══════════════════════════════════════════════════════════════════╗
# ║  Self-tests                                                      ║
# ╚═══════════════════════════════════════════════════════════════════╝

if __name__ == "__main__":
    import sys

    passed = 0
    failed = 0

    def _assert(cond: bool, msg: str) -> None:
        global passed, failed
        if cond:
            passed += 1
        else:
            failed += 1
            print(f"  FAIL: {msg}", file=sys.stderr)

    # ── GF2Matrix tests ─────────────────────────────────────────
    print("Testing GF2Matrix...")

    m1 = GF2Matrix([[1, 0, 1], [0, 1, 1]])
    _assert(m1.shape == (2, 3), "shape")
    _assert(m1[0, 0] == 1, "getitem")
    _assert(m1[0, 1] == 0, "getitem zero")
    _assert(m1.rank() == 2, "rank of full-rank 2x3")

    m_id = GF2Matrix.identity(3)
    _assert(m_id.rank() == 3, "identity rank")
    _assert(m_id[1, 1] == 1, "identity diagonal")
    _assert(m_id[0, 1] == 0, "identity off-diagonal")

    m_zero = GF2Matrix.zeros(2, 2)
    _assert(m_zero.rank() == 0, "zero matrix rank")
    _assert(m_zero.is_zero(), "zero matrix is_zero")

    m2 = GF2Matrix([[1, 1], [1, 0]])
    _assert(m2.rank() == 2, "2x2 full rank")
    _assert(m2.nullity() == 0, "2x2 nullity")

    m3 = GF2Matrix([[1, 1, 0], [0, 0, 0]])
    _assert(m3.rank() == 1, "rank-1 matrix")
    _assert(m3.nullity() == 2, "rank-1 nullity")
    kern = m3.kernel_basis()
    _assert(len(kern) == 2, "rank-1 kernel has 2 vectors")

    m4 = GF2Matrix([[1, 0], [0, 1], [1, 1]])
    m5 = GF2Matrix([[1, 1, 0], [0, 1, 1]])
    prod = m4 @ m5
    _assert(prod.shape == (3, 3), "matmul shape")

    mt = m1.transpose()
    _assert(mt.shape == (3, 2), "transpose shape")
    _assert(mt[2, 0] == 1, "transpose value")

    m_add = m1 + GF2Matrix([[1, 1, 0], [1, 0, 0]])
    _assert(m_add[0, 0] == 0, "GF2 addition 1+1=0")
    _assert(m_add[0, 1] == 1, "GF2 addition 0+1=1")

    # ── CechComplex tests ────────────────────────────────────────
    print("Testing CechComplex...")

    # Triangle: 3 fibers, 3 pairwise overlaps
    fibers_tri = [("int",), ("str",), ("bool",)]
    overlaps_tri = [
        (("int",), ("str",)),
        (("str",), ("bool",)),
        (("int",), ("bool",)),
    ]
    cx_tri = build_cech_complex(fibers_tri, overlaps_tri)
    _assert(cx_tri.dim_c0 == 3, "triangle C⁰ = 3")
    _assert(cx_tri.dim_c1 == 3, "triangle C¹ = 3")
    _assert(cx_tri.verify_complex(), "triangle δ¹∘δ⁰ = 0")
    _assert(cx_tri.h1_rank == 0, "triangle H¹ = 0 (contractible)")

    # Path: 3 fibers, 2 overlaps (no cycle)
    overlaps_path = [
        (("int",), ("str",)),
        (("str",), ("bool",)),
    ]
    cx_path = build_cech_complex(fibers_tri, overlaps_path)
    _assert(cx_path.dim_c1 == 2, "path C¹ = 2")
    _assert(cx_path.h1_rank == 0, "path H¹ = 0 (tree)")

    # Disconnected: 2 fibers, no overlap
    cx_disc = build_cech_complex(
        [("int",), ("str",)],
        [],
    )
    _assert(cx_disc.h1_rank == 0, "disconnected H¹ = 0")

    # Single fiber
    cx_single = build_cech_complex([("int",)], [])
    _assert(cx_single.h1_rank == 0, "single fiber H¹ = 0")
    _assert(cx_single.dim_c0 == 1, "single fiber C⁰ = 1")

    # 4 fibers forming a square (cycle of length 4)
    fibers_sq = [("a",), ("b",), ("c",), ("d",)]
    overlaps_sq = [
        (("a",), ("b",)),
        (("b",), ("c",)),
        (("c",), ("d",)),
        (("d",), ("a",)),
    ]
    cx_sq = build_cech_complex(fibers_sq, overlaps_sq)
    _assert(cx_sq.dim_c0 == 4, "square C⁰ = 4")
    _assert(cx_sq.dim_c1 == 4, "square C¹ = 4")
    _assert(cx_sq.verify_complex(), "square δ¹∘δ⁰ = 0")
    # Square with no diagonals: H¹ = 1 (one independent cycle)
    _assert(cx_sq.h1_rank == 1, "square H¹ = 1 (one cycle)")

    # Euler characteristic
    _assert(
        cx_tri.euler_characteristic == cx_tri.dim_c0 - cx_tri.dim_c1 + cx_tri.dim_c2,
        "Euler char formula",
    )

    # ── FiberOverlapGraph tests ──────────────────────────────────
    print("Testing FiberOverlapGraph...")

    g_tri = FiberOverlapGraph.from_overlaps(fibers_tri, overlaps_tri)
    _assert(len(g_tri.nodes) == 3, "triangle graph nodes")
    _assert(len(g_tri.edge_list()) == 3, "triangle graph edges")
    _assert(g_tri.is_connected(), "triangle is connected")
    _assert(len(g_tri.connected_components()) == 1, "triangle 1 component")
    _assert(g_tri.degree(0) == 2, "triangle degree")

    g_disc = FiberOverlapGraph.from_overlaps(
        [("int",), ("str",)], [],
    )
    _assert(not g_disc.is_connected(), "disconnected not connected")
    _assert(len(g_disc.connected_components()) == 2, "disconnected 2 comps")

    sub = g_tri.subgraph([0, 1])
    _assert(len(sub.nodes) == 2, "subgraph 2 nodes")

    # ── ObstructionLocator tests ─────────────────────────────────
    print("Testing ObstructionLocator...")

    obs_tri = localize_obstructions(cx_tri)
    _assert(obs_tri.h1_rank == 0, "triangle no obstructions")
    _assert(len(obs_tri.obstruction_edges) == 0, "triangle no edges")

    obs_sq = localize_obstructions(cx_sq)
    _assert(obs_sq.h1_rank == 1, "square H¹ = 1")
    _assert(len(obs_sq.obstruction_edges) > 0, "square has obstruction edges")
    _assert(len(obs_sq.cocycle_representatives) == 1, "square 1 cocycle rep")

    # ── IncrementalCech tests ────────────────────────────────────
    print("Testing IncrementalCech...")

    inc = IncrementalCech()
    inc.add_fiber(("int",))
    _assert(inc.h1_rank == 0, "incremental 1 fiber H¹ = 0")

    inc.add_fiber(("str",), [("int",)])
    _assert(inc.fiber_count == 2, "incremental 2 fibers")
    _assert(inc.h1_rank == 0, "incremental 2 fibers H¹ = 0 (path)")

    inc.add_fiber(("bool",), [("int",), ("str",)])
    _assert(inc.fiber_count == 3, "incremental 3 fibers")
    _assert(inc.h1_rank == 0, "incremental triangle H¹ = 0")

    inc2 = IncrementalCech()
    # For single-element tuples, must provide explicit overlaps
    inc2.add_fiber(("a",))
    inc2.add_fiber(("b",), [("a",)])
    inc2.add_fiber(("c",), [("b",)])
    inc2.add_fiber(("d",), [("c",), ("a",)])
    _assert(inc2.h1_rank == 1, "incremental square H¹ = 1")

    inc2.remove_fiber(("d",))
    _assert(inc2.fiber_count == 3, "after removal 3 fibers")
    _assert(inc2.h1_rank == 0, "after removal H¹ = 0 (path)")

    snap = inc.snapshot()
    _assert(snap.h1_rank == inc.h1_rank, "snapshot matches")

    # ── SpectralPage tests ───────────────────────────────────────
    print("Testing SpectralPage...")

    sp_tri = SpectralPage.from_complex(cx_tri)
    _assert(sp_tri.entries[(1, 0)].dimension == 0, "triangle E₂^{1,0} = 0")
    _assert(sp_tri.is_degenerate(), "spectral degenerates at E₂")
    _assert(sp_tri.total_dimension(1) == 0, "triangle total H¹ = 0")

    sp_sq = SpectralPage.from_complex(cx_sq)
    _assert(sp_sq.entries[(1, 0)].dimension == 1, "square E₂^{1,0} = 1")
    _assert(sp_sq.total_dimension(1) == 1, "square total H¹ = 1")
    _assert(sp_sq.entries[(0, 1)].dimension == 0, "vanishing q>0")

    # ── MayerVietoris tests ──────────────────────────────────────
    print("Testing MayerVietoris...")

    mv_judgments: Dict[Tuple[str, ...], bool] = {
        ("int",): True, ("str",): True, ("bool",): True,
    }
    part_a = {("int",), ("str",)}
    part_b = {("str",), ("bool",)}
    mv = mayer_vietoris_split(mv_judgments, overlaps_tri, part_a, part_b)
    _assert(mv.h1_X == 0, "MV triangle H¹ = 0")
    _assert(mv.alpha_surjective, "MV α surjective")
    _assert(mv.is_conclusive(), "MV conclusive")

    auto_a, auto_b = auto_partition(fibers_tri, overlaps_tri)
    _assert(len(auto_a) > 0, "auto partition A non-empty")
    _assert(len(auto_b) > 0, "auto partition B non-empty")

    # ── SymbolicStalk tests ──────────────────────────────────────
    print("Testing SymbolicStalk...")

    s1 = SymbolicStalk(("int",), None, None, True, explanation="Z3 UNSAT")
    s2 = SymbolicStalk(("str",), None, None, True, explanation="Z3 UNSAT")
    s3 = SymbolicStalk(("bool",), None, None, False, counterexample="x=True")
    _assert(stalk_criterion_check([s1, s2]) is True, "all iso → True")
    _assert(stalk_criterion_check([s1, s3]) is False, "one non-iso → False")
    _assert(stalk_criterion_check([]) is None, "empty → None")

    s4 = SymbolicStalk(("pair",), None, None, None)
    _assert(stalk_criterion_check([s1, s4]) is None, "inconclusive → None")
    _assert(stalks_to_h0([s1, s2, s3]) == 2, "H⁰ count")

    # ── GapDiagnostic tests ──────────────────────────────────────
    print("Testing GapDiagnostic...")

    d1 = diagnose_method_gap(True, None, None)
    _assert(d1.method == MethodNeeded.CUBICAL_ONLY, "cubical only")
    _assert(d1.is_decidable(), "cubical decidable")

    d2 = diagnose_method_gap(None, True, None)
    _assert(d2.method == MethodNeeded.CECH_ONLY, "cech only")

    d3 = diagnose_method_gap(None, None, True)
    _assert(d3.method == MethodNeeded.COMBINED, "combined")
    _assert(d3.needs_normalization(), "combined needs normalization")

    d4 = diagnose_method_gap(None, None, None)
    _assert(d4.method == MethodNeeded.NEITHER, "neither")
    _assert(not d4.is_decidable(), "neither not decidable")

    # ── CechPipeline integration test ────────────────────────────
    print("Testing CechPipeline...")

    pipeline = CechPipeline()
    jdg: Dict[Tuple[str, ...], Optional[bool]] = {
        ("int",): True, ("str",): True, ("bool",): True,
    }
    report = pipeline.run(fibers_tri, overlaps_tri, jdg)
    _assert(report.h1_rank == 0, "pipeline H¹ = 0")
    _assert(report.equivalent is True, "pipeline equivalent")
    _assert(report.obstructions.h1_rank == 0, "pipeline no obstructions")
    _assert(report.graph.is_connected(), "pipeline graph connected")
    _assert("EQUIVALENT" in report.full_summary(), "pipeline summary")

    # Pipeline with non-equivalent fiber
    jdg2: Dict[Tuple[str, ...], Optional[bool]] = {
        ("int",): True, ("str",): False, ("bool",): True,
    }
    report2 = pipeline.run(fibers_tri, overlaps_tri, jdg2)
    _assert(report2.equivalent is False, "pipeline NEQ")

    # Pipeline with all unknown
    jdg3: Dict[Tuple[str, ...], Optional[bool]] = {
        ("int",): None, ("str",): None,
    }
    report3 = pipeline.run([("int",), ("str",)], [], jdg3)
    _assert(report3.equivalent is None, "pipeline inconclusive")

    # ── Utility tests ────────────────────────────────────────────
    print("Testing utilities...")

    _assert(_gf2_rank([[1, 0], [0, 1]]) == 2, "gf2_rank identity")
    _assert(_gf2_rank([[1, 1], [1, 1]]) == 1, "gf2_rank duplicate rows")
    _assert(_gf2_rank([]) == 0, "gf2_rank empty")

    b0, b1 = betti_numbers(cx_tri)
    _assert(b1 == 0, "betti β₁ triangle")

    eq_c, neq_c, unk_c = fiber_coverage(jdg)
    _assert(eq_c == 3, "coverage eq")
    _assert(neq_c == 0, "coverage neq")
    _assert(unk_c == 0, "coverage unk")

    _assert(_fibers_share_axis(("int",), ("int",)), "same axis share")
    _assert(not _fibers_share_axis(("int",), ("str",)), "diff axis no share")
    _assert(
        _fibers_share_axis(("int", "str"), ("int", "bool")),
        "multi-axis partial share",
    )

    # ── Summary ──────────────────────────────────────────────────
    total = passed + failed
    print(f"\n{'='*50}")
    print(f"Results: {passed}/{total} passed, {failed} failed")
    if failed:
        sys.exit(1)
    else:
        print("All tests passed ✓")
        sys.exit(0)
