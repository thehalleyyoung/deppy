"""§4 Stalk computations: GF(2) algebra, first-class Čech complex,
overlap graph, obstruction localization, incremental updates,
spectral sequence, Mayer-Vietoris, symbolic stalks, and gap diagnostic.

Implements proposals from g04_cech_stalks that deepen the Čech engine
beyond the basic H¹ computation in cohomology.py.  All arithmetic
over GF(2) unless stated otherwise.
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


# ╔═══════════════════════════════════════════════════════════════════╗
# ║  §4.0  GF(2) Matrix Algebra                                    ║
# ╚═══════════════════════════════════════════════════════════════════╝

class GF2Matrix:
    """Dense matrix over GF(2) with full linear-algebra support.

    Stores rows as ``list[int]`` (0 or 1).  All operations are mod-2.
    Sufficient for the small matrices arising from Čech complexes over
    type-fiber covers (typically < 30 fibers).
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
        return cls([[0] * ncols for _ in range(nrows)])

    @classmethod
    def identity(cls, n: int) -> "GF2Matrix":
        rows = [[0] * n for _ in range(n)]
        for i in range(n):
            rows[i][i] = 1
        return cls(rows)

    @classmethod
    def from_sets(cls, nrows: int, ncols: int,
                  ones: Iterable[Tuple[int, int]]) -> "GF2Matrix":
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
        return list(self._rows[i])

    def col(self, j: int) -> List[int]:
        return [self._rows[i][j] for i in range(self._nrows)]

    def to_list(self) -> List[List[int]]:
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
        return GF2Matrix([
            [self._rows[i][j] for i in range(self._nrows)]
            for j in range(self._ncols)
        ])

    # ── Gaussian elimination & rank ──────────────────────────────

    def rref(self) -> Tuple["GF2Matrix", List[int]]:
        """Reduced row-echelon form over GF(2).  Returns (rref, pivots)."""
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
        _, pivots = self.rref()
        return len(pivots)

    def nullity(self) -> int:
        return self._ncols - self.rank()

    def kernel_basis(self) -> List[List[int]]:
        """Basis for ker(self) over GF(2)."""
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
        rref_mat, pivots = self.rref()
        return [list(rref_mat._rows[i]) for i in range(len(pivots))]

    def column_space_basis(self) -> List[List[int]]:
        """Basis for the column space (image as linear map)."""
        _, pivots = self.rref()
        return [self.col(j) for j in pivots]

    # ── coboundary check ─────────────────────────────────────────

    def is_zero(self) -> bool:
        return all(v == 0 for r in self._rows for v in r)

    def coboundary_composition_vanishes(self, other: "GF2Matrix") -> bool:
        """Verify self ∘ other = 0 (chain complex property)."""
        return (self @ other).is_zero()

    # ── dunder ───────────────────────────────────────────────────

    def __repr__(self) -> str:
        return f"GF2Matrix({self._nrows}×{self._ncols}, rank={self.rank()})"

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, GF2Matrix):
            return NotImplemented
        return self._rows == other._rows

    def pretty(self) -> str:
        lines: List[str] = []
        for r in self._rows:
            lines.append("│ " + " ".join(str(v) for v in r) + " │")
        return "\n".join(lines)


# ╔═══════════════════════════════════════════════════════════════════╗
# ║  §4.1  CechComplex — first-class Čech complex                   ║
# ╚═══════════════════════════════════════════════════════════════════╝

@dataclass
class CechComplex:
    """Full Čech complex C⁰ → C¹ → C² with coboundary matrices.

    Attributes
    ----------
    fibers : generators of C⁰
    overlaps : generators of C¹
    triples : generators of C²
    delta0 : GF2Matrix  |overlaps| × |fibers|
    delta1 : GF2Matrix  |triples| × |overlaps|
    """
    fibers: List[Tuple[str, ...]]
    overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]]
    triples: List[Tuple[int, int]]

    delta0: GF2Matrix = field(default_factory=lambda: GF2Matrix([]))
    delta1: GF2Matrix = field(default_factory=lambda: GF2Matrix([]))

    _rank_d0: Optional[int] = field(default=None, repr=False)
    _rank_d1: Optional[int] = field(default=None, repr=False)

    @property
    def rank_delta0(self) -> int:
        if self._rank_d0 is None:
            self._rank_d0 = self.delta0.rank()
        return self._rank_d0

    @property
    def rank_delta1(self) -> int:
        if self._rank_d1 is None:
            self._rank_d1 = self.delta1.rank() if self.delta1.nrows > 0 else 0
        return self._rank_d1

    @property
    def dim_c0(self) -> int:
        return len(self.fibers)

    @property
    def dim_c1(self) -> int:
        return len(self.overlaps)

    @property
    def dim_c2(self) -> int:
        return len(self.triples)

    @property
    def dim_ker_delta1(self) -> int:
        return self.dim_c1 - self.rank_delta1

    @property
    def h0(self) -> int:
        """H⁰ = ker(δ⁰).  For a connected cover this is 1."""
        return self.dim_c0 - self.rank_delta0

    @property
    def h1_rank(self) -> int:
        """H¹ = ker(δ¹) / im(δ⁰)."""
        return max(0, self.dim_ker_delta1 - self.rank_delta0)

    @property
    def euler_characteristic(self) -> int:
        return self.dim_c0 - self.dim_c1 + self.dim_c2

    def verify_complex(self) -> bool:
        """Check δ¹ ∘ δ⁰ = 0."""
        if self.delta1.nrows == 0 or self.delta0.nrows == 0:
            return True
        return self.delta1.coboundary_composition_vanishes(self.delta0)

    def ker_delta1_basis(self) -> List[List[int]]:
        """Basis for ker(δ¹) — the 1-cocycles."""
        if self.delta1.nrows == 0:
            return [
                [1 if j == k else 0 for j in range(self.dim_c1)]
                for k in range(self.dim_c1)
            ]
        return self.delta1.kernel_basis()

    def im_delta0_basis(self) -> List[List[int]]:
        """Basis for im(δ⁰) — the 1-coboundaries."""
        return self.delta0.column_space_basis()

    def summary(self) -> str:
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

    Builds D₀ and D₁ matrices over GF(2) using proper 2-simplex detection.
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

    # Build overlap edge lookup
    overlap_edge_set: Set[Tuple[int, int]] = set()
    overlap_by_edge: Dict[Tuple[int, int], int] = {}
    for k, (a, b) in enumerate(overlap_list):
        ia, ib = fiber_idx[a], fiber_idx[b]
        edge = (min(ia, ib), max(ia, ib))
        overlap_edge_set.add(edge)
        overlap_by_edge[edge] = k

    # 2-simplices: triples (i, j, k) where all three pairs overlap
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
    d1_ones: List[Tuple[int, int]] = []
    for t, (i, j, k) in enumerate(triple_simplices):
        for edge in [(i, j), (i, k), (j, k)]:
            if edge in overlap_by_edge:
                d1_ones.append((t, overlap_by_edge[edge]))
    delta1 = GF2Matrix.from_sets(len(triple_simplices), m, d1_ones)

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

    The 1-skeleton of the nerve of the cover.  Connected components
    correspond to independent subcomplexes.
    """
    nodes: List[Tuple[str, ...]]
    adjacency: Dict[int, Set[int]]

    @classmethod
    def from_overlaps(
        cls,
        fibers: List[Tuple[str, ...]],
        overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
    ) -> "FiberOverlapGraph":
        idx = {f: i for i, f in enumerate(fibers)}
        adj: Dict[int, Set[int]] = {i: set() for i in range(len(fibers))}
        for a, b in overlaps:
            if a in idx and b in idx:
                ia, ib = idx[a], idx[b]
                adj[ia].add(ib)
                adj[ib].add(ia)
        return cls(nodes=list(fibers), adjacency=adj)

    def degree(self, node_idx: int) -> int:
        return len(self.adjacency.get(node_idx, set()))

    def neighbors(self, node_idx: int) -> Set[int]:
        return self.adjacency.get(node_idx, set())

    def connected_components(self) -> List[List[int]]:
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
        return len(self.connected_components()) <= 1

    def subgraph(self, node_indices: Iterable[int]) -> "FiberOverlapGraph":
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
        edges: Set[Tuple[int, int]] = set()
        for i, nbs in self.adjacency.items():
            for j in nbs:
                edges.add((min(i, j), max(i, j)))
        return sorted(edges)

    def max_clique_size(self) -> int:
        """Upper bound on max clique via greedy coloring."""
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
        n = len(self.nodes)
        e = len(self.edge_list())
        cc = len(self.connected_components())
        return f"FiberOverlapGraph(|V|={n}, |E|={e}, components={cc})"


# ╔═══════════════════════════════════════════════════════════════════╗
# ║  §4.3  H¹ Obstruction Localization                              ║
# ╚═══════════════════════════════════════════════════════════════════╝

@dataclass
class ObstructionEdge:
    """An edge in the overlap graph contributing to H¹ ≠ 0."""
    fiber_a: Tuple[str, ...]
    fiber_b: Tuple[str, ...]
    overlap_index: int
    cocycle_coefficient: int


@dataclass
class ObstructionReport:
    """Full localization of H¹ obstructions."""
    h1_rank: int
    obstruction_edges: List[ObstructionEdge]
    cocycle_representatives: List[List[int]]
    explanation: str

    def involved_fibers(self) -> Set[Tuple[str, ...]]:
        result: Set[Tuple[str, ...]] = set()
        for e in self.obstruction_edges:
            result.add(e.fiber_a)
            result.add(e.fiber_b)
        return result


def localize_obstructions(cx: CechComplex) -> ObstructionReport:
    """Pinpoint which overlaps carry H¹ obstructions.

    Finds cocycles in ker(δ¹) that are NOT in im(δ⁰) and maps
    their non-trivial entries back to overlap edges.
    """
    if cx.h1_rank == 0:
        return ObstructionReport(
            h1_rank=0, obstruction_edges=[],
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
    """Find cocycles not in the span of coboundaries over GF(2)."""
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
    fiber.  Tracks the GF2 matrices and recomputes only when dirty.
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
        if fiber not in self._fiber_idx:
            return
        self._fibers = [f for f in self._fibers if f != fiber]
        self._fiber_idx = {f: i for i, f in enumerate(self._fibers)}
        self._overlaps = [
            (a, b) for a, b in self._overlaps if a != fiber and b != fiber
        ]
        self._dirty = True

    def _rebuild(self) -> None:
        if len(self._fibers) <= 1 or not self._overlaps:
            self._complex = CechComplex(
                fibers=list(self._fibers), overlaps=[], triples=[],
                delta0=GF2Matrix([]), delta1=GF2Matrix([]),
            )
        else:
            self._complex = build_cech_complex(self._fibers, self._overlaps)
        self._dirty = False

    @property
    def complex(self) -> CechComplex:
        if self._dirty or self._complex is None:
            self._rebuild()
        assert self._complex is not None
        return self._complex

    @property
    def h1_rank(self) -> int:
        return self.complex.h1_rank

    @property
    def h0(self) -> int:
        return self.complex.h0

    def snapshot(self) -> CechComplex:
        cx = self.complex
        return CechComplex(
            fibers=list(cx.fibers), overlaps=list(cx.overlaps),
            triples=list(cx.triples),
            delta0=GF2Matrix(cx.delta0.to_list()),
            delta1=GF2Matrix(cx.delta1.to_list()),
        )


def _fibers_share_axis(a: Tuple[str, ...], b: Tuple[str, ...]) -> bool:
    """True iff fibers agree on at least one axis position."""
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

    For constant GF(2)-coefficient sheaves the sequence degenerates at E₂,
    so E₂^{p,0} = Ĥ^p(U, F) gives global cohomology directly.
    """
    entries: Dict[Tuple[int, int], SpectralEntry]
    converges_at: str = "E₂"

    @classmethod
    def from_complex(cls, cx: CechComplex) -> "SpectralPage":
        entries: Dict[Tuple[int, int], SpectralEntry] = {}

        entries[(0, 0)] = SpectralEntry(
            p=0, q=0, dimension=cx.h0,
            generators=[], label="H⁰ = ker(δ⁰)",
        )

        h1_gens = _find_non_coboundary_cocycles(
            cx.ker_delta1_basis(), cx.im_delta0_basis(), cx.dim_c1,
        )
        entries[(1, 0)] = SpectralEntry(
            p=1, q=0, dimension=cx.h1_rank,
            generators=h1_gens, label="H¹ = ker(δ¹)/im(δ⁰)",
        )

        for p in range(3):
            for q in range(1, 3):
                entries[(p, q)] = SpectralEntry(
                    p=p, q=q, dimension=0, generators=[],
                    label="vanishes (constant sheaf)",
                )

        return cls(entries=entries)

    def total_dimension(self, n: int) -> int:
        return sum(
            e.dimension for (p, q), e in self.entries.items() if p + q == n
        )

    def is_degenerate(self) -> bool:
        return True

    def summary(self) -> str:
        lines = [f"Spectral Sequence (converges at {self.converges_at}):"]
        for (p, q) in sorted(self.entries):
            e = self.entries[(p, q)]
            if e.dimension > 0:
                lines.append(f"  E₂^{{{p},{q}}} = GF(2)^{e.dimension}  ({e.label})")
        if not any(e.dimension > 0 for e in self.entries.values()):
            lines.append("  All entries vanish → trivial cohomology")
        return "\n".join(lines)


# ╔═══════════════════════════════════════════════════════════════════╗
# ║  §4.6  Mayer-Vietoris Decomposition                             ║
# ╚═══════════════════════════════════════════════════════════════════╝

@dataclass
class MayerVietorisResult:
    """Result of Mayer-Vietoris decomposition (Corollary 8.4)."""
    h1_A: int
    h1_B: int
    alpha_surjective: bool
    h1_X: int
    connecting_image_dim: int
    piece_A_fibers: List[Tuple[str, ...]] = field(default_factory=list)
    piece_B_fibers: List[Tuple[str, ...]] = field(default_factory=list)
    intersection_fibers: List[Tuple[str, ...]] = field(default_factory=list)

    def is_conclusive(self) -> bool:
        return self.h1_A == 0 and self.h1_B == 0 and self.alpha_surjective

    def summary(self) -> str:
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
    """Apply Mayer-Vietoris to a two-piece decomposition."""
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
        h1_A=h1_A, h1_B=h1_B,
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

    Uses connected components if disconnected; otherwise splits at median.
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
    return set(fibers[:mid + 1]), set(fibers[mid:])


# ╔═══════════════════════════════════════════════════════════════════╗
# ║  §4.7  Symbolic Stalk Criterion                                  ║
# ╚═══════════════════════════════════════════════════════════════════╝

@dataclass
class SymbolicStalk:
    """A symbolic stalk ⟦f⟧|_{U_τ} (Definition 9.5).

    Represents restriction of denotational semantics of two programs
    to a single type fiber, together with the equivalence verdict.
    """
    fiber: Tuple[str, ...]
    term_f: object
    term_g: object
    is_isomorphism: Optional[bool]
    counterexample: Optional[str] = None
    explanation: str = ""

    def is_conclusive(self) -> bool:
        return self.is_isomorphism is not None


def stalk_criterion_check(stalks: List[SymbolicStalk]) -> Optional[bool]:
    """Theorem 9.3: η is an isomorphism iff η_x is an iso for all x.

    Returns True if all stalks are isomorphisms, False if any is not,
    None if some are inconclusive and none are False.
    """
    if not stalks:
        return None
    has_inconclusive = False
    for s in stalks:
        if s.is_isomorphism is False:
            return False
        if s.is_isomorphism is None:
            has_inconclusive = True
    return None if has_inconclusive else True


def stalks_to_h0(stalks: List[SymbolicStalk]) -> int:
    """Count stalks with isomorphism = True (Theorem 9.8)."""
    return sum(1 for s in stalks if s.is_isomorphism is True)


# ╔═══════════════════════════════════════════════════════════════════╗
# ║  §4.8  Gap Diagnostic                                           ║
# ╚═══════════════════════════════════════════════════════════════════╝

class MethodNeeded(Enum):
    CUBICAL_ONLY = "cubical_only"
    CECH_ONLY = "cech_only"
    COMBINED = "combined"
    NEITHER = "neither"


@dataclass
class GapDiagnostic:
    """Diagnostic for which verification method(s) suffice.

    Implements Proposition 10.7 (Formalization of the Gap).
    """
    cubical_succeeds: bool
    cech_raw_succeeds: bool
    cctt_succeeds: bool
    method: MethodNeeded
    explanation: str
    fibers_cubical_ok: List[Tuple[str, ...]] = field(default_factory=list)
    fibers_cech_ok: List[Tuple[str, ...]] = field(default_factory=list)

    def needs_normalization(self) -> bool:
        return self.method == MethodNeeded.COMBINED

    def is_decidable(self) -> bool:
        return self.method != MethodNeeded.NEITHER


def diagnose_method_gap(
    monolithic_result: Optional[bool],
    raw_cech_result: Optional[bool],
    cctt_result: Optional[bool],
    fibers_cubical: Optional[List[Tuple[str, ...]]] = None,
    fibers_cech: Optional[List[Tuple[str, ...]]] = None,
) -> GapDiagnostic:
    """Proposition 10.7: classify where (f, g) falls in the method gap."""
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
        explanation = "Cubical normalization per fiber + cohomological gluing needed"
    else:
        method = MethodNeeded.NEITHER
        explanation = "Neither method succeeds (may be genuinely inequivalent or undecidable)"

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
# ║  §4.9  CechPipeline — Integration wrapper                       ║
# ╚═══════════════════════════════════════════════════════════════════╝

@dataclass
class PipelineReport:
    """Full report from the CechPipeline."""
    complex: CechComplex
    graph: FiberOverlapGraph
    obstructions: ObstructionReport
    spectral: SpectralPage
    mayer_vietoris: Optional[MayerVietorisResult]
    stalks: List[SymbolicStalk]
    h1_rank: int
    equivalent: Optional[bool]

    def full_summary(self) -> str:
        lines = [
            "═══ Čech Pipeline Report ═══",
            self.complex.summary(),
            self.graph.summary(),
            f"H¹ = {self.h1_rank}  →  "
            f"{'EQUIVALENT' if self.equivalent else 'NOT EQUIVALENT' if self.equivalent is False else 'INCONCLUSIVE'}",
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

    Wraps individual modules into a single entry point matching
    the checker's ``compute_cech_h1`` call site.
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
        equiv_fibers = [f for f in fibers if judgments.get(f) is True]

        # 1. Build complex
        if len(equiv_fibers) > 1 and overlaps:
            cx = build_cech_complex(equiv_fibers, overlaps)
        else:
            cx = CechComplex(
                fibers=equiv_fibers, overlaps=[], triples=[],
                delta0=GF2Matrix([]), delta1=GF2Matrix([]),
            )

        # 2. Overlap graph
        graph = FiberOverlapGraph.from_overlaps(fibers, overlaps)

        # 3. Obstruction localization
        obs = localize_obstructions(cx)

        # 4. Spectral sequence
        spectral = SpectralPage.from_complex(cx)

        # 5. Mayer-Vietoris
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
            complex=cx, graph=graph, obstructions=obs,
            spectral=spectral, mayer_vietoris=mv_result,
            stalks=stalks, h1_rank=cx.h1_rank, equivalent=equivalent,
        )


# ╔═══════════════════════════════════════════════════════════════════╗
# ║  §4.10  Utilities                                               ║
# ╚═══════════════════════════════════════════════════════════════════╝

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

    # ── GF2Matrix ────────────────────────────────────────────────
    print("Testing GF2Matrix...")
    m1 = GF2Matrix([[1, 0, 1], [0, 1, 1]])
    _assert(m1.shape == (2, 3), "shape")
    _assert(m1[0, 0] == 1, "getitem")
    _assert(m1.rank() == 2, "rank of full-rank 2x3")

    m_id = GF2Matrix.identity(3)
    _assert(m_id.rank() == 3, "identity rank")

    m_zero = GF2Matrix.zeros(2, 2)
    _assert(m_zero.rank() == 0, "zero matrix rank")
    _assert(m_zero.is_zero(), "zero matrix is_zero")

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

    m_add = m1 + GF2Matrix([[1, 1, 0], [1, 0, 0]])
    _assert(m_add[0, 0] == 0, "GF2 addition 1+1=0")

    # ── CechComplex ──────────────────────────────────────────────
    print("Testing CechComplex...")
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
    _assert(cx_tri.h1_rank == 0, "triangle H¹ = 0")

    overlaps_path = [
        (("int",), ("str",)),
        (("str",), ("bool",)),
    ]
    cx_path = build_cech_complex(fibers_tri, overlaps_path)
    _assert(cx_path.h1_rank == 0, "path H¹ = 0")

    fibers_sq = [("a",), ("b",), ("c",), ("d",)]
    overlaps_sq = [
        (("a",), ("b",)),
        (("b",), ("c",)),
        (("c",), ("d",)),
        (("d",), ("a",)),
    ]
    cx_sq = build_cech_complex(fibers_sq, overlaps_sq)
    _assert(cx_sq.verify_complex(), "square δ¹∘δ⁰ = 0")
    _assert(cx_sq.h1_rank == 1, "square H¹ = 1")

    # ── FiberOverlapGraph ────────────────────────────────────────
    print("Testing FiberOverlapGraph...")
    g_tri = FiberOverlapGraph.from_overlaps(fibers_tri, overlaps_tri)
    _assert(g_tri.is_connected(), "triangle is connected")
    _assert(len(g_tri.edge_list()) == 3, "triangle edges")
    _assert(g_tri.degree(0) == 2, "triangle degree")

    g_disc = FiberOverlapGraph.from_overlaps([("int",), ("str",)], [])
    _assert(not g_disc.is_connected(), "disconnected not connected")
    _assert(len(g_disc.connected_components()) == 2, "disconnected 2 comps")

    sub = g_tri.subgraph([0, 1])
    _assert(len(sub.nodes) == 2, "subgraph 2 nodes")

    # ── ObstructionLocator ───────────────────────────────────────
    print("Testing ObstructionLocator...")
    obs_tri = localize_obstructions(cx_tri)
    _assert(obs_tri.h1_rank == 0, "triangle no obstructions")

    obs_sq = localize_obstructions(cx_sq)
    _assert(obs_sq.h1_rank == 1, "square H¹ = 1")
    _assert(len(obs_sq.obstruction_edges) > 0, "square has obstruction edges")

    # ── IncrementalCech ──────────────────────────────────────────
    print("Testing IncrementalCech...")
    inc = IncrementalCech()
    inc.add_fiber(("int",))
    _assert(inc.h1_rank == 0, "incremental 1 fiber H¹ = 0")

    inc.add_fiber(("str",), [("int",)])
    _assert(inc.fiber_count == 2, "incremental 2 fibers")

    inc.add_fiber(("bool",), [("int",), ("str",)])
    _assert(inc.h1_rank == 0, "incremental triangle H¹ = 0")

    inc2 = IncrementalCech()
    inc2.add_fiber(("a",))
    inc2.add_fiber(("b",), [("a",)])
    inc2.add_fiber(("c",), [("b",)])
    inc2.add_fiber(("d",), [("c",), ("a",)])
    _assert(inc2.h1_rank == 1, "incremental square H¹ = 1")

    inc2.remove_fiber(("d",))
    _assert(inc2.h1_rank == 0, "after removal H¹ = 0")

    snap = inc.snapshot()
    _assert(snap.h1_rank == inc.h1_rank, "snapshot matches")

    # ── SpectralPage ─────────────────────────────────────────────
    print("Testing SpectralPage...")
    sp_tri = SpectralPage.from_complex(cx_tri)
    _assert(sp_tri.entries[(1, 0)].dimension == 0, "triangle E₂^{1,0} = 0")
    _assert(sp_tri.is_degenerate(), "spectral degenerates at E₂")

    sp_sq = SpectralPage.from_complex(cx_sq)
    _assert(sp_sq.entries[(1, 0)].dimension == 1, "square E₂^{1,0} = 1")
    _assert(sp_sq.total_dimension(1) == 1, "square total H¹ = 1")

    # ── MayerVietoris ────────────────────────────────────────────
    print("Testing MayerVietoris...")
    mv_judgments: Dict[Tuple[str, ...], bool] = {
        ("int",): True, ("str",): True, ("bool",): True,
    }
    part_a = {("int",), ("str",)}
    part_b = {("str",), ("bool",)}
    mv = mayer_vietoris_split(mv_judgments, overlaps_tri, part_a, part_b)
    _assert(mv.h1_X == 0, "MV triangle H¹ = 0")
    _assert(mv.is_conclusive(), "MV conclusive")

    auto_a, auto_b = auto_partition(fibers_tri, overlaps_tri)
    _assert(len(auto_a) > 0 and len(auto_b) > 0, "auto partition non-empty")

    # ── SymbolicStalk ────────────────────────────────────────────
    print("Testing SymbolicStalk...")
    s1 = SymbolicStalk(("int",), None, None, True)
    s2 = SymbolicStalk(("str",), None, None, True)
    s3 = SymbolicStalk(("bool",), None, None, False, counterexample="x=True")
    _assert(stalk_criterion_check([s1, s2]) is True, "all iso → True")
    _assert(stalk_criterion_check([s1, s3]) is False, "one non-iso → False")
    _assert(stalk_criterion_check([]) is None, "empty → None")
    _assert(stalks_to_h0([s1, s2, s3]) == 2, "H⁰ count")

    # ── GapDiagnostic ────────────────────────────────────────────
    print("Testing GapDiagnostic...")
    d1 = diagnose_method_gap(True, None, None)
    _assert(d1.method == MethodNeeded.CUBICAL_ONLY, "cubical only")

    d2 = diagnose_method_gap(None, True, None)
    _assert(d2.method == MethodNeeded.CECH_ONLY, "cech only")

    d3 = diagnose_method_gap(None, None, True)
    _assert(d3.method == MethodNeeded.COMBINED, "combined")
    _assert(d3.needs_normalization(), "combined needs normalization")

    d4 = diagnose_method_gap(None, None, None)
    _assert(d4.method == MethodNeeded.NEITHER, "neither")

    # ── CechPipeline ─────────────────────────────────────────────
    print("Testing CechPipeline...")
    pipeline = CechPipeline()
    jdg: Dict[Tuple[str, ...], Optional[bool]] = {
        ("int",): True, ("str",): True, ("bool",): True,
    }
    report = pipeline.run(fibers_tri, overlaps_tri, jdg)
    _assert(report.h1_rank == 0, "pipeline H¹ = 0")
    _assert(report.equivalent is True, "pipeline equivalent")
    _assert("EQUIVALENT" in report.full_summary(), "pipeline summary")

    jdg2: Dict[Tuple[str, ...], Optional[bool]] = {
        ("int",): True, ("str",): False, ("bool",): True,
    }
    report2 = pipeline.run(fibers_tri, overlaps_tri, jdg2)
    _assert(report2.equivalent is False, "pipeline NEQ")

    # ── Utilities ────────────────────────────────────────────────
    print("Testing utilities...")
    b0, b1 = betti_numbers(cx_tri)
    _assert(b1 == 0, "betti β₁ triangle")

    eq_c, neq_c, unk_c = fiber_coverage(jdg)
    _assert(eq_c == 3 and neq_c == 0 and unk_c == 0, "coverage")

    _assert(_fibers_share_axis(("int",), ("int",)), "same axis share")
    _assert(not _fibers_share_axis(("int",), ("str",)), "diff axis no share")

    # ── Summary ──────────────────────────────────────────────────
    total = passed + failed
    print(f"\n{'='*50}")
    print(f"Results: {passed}/{total} passed, {failed} failed")
    sys.exit(1 if failed else 0)
