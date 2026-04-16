"""Sheaf-theoretic structures for fiber decomposition and H¹ computation.

Implements the algebraic-geometric machinery from monograph Ch.5-6:
  - GF(2) linear algebra (vectors, matrices, kernel/rank)
  - Grothendieck covering sieves (DuckSieve, CoveringFamily)
  - Isomorphism sheaf Iso(Sem_f, Sem_g) with GF(2) sections
  - Čech complex C⁰ →[δ⁰] C¹ →[δ¹] C² with explicit GF2Matrix ops
  - Fiber pruning and covering minimization
  - Overlap cache for incremental re-checking

Wired from proposals in g03_kan_sheaves.py (Proposals 3, 5, 6, 7, 9, 10).
"""
from __future__ import annotations

import hashlib
import itertools
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from cctt.cohomology import LocalJudgment


# ═══════════════════════════════════════════════════════════════════
#  GF(2) linear algebra
# ═══════════════════════════════════════════════════════════════════

class GF2Vector:
    """A vector over GF(2) = {0, 1} with arithmetic mod 2."""

    __slots__ = ('entries',)

    def __init__(self, entries: List[int]) -> None:
        self.entries = [e % 2 for e in entries]

    @property
    def dim(self) -> int:
        return len(self.entries)

    def __add__(self, other: GF2Vector) -> GF2Vector:
        if self.dim != other.dim:
            raise ValueError(f'dimension mismatch: {self.dim} vs {other.dim}')
        return GF2Vector([(a + b) % 2 for a, b in zip(self.entries, other.entries)])

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, GF2Vector):
            return NotImplemented
        return self.entries == other.entries

    def __repr__(self) -> str:
        return f'GF2[{"".join(str(e) for e in self.entries)}]'

    def dot(self, other: GF2Vector) -> int:
        if self.dim != other.dim:
            raise ValueError(f'dimension mismatch: {self.dim} vs {other.dim}')
        return sum(a * b for a, b in zip(self.entries, other.entries)) % 2

    def is_zero(self) -> bool:
        return all(e == 0 for e in self.entries)

    @staticmethod
    def zero(n: int) -> GF2Vector:
        return GF2Vector([0] * n)

    @staticmethod
    def basis(n: int, k: int) -> GF2Vector:
        v = [0] * n
        v[k] = 1
        return GF2Vector(v)


class GF2Matrix:
    """A matrix over GF(2) with Gaussian elimination for rank/kernel."""

    __slots__ = ('rows', 'nrows', 'ncols')

    def __init__(self, rows: List[List[int]]) -> None:
        self.rows = [[e % 2 for e in row] for row in rows]
        self.nrows = len(self.rows)
        self.ncols = len(self.rows[0]) if self.rows else 0

    def rank(self) -> int:
        m = [row[:] for row in self.rows]
        rows, cols = self.nrows, self.ncols
        r = 0
        for col in range(cols):
            pivot = None
            for row in range(r, rows):
                if m[row][col] == 1:
                    pivot = row
                    break
            if pivot is None:
                continue
            m[r], m[pivot] = m[pivot], m[r]
            for row in range(rows):
                if row != r and m[row][col] == 1:
                    m[row] = [(m[row][j] + m[r][j]) % 2 for j in range(cols)]
            r += 1
        return r

    def kernel_basis(self) -> List[GF2Vector]:
        """Compute a basis for ker(M) over GF(2)."""
        m = [row[:] for row in self.rows]
        rows, cols = self.nrows, self.ncols
        pivot_col = [-1] * rows
        r = 0
        for col in range(cols):
            pivot = None
            for row in range(r, rows):
                if m[row][col] == 1:
                    pivot = row
                    break
            if pivot is None:
                continue
            m[r], m[pivot] = m[pivot], m[r]
            pivot_col[r] = col
            for row in range(rows):
                if row != r and m[row][col] == 1:
                    m[row] = [(m[row][j] + m[r][j]) % 2 for j in range(cols)]
            r += 1

        pivot_cols = set(pivot_col[i] for i in range(r))
        free_cols = [c for c in range(cols) if c not in pivot_cols]
        kernel: List[GF2Vector] = []
        for fc in free_cols:
            v = [0] * cols
            v[fc] = 1
            for i in range(r):
                pc = pivot_col[i]
                if pc >= 0 and m[i][fc] == 1:
                    v[pc] = 1
            kernel.append(GF2Vector(v))
        return kernel

    def transpose(self) -> GF2Matrix:
        if self.nrows == 0 or self.ncols == 0:
            return GF2Matrix([])
        t = [[self.rows[r][c] for r in range(self.nrows)] for c in range(self.ncols)]
        return GF2Matrix(t)

    def __mul__(self, other: GF2Matrix) -> GF2Matrix:
        if self.ncols != other.nrows:
            raise ValueError(
                f'shape mismatch: ({self.nrows}×{self.ncols}) × '
                f'({other.nrows}×{other.ncols})')
        result = []
        for i in range(self.nrows):
            row = []
            for j in range(other.ncols):
                s = sum(self.rows[i][k] * other.rows[k][j]
                        for k in range(self.ncols)) % 2
                row.append(s)
            result.append(row)
        return GF2Matrix(result)

    def __repr__(self) -> str:
        return f'GF2Matrix({self.nrows}×{self.ncols}, rank={self.rank()})'


# ═══════════════════════════════════════════════════════════════════
#  Grothendieck covering sieves  (Proposal 3)
# ═══════════════════════════════════════════════════════════════════

ALL_TYPE_TAGS: FrozenSet[str] = frozenset(
    {'int', 'bool', 'str', 'pair', 'ref', 'none'}
)

_NUMERIC_OPS: FrozenSet[str] = frozenset({
    'sub', 'mul', 'imul', 'floordiv', 'mod', 'pow', 'neg',
    'lshift', 'rshift', 'bitor', 'bitand', 'bitxor', 'invert',
    'call_range', 'used_as_index', 'truediv', 'lt', 'le', 'gt', 'ge',
})

_STR_OPS: FrozenSet[str] = frozenset({
    'method_upper', 'method_lower', 'method_strip', 'method_split',
    'method_replace', 'method_find', 'method_startswith',
    'method_endswith', 'method_join', 'method_encode', 'method_format',
})

_COLLECTION_OPS: FrozenSet[str] = frozenset({
    'iter', 'getitem', 'call_len', 'call_sorted', 'call_list',
    'call_set', 'call_reversed', 'call_enumerate', 'call_sum',
    'call_zip', 'call_map', 'call_filter',
})


@dataclass(frozen=True)
class DuckSieve:
    """The Grothendieck covering sieve for a parameter (Def 6.5).

    A sieve on an object U in the site category is a downward-closed
    collection of morphisms into U.  In our setting, the objects are
    type tags and the sieve is the set of tags compatible with all
    operations applied to the parameter in both programs.
    """
    param_name: str
    tags: FrozenSet[str]
    operations: FrozenSet[str]
    is_tight: bool

    @staticmethod
    def trivial(param_name: str) -> DuckSieve:
        """The trivial (maximal) sieve — no narrowing."""
        return DuckSieve(param_name=param_name, tags=ALL_TYPE_TAGS,
                         operations=frozenset(), is_tight=False)

    @staticmethod
    def from_tag_and_ops(param_name: str, tag: str,
                         tight: bool, ops: FrozenSet[str]) -> DuckSieve:
        """Build a sieve from an inferred duck type."""
        tag_map: Dict[str, FrozenSet[str]] = {
            'int': frozenset({'int'}),
            'str': frozenset({'str'}),
            'bool': frozenset({'bool'}),
            'ref': frozenset({'ref'}),
            'list': frozenset({'pair', 'ref'}),
            'collection': frozenset({'pair', 'ref', 'str'}),
            'any': ALL_TYPE_TAGS,
            'unknown': ALL_TYPE_TAGS,
        }
        tags = tag_map.get(tag, ALL_TYPE_TAGS)
        return DuckSieve(param_name=param_name, tags=tags,
                         operations=ops, is_tight=tight)

    @property
    def is_trivial(self) -> bool:
        return self.tags == ALL_TYPE_TAGS

    @property
    def fiber_count(self) -> int:
        return len(self.tags)

    def intersect(self, other: DuckSieve) -> DuckSieve:
        """Intersect two sieves (meet in the sieve lattice)."""
        if self.param_name != other.param_name:
            raise ValueError(
                f'Cannot intersect sieves for different params: '
                f'{self.param_name} vs {other.param_name}')
        new_tags = self.tags & other.tags
        return DuckSieve(
            param_name=self.param_name,
            tags=new_tags if new_tags else frozenset({'none'}),
            operations=self.operations | other.operations,
            is_tight=len(new_tags) <= 1,
        )

    def contains_tag(self, tag: str) -> bool:
        return tag in self.tags

    def as_fiber_list(self) -> List[str]:
        return sorted(self.tags)


@dataclass
class CoveringFamily:
    """The covering family {U_i} from a collection of per-parameter sieves.

    The covering is the Cartesian product of per-parameter sieve tags,
    capped at max_fibers to prevent Z3 memory blow-up.

    MONOGRAPH: Prop 6.6 — the duck sieve forms a covering sieve.
    """
    sieves: List[DuckSieve]
    combos: List[Tuple[str, ...]] = field(default_factory=list)
    capped: bool = False

    MAX_FIBERS: int = field(default=12, init=False, repr=False)

    @staticmethod
    def from_sieves(sieves: List[DuckSieve],
                    max_fibers: int = 12) -> CoveringFamily:
        if not sieves:
            return CoveringFamily(sieves=[], combos=[()], capped=False)
        raw = list(itertools.product(*(s.as_fiber_list() for s in sieves)))
        capped = len(raw) > max_fibers
        combos = raw[:max_fibers]
        return CoveringFamily(sieves=sieves, combos=combos, capped=capped)

    @property
    def total_fibers(self) -> int:
        return len(self.combos)

    @property
    def param_names(self) -> List[str]:
        return [s.param_name for s in self.sieves]

    def overlaps(self) -> List[Tuple[Tuple[str, ...], Tuple[str, ...]]]:
        """Compute pairwise overlaps: fiber combos sharing at least one axis.

        Two fibers overlap when they agree on at least one parameter's tag.
        This defines the Čech nerve of the covering.
        """
        result: List[Tuple[Tuple[str, ...], Tuple[str, ...]]] = []
        for i in range(len(self.combos)):
            for j in range(i + 1, len(self.combos)):
                ci, cj = self.combos[i], self.combos[j]
                if any(ci[k] == cj[k] for k in range(len(ci))):
                    result.append((ci, cj))
        return result


# ═══════════════════════════════════════════════════════════════════
#  Isomorphism sheaf  (Proposal 5)
# ═══════════════════════════════════════════════════════════════════

class IsomorphismSheaf:
    """The isomorphism sheaf Iso(Sem_f, Sem_g) (Def 6.11).

    Values in GF(2): 1 = equivalent, 0 = counterexample, None = unknown.
    The sheaf condition requires that local sections on overlapping fibers
    agree on their overlap.  H¹ = 0 says local equivalences glue globally.
    """

    def __init__(self, judgments: Dict[Tuple[str, ...], LocalJudgment]) -> None:
        self._judgments = dict(judgments)
        self._sections: Dict[Tuple[str, ...], Optional[int]] = {}
        for fiber, j in judgments.items():
            if j.is_equivalent is True:
                self._sections[fiber] = 1
            elif j.is_equivalent is False:
                self._sections[fiber] = 0
            else:
                self._sections[fiber] = None
        self._fibers = sorted(self._sections.keys())

    @property
    def fibers(self) -> List[Tuple[str, ...]]:
        return list(self._fibers)

    @property
    def num_fibers(self) -> int:
        return len(self._fibers)

    def section(self, fiber: Tuple[str, ...]) -> Optional[int]:
        """Iso(U_fiber) ∈ {0, 1} or None if unknown."""
        return self._sections.get(fiber)

    def judgment(self, fiber: Tuple[str, ...]) -> Optional[LocalJudgment]:
        return self._judgments.get(fiber)

    def known_fibers(self) -> List[Tuple[str, ...]]:
        return [f for f in self._fibers if self._sections[f] is not None]

    def equivalent_fibers(self) -> List[Tuple[str, ...]]:
        return [f for f in self._fibers if self._sections.get(f) == 1]

    def obstruction_fibers(self) -> List[Tuple[str, ...]]:
        return [f for f in self._fibers if self._sections.get(f) == 0]

    def unknown_fibers(self) -> List[Tuple[str, ...]]:
        return [f for f in self._fibers if self._sections.get(f) is None]

    def coverage(self) -> float:
        if not self._fibers:
            return 0.0
        return len(self.known_fibers()) / len(self._fibers)

    def global_section(self) -> Optional[int]:
        """Γ(Iso) — the global section if it exists.

        Returns 1 if all known fibers are equivalent and coverage is complete.
        Returns 0 if any fiber has a counterexample.
        Returns None if inconclusive.
        """
        vals = [v for v in self._sections.values() if v is not None]
        if not vals:
            return None
        if any(v == 0 for v in vals):
            return 0
        if all(v == 1 for v in vals) and len(vals) == len(self._fibers):
            return 1
        return None

    def as_0_cochain(self) -> GF2Vector:
        """Return as C⁰ vector over GF(2) for Čech computation.

        Unknown sections are treated as 0 (conservative).
        """
        entries = [self._sections.get(f, 0) or 0 for f in self._fibers]
        return GF2Vector(entries)

    def as_dict(self) -> Dict[Tuple[str, ...], Optional[int]]:
        return dict(self._sections)

    def __repr__(self) -> str:
        eq = len(self.equivalent_fibers())
        neq = len(self.obstruction_fibers())
        unk = len(self.unknown_fibers())
        return f'IsomorphismSheaf(eq={eq}, neq={neq}, unknown={unk})'


# ═══════════════════════════════════════════════════════════════════
#  Fiber pruning  (Proposal 6)
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class FiberRelevance:
    """Records why a fiber is or is not relevant for checking.

    A fiber is IRRELEVANT if all operations on its parameters are
    type-agnostic (eq, ne, hash, etc.) — the fiber can be collapsed
    without loss of soundness.
    """
    fiber: Tuple[str, ...]
    is_relevant: bool
    reason: str = ''


# Operations that behave identically regardless of type tag
TYPE_AGNOSTIC_OPS: FrozenSet[str] = frozenset({
    'eq', 'ne', 'is', 'isnot', 'not', 'isinstance_check',
    'call_id', 'call_hash', 'call_type', 'call_repr', 'call_str',
    'call_print', 'call_bool',
})


def prune_irrelevant_fibers(
    covering: CoveringFamily,
    ops_per_param: Dict[str, FrozenSet[str]],
) -> Tuple[CoveringFamily, List[FiberRelevance]]:
    """Remove fibers where all parameters have type-agnostic operations.

    Returns (pruned_covering, relevance_reports).
    """
    reports: List[FiberRelevance] = []
    kept: List[Tuple[str, ...]] = []

    for combo in covering.combos:
        dominated = True
        for i, sieve in enumerate(covering.sieves):
            pname = sieve.param_name
            ops = ops_per_param.get(pname, frozenset())
            if ops - TYPE_AGNOSTIC_OPS:
                dominated = False
                break
        if dominated and len(kept) >= 1:
            reports.append(FiberRelevance(
                combo, is_relevant=False,
                reason='all ops type-agnostic; collapsed with representative'))
        else:
            kept.append(combo)
            reports.append(FiberRelevance(combo, is_relevant=True))

    pruned = CoveringFamily(
        sieves=covering.sieves,
        combos=kept,
        capped=covering.capped,
    )
    return pruned, reports


# ═══════════════════════════════════════════════════════════════════
#  Čech complex with GF(2) matrices  (Proposal 7)
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class CechCohomology:
    """Result of a Čech cohomology computation.

    h1 = 0 ↔ local sections glue to global ↔ programs are EQUIVALENT.
    """
    h0: int
    h1: int
    rank_delta0: int
    rank_delta1: int
    dim_c0: int
    dim_c1: int
    dim_c2: int

    @property
    def is_trivial(self) -> bool:
        """H¹ = 0 means local sections glue to global."""
        return self.h1 == 0

    @property
    def euler_characteristic(self) -> int:
        """χ = h⁰ - h¹ (alternating sum of Betti numbers)."""
        return self.h0 - self.h1


class CechComplex:
    """The Čech complex C⁰ →[δ⁰] C¹ →[δ¹] C² with GF(2) matrices.

    Given a covering family {U_i}:
      - C⁰: one basis element per fiber U_i
      - C¹: one basis element per pairwise overlap U_i ∩ U_j
      - C²: one basis element per triple overlap U_i ∩ U_j ∩ U_k
      - H¹ = ker(δ¹) / im(δ⁰) is the obstruction to gluing
    """

    def __init__(
        self,
        fibers: List[Tuple[str, ...]],
        overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
        delta0: GF2Matrix,
        delta1: GF2Matrix,
        triple_overlaps: List[Tuple[int, int]],
    ) -> None:
        self.fibers = fibers
        self.overlaps = overlaps
        self.delta0 = delta0
        self.delta1 = delta1
        self.triple_overlaps = triple_overlaps

    @staticmethod
    def build(
        fibers: List[Tuple[str, ...]],
        overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
    ) -> CechComplex:
        """Build the Čech complex from fibers and overlaps."""
        fiber_idx = {f: i for i, f in enumerate(fibers)}
        n = len(fibers)

        overlap_list = [(a, b) for a, b in overlaps
                        if a in fiber_idx and b in fiber_idx]
        m = len(overlap_list)

        # δ⁰ : C⁰ → C¹  (m overlaps × n fibers)
        delta0_rows = []
        for a, b in overlap_list:
            row = [0] * n
            row[fiber_idx[a]] = 1
            row[fiber_idx[b]] = 1
            delta0_rows.append(row)
        delta0 = GF2Matrix(delta0_rows) if delta0_rows else GF2Matrix([])

        # Triple overlaps: pairs of overlaps sharing a fiber
        triples: List[Tuple[int, int]] = []
        for i, (a1, b1) in enumerate(overlap_list):
            for j, (a2, b2) in enumerate(overlap_list):
                if j <= i:
                    continue
                if {a1, b1} & {a2, b2}:
                    triples.append((i, j))

        # δ¹ : C¹ → C²  (triples × overlaps)
        delta1_rows = []
        for oi, oj in triples:
            row = [0] * m
            row[oi] = 1
            row[oj] = 1
            delta1_rows.append(row)
        delta1 = GF2Matrix(delta1_rows) if delta1_rows else GF2Matrix([])

        return CechComplex(fibers, overlaps, delta0, delta1, triples)

    def compute_h1(self) -> CechCohomology:
        """Compute H¹ = ker(δ¹) / im(δ⁰)."""
        n = len(self.fibers)

        rank_d0 = self.delta0.rank() if self.delta0.nrows > 0 else 0
        rank_d1 = self.delta1.rank() if self.delta1.nrows > 0 else 0

        dim_c1 = self.delta0.nrows if self.delta0.nrows > 0 else 0
        ker_d1 = dim_c1 - rank_d1

        h1 = max(0, ker_d1 - rank_d0)

        return CechCohomology(
            h0=n,
            h1=h1,
            rank_delta0=rank_d0,
            rank_delta1=rank_d1,
            dim_c0=n,
            dim_c1=dim_c1,
            dim_c2=len(self.triple_overlaps),
        )

    def kernel_basis_delta0(self) -> List[GF2Vector]:
        """Basis of ker(δ⁰) — the 0-cocycles."""
        if self.delta0.nrows == 0:
            return []
        return self.delta0.transpose().kernel_basis()


# ═══════════════════════════════════════════════════════════════════
#  Covering minimization  (Proposal 9)
# ═══════════════════════════════════════════════════════════════════

def _fibers_share_axis(a: Tuple[str, ...], b: Tuple[str, ...]) -> bool:
    """Check if two fiber combos share at least one tag on the same axis."""
    return any(ai == bi for ai, bi in zip(a, b))


def minimize_covering(
    covering: CoveringFamily,
    judgments: Optional[Dict[Tuple[str, ...], LocalJudgment]] = None,
) -> CoveringFamily:
    """Remove redundant fibers from a covering family.

    Deduplicates, then optionally removes fibers subsumed by
    already-proven-equivalent fibers (monotonicity of equivalence).
    """
    # Step 1: remove duplicates
    seen: Set[Tuple[str, ...]] = set()
    unique: List[Tuple[str, ...]] = []
    for combo in covering.combos:
        if combo not in seen:
            seen.add(combo)
            unique.append(combo)

    # Step 2: if judgments provided, remove fibers subsumed by equivalent ones
    if judgments:
        proven_eq = {f for f, j in judgments.items() if j.is_equivalent is True}
        minimal: List[Tuple[str, ...]] = []
        for combo in unique:
            if combo not in proven_eq or combo in minimal:
                minimal.append(combo)
            else:
                covered_by_other = False
                for other in unique:
                    if other == combo:
                        continue
                    if other in proven_eq and _fibers_share_axis(combo, other):
                        covered_by_other = True
                        break
                if not covered_by_other:
                    minimal.append(combo)
        unique = minimal

    return CoveringFamily(
        sieves=covering.sieves,
        combos=unique,
        capped=covering.capped,
    )


# ═══════════════════════════════════════════════════════════════════
#  Overlap cache  (Proposal 10)
# ═══════════════════════════════════════════════════════════════════

class OverlapCache:
    """Cache for overlap computation and Čech complex construction.

    Avoids recomputing the overlap structure and coboundary matrices
    when only local judgments change (same covering family).
    """

    def __init__(self, max_entries: int = 64) -> None:
        self._cache: Dict[str, CechComplex] = {}
        self._access_order: List[str] = []
        self._max_entries = max_entries
        self._hits = 0
        self._misses = 0

    def _key(self, fibers: List[Tuple[str, ...]],
             overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]]) -> str:
        content = repr((sorted(fibers), sorted(overlaps)))
        return hashlib.md5(content.encode()).hexdigest()

    def get_or_build(
        self,
        fibers: List[Tuple[str, ...]],
        overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
    ) -> CechComplex:
        """Get the CechComplex from cache, or build and cache it."""
        key = self._key(fibers, overlaps)
        if key in self._cache:
            self._hits += 1
            return self._cache[key]

        self._misses += 1
        cx = CechComplex.build(fibers, overlaps)

        # LRU eviction
        if len(self._cache) >= self._max_entries:
            oldest = self._access_order.pop(0)
            self._cache.pop(oldest, None)

        self._cache[key] = cx
        self._access_order.append(key)
        return cx

    def invalidate(self) -> None:
        self._cache.clear()
        self._access_order.clear()

    def stats(self) -> Dict[str, int]:
        return {
            'hits': self._hits,
            'misses': self._misses,
            'entries': len(self._cache),
            'max_entries': self._max_entries,
        }


# ═══════════════════════════════════════════════════════════════════
#  Integration: enhanced Čech pipeline
# ═══════════════════════════════════════════════════════════════════

def compute_enhanced_cech(
    judgments: Dict[Tuple[str, ...], LocalJudgment],
    overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
    cache: Optional[OverlapCache] = None,
) -> Tuple[CechCohomology, IsomorphismSheaf]:
    """Compute Čech H¹ using the structured sheaf/complex pipeline.

    Combines IsomorphismSheaf, CechComplex, and optional OverlapCache
    into a single call that returns both the cohomology result and
    the isomorphism sheaf for downstream inspection.
    """
    sheaf = IsomorphismSheaf(judgments)
    fibers = sheaf.equivalent_fibers()

    if not fibers:
        return (
            CechCohomology(h0=0, h1=0, rank_delta0=0, rank_delta1=0,
                           dim_c0=sheaf.num_fibers, dim_c1=0, dim_c2=0),
            sheaf,
        )

    # Filter overlaps to equivalent fibers only
    fiber_set = set(fibers)
    relevant_overlaps = [(a, b) for a, b in overlaps
                         if a in fiber_set and b in fiber_set]

    if cache is not None:
        cx = cache.get_or_build(fibers, relevant_overlaps)
    else:
        cx = CechComplex.build(fibers, relevant_overlaps)

    cohomology = cx.compute_h1()
    return cohomology, sheaf


# ═══════════════════════════════════════════════════════════════════
#  Self-tests
# ═══════════════════════════════════════════════════════════════════

def _run_self_tests() -> None:
    import sys

    counts = {'passed': 0, 'failed': 0}

    def check(name: str, condition: bool) -> None:
        if condition:
            counts['passed'] += 1
            print(f'  ✓ {name}')
        else:
            counts['failed'] += 1
            print(f'  ✗ {name}')

    # ── GF(2) linear algebra ──
    print('GF(2) linear algebra:')
    v1 = GF2Vector([1, 0, 1])
    v2 = GF2Vector([1, 1, 0])
    check('GF2Vector add', (v1 + v2).entries == [0, 1, 1])
    check('GF2Vector dot', v1.dot(v2) == 1)
    check('GF2Vector zero', GF2Vector.zero(3).is_zero())
    check('GF2Vector basis', GF2Vector.basis(3, 1).entries == [0, 1, 0])

    m1 = GF2Matrix([[1, 1, 0], [0, 1, 1], [1, 0, 1]])
    check('GF2Matrix rank', m1.rank() == 2)
    check('GF2Matrix kernel non-empty', len(m1.kernel_basis()) == 1)
    check('GF2Matrix kernel correct',
          m1.kernel_basis()[0].entries in ([1, 1, 1],))

    m_id = GF2Matrix([[1, 0], [0, 1]])
    check('GF2Matrix identity rank', m_id.rank() == 2)
    check('GF2Matrix identity kernel empty', len(m_id.kernel_basis()) == 0)

    m_zero = GF2Matrix([[0, 0], [0, 0]])
    check('GF2Matrix zero rank', m_zero.rank() == 0)

    mt = m1.transpose()
    check('GF2Matrix transpose shape', mt.nrows == 3 and mt.ncols == 3)

    m_prod = m_id * m_id
    check('GF2Matrix mul identity', m_prod.rows == [[1, 0], [0, 1]])

    # ── DuckSieve / CoveringFamily ──
    print('\nDuckSieve / CoveringFamily:')
    s_int = DuckSieve('n', frozenset({'int'}), frozenset({'sub', 'mul'}), True)
    check('sieve not trivial', not s_int.is_trivial)
    check('sieve fiber_count', s_int.fiber_count == 1)
    check('contains_tag', s_int.contains_tag('int'))
    check('not contains_tag', not s_int.contains_tag('str'))

    s_triv = DuckSieve.trivial('x')
    check('trivial sieve', s_triv.is_trivial)
    check('trivial fiber_count', s_triv.fiber_count == 6)

    s_str = DuckSieve('n', frozenset({'str', 'int'}), frozenset({'add'}), False)
    s_meet = s_int.intersect(s_str)
    check('sieve intersect', s_meet.tags == frozenset({'int'}))
    check('sieve intersect tight', s_meet.is_tight)

    s_from = DuckSieve.from_tag_and_ops('p', 'collection', False,
                                        frozenset({'iter'}))
    check('from_tag_and_ops collection',
          s_from.tags == frozenset({'pair', 'ref', 'str'}))

    fam = CoveringFamily.from_sieves([
        DuckSieve('a', frozenset({'int', 'str'}), frozenset(), False),
        DuckSieve('b', frozenset({'int', 'bool'}), frozenset(), False),
    ])
    check('covering combos count', fam.total_fibers == 4)
    check('covering overlaps exist', len(fam.overlaps()) > 0)
    check('covering param_names', fam.param_names == ['a', 'b'])

    fam_empty = CoveringFamily.from_sieves([])
    check('empty covering', fam_empty.total_fibers == 1)

    big_sieves = [DuckSieve(f'p{i}', ALL_TYPE_TAGS, frozenset(), False)
                  for i in range(4)]
    big_fam = CoveringFamily.from_sieves(big_sieves, max_fibers=12)
    check('covering capped', big_fam.capped)
    check('covering max fibers', big_fam.total_fibers <= 12)

    # ── IsomorphismSheaf ──
    print('\nIsomorphismSheaf:')
    j_eq = LocalJudgment(('int',), True, explanation='sections agree')
    j_neq = LocalJudgment(('str',), False, counterexample='str:abc')
    j_unk = LocalJudgment(('bool',), None, explanation='timeout')

    sheaf_all_eq = IsomorphismSheaf({
        ('int',): LocalJudgment(('int',), True),
        ('str',): LocalJudgment(('str',), True),
    })
    check('sheaf global=1', sheaf_all_eq.global_section() == 1)
    check('sheaf coverage', sheaf_all_eq.coverage() == 1.0)
    check('sheaf eq fibers', len(sheaf_all_eq.equivalent_fibers()) == 2)

    sheaf_mixed = IsomorphismSheaf({
        ('int',): j_eq,
        ('str',): j_neq,
        ('bool',): j_unk,
    })
    check('sheaf global=0 with obstruction',
          sheaf_mixed.global_section() == 0)
    check('sheaf obstruction fibers',
          sheaf_mixed.obstruction_fibers() == [('str',)])
    check('sheaf unknown fibers',
          sheaf_mixed.unknown_fibers() == [('bool',)])
    check('sheaf section(int)=1', sheaf_mixed.section(('int',)) == 1)
    check('sheaf section(str)=0', sheaf_mixed.section(('str',)) == 0)
    check('sheaf section(bool)=None',
          sheaf_mixed.section(('bool',)) is None)

    c0 = sheaf_mixed.as_0_cochain()
    check('as_0_cochain type', isinstance(c0, GF2Vector))
    check('as_0_cochain dim', c0.dim == 3)

    sheaf_empty = IsomorphismSheaf({})
    check('empty sheaf global=None', sheaf_empty.global_section() is None)
    check('empty sheaf coverage=0', sheaf_empty.coverage() == 0.0)

    # ── Fiber pruning ──
    print('\nFiber pruning:')
    sieve_agnostic = DuckSieve('x', ALL_TYPE_TAGS, frozenset({'eq'}), False)
    fam_ag = CoveringFamily.from_sieves([sieve_agnostic])
    pruned_ag, reports_ag = prune_irrelevant_fibers(
        fam_ag, {'x': frozenset({'eq'})})
    check('pruning reduces fibers',
          pruned_ag.total_fibers < fam_ag.total_fibers)
    check('pruning keeps at least 1', pruned_ag.total_fibers >= 1)
    check('pruning reports all fibers',
          len(reports_ag) == fam_ag.total_fibers)

    sieve_numeric = DuckSieve('n', frozenset({'int'}),
                              frozenset({'mul'}), True)
    fam_num = CoveringFamily.from_sieves([sieve_numeric])
    pruned_num, _ = prune_irrelevant_fibers(
        fam_num, {'n': frozenset({'mul'})})
    check('numeric not pruned',
          pruned_num.total_fibers == fam_num.total_fibers)

    # ── CechComplex ──
    print('\nCechComplex:')
    fibers_3 = [('int',), ('str',), ('pair',)]
    overlaps_3 = [(('int',), ('str',)), (('str',), ('pair',))]
    cx3 = CechComplex.build(fibers_3, overlaps_3)
    h1_result = cx3.compute_h1()
    check('cech h1=0 (no obstruction)', h1_result.h1 == 0)
    check('cech dim_c0', h1_result.dim_c0 == 3)
    check('cech dim_c1', h1_result.dim_c1 == 2)
    check('cech euler', h1_result.euler_characteristic == 3)
    check('cech is_trivial', h1_result.is_trivial)

    fibers_2 = [('int',), ('str',)]
    cx2 = CechComplex.build(fibers_2, [])
    h1_2 = cx2.compute_h1()
    check('cech no overlaps h1=0', h1_2.h1 == 0)

    cx1 = CechComplex.build([('int',)], [])
    check('cech single fiber', cx1.compute_h1().h1 == 0)

    overlaps_tri = [
        (('int',), ('str',)),
        (('str',), ('pair',)),
        (('int',), ('pair',)),
    ]
    cx_tri = CechComplex.build(fibers_3, overlaps_tri)
    h1_tri = cx_tri.compute_h1()
    check('cech triangle h1', h1_tri.h1 == 0)
    check('cech triangle dim_c2 > 0', h1_tri.dim_c2 > 0)

    kb = cx3.kernel_basis_delta0()
    check('kernel basis exists', isinstance(kb, list))

    # ── Covering minimization ──
    print('\nCovering minimization:')
    fam_dup = CoveringFamily(
        sieves=[],
        combos=[('int',), ('int',), ('str',), ('str',), ('bool',)],
    )
    mini = minimize_covering(fam_dup)
    check('dedup removes duplicates', mini.total_fibers == 3)

    j_proven = {
        ('int',): LocalJudgment(('int',), True),
        ('str',): LocalJudgment(('str',), True),
        ('bool',): LocalJudgment(('bool',), None),
    }
    fam_3 = CoveringFamily(
        sieves=[], combos=[('int',), ('str',), ('bool',)])
    mini_j = minimize_covering(fam_3, j_proven)
    check('minimization with judgments', mini_j.total_fibers >= 1)

    # ── OverlapCache ──
    print('\nOverlapCache:')
    cache = OverlapCache(max_entries=4)
    cx_a = cache.get_or_build(fibers_3, overlaps_3)
    cx_b = cache.get_or_build(fibers_3, overlaps_3)
    check('cache hit', cx_a is cx_b)
    check('cache stats hits=1', cache.stats()['hits'] == 1)
    check('cache stats misses=1', cache.stats()['misses'] == 1)

    cx_c = cache.get_or_build(fibers_2, [])
    check('cache miss on different input', cx_c is not cx_a)
    check('cache stats misses=2', cache.stats()['misses'] == 2)

    for i in range(10):
        cache.get_or_build([(f'tag{i}',)], [])
    check('cache max entries', cache.stats()['entries'] <= 4)

    cache.invalidate()
    check('cache invalidate', cache.stats()['entries'] == 0)

    # ── Enhanced pipeline integration ──
    print('\nEnhanced pipeline:')
    all_judgments = {
        ('int',): LocalJudgment(('int',), True),
        ('str',): LocalJudgment(('str',), True),
        ('pair',): LocalJudgment(('pair',), True),
    }
    cohom, sheaf = compute_enhanced_cech(all_judgments, overlaps_3)
    check('enhanced h1=0', cohom.is_trivial)
    check('enhanced sheaf global=1', sheaf.global_section() == 1)

    # With an obstruction
    bad_judgments = {
        ('int',): LocalJudgment(('int',), True),
        ('str',): LocalJudgment(('str',), False, counterexample='x'),
    }
    cohom_bad, sheaf_bad = compute_enhanced_cech(bad_judgments, overlaps_3)
    check('enhanced with obstruction sheaf global=0',
          sheaf_bad.global_section() == 0)

    # ── Summary ──
    print(f'\n{"═" * 50}')
    print(f'Results: {counts["passed"]} passed, {counts["failed"]} failed')
    if counts['failed']:
        sys.exit(1)
    else:
        print('All tests passed ✓')
        sys.exit(0)


if __name__ == '__main__':
    _run_self_tests()
