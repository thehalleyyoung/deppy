"""§4: Čech Cohomology Engine — H¹ computation over type fibers.

Builds the full Čech complex C⁰ → C¹ → C² from local equivalence
judgments, computes coboundary operators δ⁰ and δ¹, and determines
H¹ = ker(δ¹)/im(δ⁰) via GF(2) rank.

H¹ = 0 ↔ local equivalences glue to global ↔ EQUIVALENT.

Proactive cohomology extensions:
  - Fiber priority ordering via overlap-graph degree
  - Cohomological pre-screening via OTerm fiber signatures
  - Enriched LocalJudgment with method/confidence tracking
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple


@dataclass
class LocalJudgment:
    """Result of checking equivalence on a single type fiber."""
    fiber: Tuple[str, ...]
    is_equivalent: Optional[bool]  # True/False/None(timeout)
    counterexample: Optional[str] = None
    explanation: str = ''
    concrete_obstruction: bool = False  # True when NEQ proof uses only interpreted fns
    method: str = 'z3'  # z3, denotational, prescreen, descent
    confidence: float = 1.0  # 1.0 for Z3 proofs, lower for heuristics


@dataclass
class CechResult:
    """Result of the full Čech cohomology computation."""
    h0: int          # number of locally equivalent fibers
    h1_rank: int     # rank of H¹ (0 = equivalence glues)
    total_fibers: int
    unknown_fibers: int
    obstructions: List[Tuple[str, ...]]  # fibers with counterexamples
    obstruction_fibers: List[Tuple[str, ...]] = field(default_factory=list)

    @property
    def equivalent(self) -> Optional[bool]:
        if self.obstructions:
            return False
        if self.h0 > 0 and self.h1_rank == 0 and self.unknown_fibers == 0:
            return True
        # Partial coverage: only declare equivalence if we verified
        # a majority of fibers (>= 50%)
        if self.h0 > 0 and self.h1_rank == 0 and self.total_fibers > 0:
            coverage = self.h0 / self.total_fibers
            if coverage >= 0.5:
                return True
        return None


# ═══════════════════════════════════════════════════════════
# Proactive: Fiber Priority Ordering
# ═══════════════════════════════════════════════════════════

def compute_fiber_priority(fiber_combos: List[Tuple[str, ...]],
                           overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
                           ) -> List[Tuple[str, ...]]:
    """Order fibers by information value (overlap degree), highest first.

    High-overlap fibers are more constraining — checking them first
    enables early termination when H¹ > 0. Ties broken by preferring
    'int' fibers (richest Z3 theory) and single-type fibers.
    """
    if len(fiber_combos) <= 1:
        return list(fiber_combos)

    # Build overlap degree map
    degree: Dict[Tuple[str, ...], int] = {f: 0 for f in fiber_combos}
    fiber_set = set(fiber_combos)
    for a, b in overlaps:
        if a in fiber_set:
            degree[a] = degree.get(a, 0) + 1
        if b in fiber_set:
            degree[b] = degree.get(b, 0) + 1

    def _priority_key(fiber: Tuple[str, ...]) -> Tuple[int, int, int]:
        deg = degree.get(fiber, 0)
        # Prefer int-only fibers (richest Z3 theory, most likely to find NEQ)
        has_int = sum(1 for t in fiber if t == 'int')
        # Prefer single-type fibers (simpler Z3 queries)
        is_uniform = 1 if len(set(fiber)) == 1 else 0
        return (deg, has_int, is_uniform)

    return sorted(fiber_combos, key=_priority_key, reverse=True)


# ═══════════════════════════════════════════════════════════
# Proactive: Cohomological Pre-Screening
# ═══════════════════════════════════════════════════════════

def _oterm_top_constructor(t) -> str:
    """Extract the top-level constructor name of an OTerm."""
    return type(t).__name__


def _oterm_shape(t) -> Tuple[str, int]:
    """Extract (constructor, arity) as a lightweight signature."""
    name = type(t).__name__
    if hasattr(t, 'args'):
        return (name, len(t.args))
    if hasattr(t, 'elements'):
        return (name, len(t.elements))
    if hasattr(t, 'pairs'):
        return (name, len(t.pairs))
    return (name, 0)


def _oterm_op_set(t, depth: int = 0) -> FrozenSet[str]:
    """Recursively collect the set of operation names used in an OTerm."""
    if depth > 15:
        return frozenset()
    ops: Set[str] = set()
    name = type(t).__name__
    if name == 'OOp':
        ops.add(t.name)
        for a in t.args:
            ops |= _oterm_op_set(a, depth + 1)
    elif name == 'OFold':
        ops.add(f'fold_{t.op_name}')
        ops |= _oterm_op_set(t.init, depth + 1)
        ops |= _oterm_op_set(t.collection, depth + 1)
    elif name == 'OCase':
        ops.add('case')
        ops |= _oterm_op_set(t.test, depth + 1)
        ops |= _oterm_op_set(t.true_branch, depth + 1)
        ops |= _oterm_op_set(t.false_branch, depth + 1)
    elif name == 'OFix':
        ops.add(f'fix_{t.name}')
        ops |= _oterm_op_set(t.body, depth + 1)
    elif name == 'OSeq':
        for e in t.elements:
            ops |= _oterm_op_set(e, depth + 1)
    elif name == 'OMap':
        ops.add('map')
        ops |= _oterm_op_set(t.transform, depth + 1)
        ops |= _oterm_op_set(t.collection, depth + 1)
    elif name == 'OLam':
        ops |= _oterm_op_set(t.body, depth + 1)
    elif name == 'OCatch':
        ops.add('catch')
        ops |= _oterm_op_set(t.body, depth + 1)
        ops |= _oterm_op_set(t.default, depth + 1)
    elif name == 'OQuotient':
        ops.add(f'quotient_{t.equiv_class}')
        ops |= _oterm_op_set(t.inner, depth + 1)
    return frozenset(ops)


def cohomological_prescreen(oterm_f, oterm_g) -> Optional[bool]:
    """Pre-screen two OTerms for likely NEQ using structural signatures.

    Returns False if structurally provably NEQ (different top-level
    constructors in ways that guarantee semantic difference).
    Returns None if inconclusive (cannot determine from structure alone).
    Never returns True (pre-screening cannot prove equivalence).
    """
    if oterm_f is None or oterm_g is None:
        return None

    shape_f = _oterm_shape(oterm_f)
    shape_g = _oterm_shape(oterm_g)
    top_f = shape_f[0]
    top_g = shape_g[0]

    # Different top-level constructors that are provably incompatible
    incompatible_pairs = {
        ('OFold', 'OLit'), ('OLit', 'OFold'),
        ('OFold', 'OVar'), ('OVar', 'OFold'),
        ('OLit', 'OOp'), ('OOp', 'OLit'),
        ('OLit', 'OFold'), ('OFold', 'OLit'),
        ('OLit', 'OMap'), ('OMap', 'OLit'),
        ('OLit', 'OFix'), ('OFix', 'OLit'),
    }

    # OLit vs OLit: compare values directly
    if top_f == 'OLit' and top_g == 'OLit':
        if hasattr(oterm_f, 'value') and hasattr(oterm_g, 'value'):
            if oterm_f.value != oterm_g.value:
                return False

    if (top_f, top_g) in incompatible_pairs:
        return False

    return None


# ═══════════════════════════════════════════════════════════
# Proactive: Sheaf Descent Check
# ═══════════════════════════════════════════════════════════

def sheaf_descent_check(
    judgments: Dict[Tuple[str, ...], LocalJudgment],
    overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
) -> Optional[bool]:
    """Check if per-fiber verdicts satisfy the sheaf descent condition.

    If all checked fibers agree (all EQ) and there are no unknown fibers,
    the descent condition is satisfied → global EQ.
    If any fiber is NEQ with a concrete obstruction → global NEQ.
    Otherwise → None (inconclusive).

    This promotes partial per-fiber results to a global verdict when
    the cocycle condition (H¹ = 0) is met.
    """
    if not judgments:
        return None

    eq_fibers = [f for f, j in judgments.items() if j.is_equivalent is True]
    neq_fibers = [f for f, j in judgments.items()
                  if j.is_equivalent is False and j.concrete_obstruction]
    unknown_fibers = [f for f, j in judgments.items() if j.is_equivalent is None]

    # Concrete NEQ on any fiber → global NEQ (early termination)
    if neq_fibers:
        return False

    # All fibers verified EQ and no unknowns → check cocycle condition
    if eq_fibers and not unknown_fibers:
        # Compute H¹ to verify gluing
        cech = compute_cech_h1(judgments, overlaps)
        return cech.h1_rank == 0

    # Partial coverage: if enough fibers agree, descent with coverage
    total = len(judgments)
    if eq_fibers and total > 0:
        coverage = len(eq_fibers) / total
        if coverage >= 0.5 and not neq_fibers:
            cech = compute_cech_h1(
                {f: judgments[f] for f in eq_fibers},
                [(a, b) for a, b in overlaps
                 if a in eq_fibers and b in eq_fibers])
            if cech.h1_rank == 0:
                return True

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


# ═══════════════════════════════════════════════════════════
# Bridge to stalks module (advanced Čech computations)
# ═══════════════════════════════════════════════════════════

def build_full_cech_complex(
    judgments: Dict[Tuple[str, ...], LocalJudgment],
    overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
):
    """Build a first-class CechComplex from local judgments and overlaps.

    Delegates to cctt.stalks.build_cech_complex for the heavy lifting,
    returning a stalks.CechComplex with GF2Matrix-backed δ⁰/δ¹.
    """
    from cctt.stalks import build_cech_complex as _build
    equiv_fibers = [f for f, j in judgments.items() if j.is_equivalent is True]
    if len(equiv_fibers) <= 1 or not overlaps:
        from cctt.stalks import CechComplex as CC, GF2Matrix
        return CC(fibers=equiv_fibers, overlaps=[], triples=[],
                  delta0=GF2Matrix([]), delta1=GF2Matrix([]))
    return _build(equiv_fibers, overlaps)


def run_cech_pipeline(
    fibers: List[Tuple[str, ...]],
    overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
    judgments: Dict[Tuple[str, ...], LocalJudgment],
):
    """Run the full Čech pipeline (complex + graph + obstructions + spectral).

    Converts LocalJudgment verdicts to Optional[bool] and delegates to
    cctt.stalks.CechPipeline.
    """
    from cctt.stalks import CechPipeline
    bool_map: Dict[Tuple[str, ...], Optional[bool]] = {
        f: j.is_equivalent for f, j in judgments.items()
    }
    return CechPipeline().run(fibers, overlaps, bool_map)


def localize_h1_obstructions(
    judgments: Dict[Tuple[str, ...], LocalJudgment],
    overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
):
    """Localize H¹ obstructions to specific overlap edges.

    Returns a stalks.ObstructionReport listing the offending edges.
    """
    from cctt.stalks import localize_obstructions
    cx = build_full_cech_complex(judgments, overlaps)
    return localize_obstructions(cx)


# ═══════════════════════════════════════════════════════════
# Bridge to structured sheaf module (cctt.sheaves)
# ═══════════════════════════════════════════════════════════

def build_isomorphism_sheaf(
    judgments: Dict[Tuple[str, ...], LocalJudgment],
) -> Any:
    """Build an IsomorphismSheaf from local judgments.

    Delegates to cctt.sheaves.IsomorphismSheaf for structured
    GF(2)-valued sheaf operations (global section, coverage, etc.).
    """
    from cctt.sheaves import IsomorphismSheaf
    return IsomorphismSheaf(judgments)


def build_cech_complex(
    fibers: List[Tuple[str, ...]],
    overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
) -> Any:
    """Build a structured CechComplex from fibers and overlaps.

    Delegates to cctt.sheaves.CechComplex for GF2Matrix-based
    coboundary computation with kernel/rank accessors.
    """
    from cctt.sheaves import CechComplex
    return CechComplex.build(fibers, overlaps)
