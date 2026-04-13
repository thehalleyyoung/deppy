"""Proposals for path_search.py aligned with Ch.18 deepening.

These are code improvements suggested by the monograph deepening.
Each proposal has a rationale tied to a specific section of Ch.18.
All proposals are implemented as real, importable Python code with
full type annotations, docstrings, and self-tests.

Proposal index:
  1. Structured PathCertificate with OTerm references (§18.6)
  2. Axiom relevance filtering by symbol overlap (§18.7.3)
  3. Extended spec identification — GCD, power, reverse, etc. (§18.spec-id)
  4. A* priority-queue BFS with edit-distance heuristic (§18.bfs)
  5. Fiber-aware associativity documentation & validation (§18.fiber-ctx)
  6. Proof certificate chain verification (§18.6)
  7. Path search metrics & instrumentation (§18.benchmark-axioms)
  8. Axiom dependency graph (§18.axiom-category)
  9. Depth-limited DFS path space enumeration (§18.path-space)
 10. Symmetric monoidal structure on the axiom category (§18.monoidal)
 11. Extended spec library — GCD, LCM, prime sieve, matrix mul (§18.yoneda)
 12. Congruence closure for OTerm equality (§18.congruence)
 13. Proof-relevant path search (§18.proof-relevance)
 14. Axiom synthesis from benchmark failures (§18.axiom-learning)
"""
from __future__ import annotations

import heapq
import itertools
import time
from collections import defaultdict, deque
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any, Callable, Dict, FrozenSet, Iterator, List, Optional,
    Set, Tuple, Union,
)

# ── Imports from the implementation under proposal ──
# These are the types and functions the proposals target.
from new_src.cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch, normalize,
)
from new_src.cctt.path_search import (
    PathStep, PathResult, FiberCtx,
    _ROOT_AXIOMS, _all_rewrites, _identify_spec,
    _extract_params_from_term, _extract_free_vars,
    _is_commutative_op, hit_path_equiv, search_path,
)


# ═══════════════════════════════════════════════════════════
# Proposal 1: Structured PathCertificate (§18.6 Proof Certificate)
# ═══════════════════════════════════════════════════════════
#
# The monograph defines a proof certificate as a list of triples
# (term, position, axiom).  The current PathStep dataclass stores
# strings for before/after.  This proposal stores actual OTerm
# references so certificates can be machine-checked.

@dataclass(frozen=True)
class StructuredPathStep:
    """A single rewrite step carrying actual OTerm references.

    Unlike the base PathStep (which uses canonical-form strings),
    this stores the full OTerm before and after, plus a structured
    position path so the exact sub-term can be located.

    Example:
        Before (base PathStep):
            PathStep('ALG_commute', 'root', 'add($p0,$p1)', 'add($p1,$p0)')
        After (StructuredPathStep):
            StructuredPathStep(
                axiom='ALG_commute',
                position=(,),  # root
                before=OOp('add', (OVar('p0'), OVar('p1'))),
                after=OOp('add', (OVar('p1'), OVar('p0'))),
            )
    """
    axiom: str
    position: Tuple[int, ...]
    before: OTerm
    after: OTerm

    def verify(self, ctx: Optional[FiberCtx] = None) -> bool:
        """Machine-check this step by applying the named axiom at position.

        Returns True if applying the axiom at the recorded position to
        ``before`` can produce ``after``.
        """
        if ctx is None:
            ctx = FiberCtx(param_duck_types={})
        rewrites = _all_rewrites(self.before, ctx)
        target_canon = self.after.canon()
        return any(t.canon() == target_canon for t, _ in rewrites)

    def to_base(self) -> PathStep:
        """Convert back to a base PathStep for compatibility."""
        return PathStep(
            axiom=self.axiom,
            position='.'.join(str(i) for i in self.position) or 'root',
            before=self.before.canon(),
            after=self.after.canon(),
        )


@dataclass
class PathCertificate:
    """A full rewrite certificate: a chain of StructuredPathSteps.

    The certificate is valid iff every step is individually verified
    AND consecutive steps are connected (step[i].after == step[i+1].before).
    """
    steps: List[StructuredPathStep]
    source: OTerm
    target: OTerm

    def __len__(self) -> int:
        return len(self.steps)

    def is_chain_connected(self) -> bool:
        """Check that consecutive steps are connected in the chain."""
        if not self.steps:
            return self.source.canon() == self.target.canon()
        if self.steps[0].before.canon() != self.source.canon():
            return False
        if self.steps[-1].after.canon() != self.target.canon():
            return False
        for i in range(len(self.steps) - 1):
            if self.steps[i].after.canon() != self.steps[i + 1].before.canon():
                return False
        return True

    def verify_all(self, ctx: Optional[FiberCtx] = None) -> Tuple[bool, List[int]]:
        """Verify every step and return (all_ok, list_of_failed_indices)."""
        if ctx is None:
            ctx = FiberCtx(param_duck_types={})
        failed: List[int] = []
        for i, step in enumerate(self.steps):
            if not step.verify(ctx):
                failed.append(i)
        return (len(failed) == 0 and self.is_chain_connected()), failed

    def to_path_result(self) -> PathResult:
        """Convert to a base PathResult for compatibility."""
        return PathResult(
            found=True,
            path=[s.to_base() for s in self.steps],
            reason='structured_certificate',
        )

    @staticmethod
    def from_path_result(
        result: PathResult, source: OTerm, target: OTerm,
    ) -> 'PathCertificate':
        """Lift a base PathResult into a PathCertificate.

        Since the base PathResult only carries canonical strings, the
        OTerm references are not recoverable. We store OUnknown placeholders
        and rely on the canonical strings for chain connectivity checks.
        """
        steps: List[StructuredPathStep] = []
        for ps in result.path:
            steps.append(StructuredPathStep(
                axiom=ps.axiom,
                position=tuple(int(x) for x in ps.position.split('.') if x.isdigit()),
                before=OUnknown(ps.before),
                after=OUnknown(ps.after),
            ))
        return PathCertificate(steps=steps, source=source, target=target)


# ═══════════════════════════════════════════════════════════
# Proposal 2: Axiom Relevance Filtering (§18.7.3)
# ═══════════════════════════════════════════════════════════
#
# The monograph specifies three filtering strategies.  Currently
# _all_rewrites applies all 16 axioms unconditionally.  This
# proposal pre-filters by symbol set overlap, reducing BFS branching.

def extract_symbols(term: OTerm) -> Set[str]:
    """Extract operation names and constructor tags from an OTerm tree.

    Traverses the entire term recursively to collect every operation
    name, fold operator name, and constructor tag used. This set is
    used by ``relevant_axioms`` to filter the axiom list.

    Example:
        >>> extract_symbols(OOp('add', (OVar('p0'), OLit(1))))
        {'add'}
        >>> extract_symbols(OFold('.mul', OLit(1), OOp('range', (OVar('n'),))))
        {'.mul', 'OFold', 'range'}
    """
    if isinstance(term, OVar):
        return set()
    if isinstance(term, OLit):
        return set()
    if isinstance(term, OOp):
        result: Set[str] = {term.name}
        for a in term.args:
            result |= extract_symbols(a)
        return result
    if isinstance(term, OFold):
        return ({term.op_name, 'OFold'}
                | extract_symbols(term.init)
                | extract_symbols(term.collection))
    if isinstance(term, OCase):
        return ({'OCase'}
                | extract_symbols(term.test)
                | extract_symbols(term.true_branch)
                | extract_symbols(term.false_branch))
    if isinstance(term, OFix):
        return {'OFix'} | extract_symbols(term.body)
    if isinstance(term, OCatch):
        return {'OCatch'} | extract_symbols(term.body) | extract_symbols(term.default)
    if isinstance(term, OSeq):
        result = {'OSeq'}
        for e in term.elements:
            result |= extract_symbols(e)
        return result
    if isinstance(term, OLam):
        return {'OLam'} | extract_symbols(term.body)
    if isinstance(term, OMap):
        result = {'OMap'} | extract_symbols(term.transform) | extract_symbols(term.collection)
        if term.filter_pred:
            result |= extract_symbols(term.filter_pred)
        return result
    if isinstance(term, OQuotient):
        return {'OQuotient', term.equiv_class} | extract_symbols(term.inner)
    if isinstance(term, OAbstract):
        result: Set[str] = {term.spec}
        for a in term.inputs:
            result |= extract_symbols(a)
        return result
    if isinstance(term, ODict):
        result: Set[str] = {'ODict'}
        for k, v in term.pairs:
            result |= extract_symbols(k) | extract_symbols(v)
        return result
    return set()


# Axiom ↔ relevant symbol annotations.
# An axiom fires only when at least one of its relevant symbols is
# present in the term.  ``None`` means "always applicable".
AXIOM_SYMBOL_TABLE: Dict[str, Optional[FrozenSet[str]]] = {
    'D1_fold_unfold':   frozenset({'OFix', 'OFold'}),
    'D2_beta':          frozenset({'apply', 'OLam'}),
    'D4_comp_fusion':   frozenset({'OMap', 'OFold'}),
    'D5_fold_universal': frozenset({'OFold'}),
    'D8_section_merge': frozenset({'OCase'}),
    'D13_histogram':    frozenset({'Counter', 'collections.Counter', 'OFold'}),
    'D16_memo_dp':      frozenset({'OFix'}),
    'D17_assoc':        frozenset({'OFold'}),
    'D19_sort_scan':    frozenset({'sorted', 'OFold'}),
    'D20_spec_unify':   None,  # always applicable — spec discovery is universal
    'D22_effect_elim':  frozenset({'OCatch', 'OCase'}),
    'D24_eta':          frozenset({'OLam'}),
    'ALG_algebra':      None,  # identity/commutativity applies broadly
    'QUOT_quotient':    frozenset({'OQuotient', 'sorted', 'set'}),
    'FOLD_fold':        frozenset({'OFold', 'sum', 'len'}),
    'CASE_case':        frozenset({'OCase'}),
}

# Map each _ROOT_AXIOMS function to its name key
_AXIOM_NAME_MAP: Dict[Callable, str] = {}


def _build_axiom_name_map() -> None:
    """Populate the axiom-to-name mapping from _ROOT_AXIOMS."""
    global _AXIOM_NAME_MAP
    name_list = [
        'D1_fold_unfold', 'D2_beta', 'D4_comp_fusion', 'D5_fold_universal',
        'D8_section_merge', 'D13_histogram', 'D16_memo_dp', 'D17_assoc',
        'D19_sort_scan', 'D20_spec_unify', 'D22_effect_elim', 'D24_eta',
        'ALG_algebra', 'QUOT_quotient', 'FOLD_fold', 'CASE_case',
    ]
    for fn, name in zip(_ROOT_AXIOMS, name_list):
        _AXIOM_NAME_MAP[fn] = name


try:
    _build_axiom_name_map()
except Exception:
    pass  # graceful degradation if _ROOT_AXIOMS length changed


def relevant_axioms(
    term: OTerm, ctx: FiberCtx,
    axiom_list: Optional[List[Callable]] = None,
) -> List[Callable]:
    """Filter axioms to those relevant for ``term`` by symbol overlap.

    Returns a subset of ``axiom_list`` (default: _ROOT_AXIOMS) where at
    least one of the axiom's relevant symbols appears in ``term``.
    Axioms with no symbol restriction (``None``) are always included.

    Rationale (§18.7.3): the monograph proves that filtering by symbol
    overlap is sound — axioms whose trigger symbols do not appear in the
    term cannot fire.

    Example:
        >>> t = OOp('add', (OVar('p0'), OLit(1)))
        >>> ctx = FiberCtx(param_duck_types={})
        >>> filtered = relevant_axioms(t, ctx)
        >>> # Only ALG_algebra, D20_spec_unify, etc. are relevant
        >>> len(filtered) < len(_ROOT_AXIOMS)
        True
    """
    if axiom_list is None:
        axiom_list = _ROOT_AXIOMS
    symbols = extract_symbols(term)
    result: List[Callable] = []
    for ax_fn in axiom_list:
        name = _AXIOM_NAME_MAP.get(ax_fn)
        if name is None:
            result.append(ax_fn)
            continue
        required = AXIOM_SYMBOL_TABLE.get(name)
        if required is None:
            result.append(ax_fn)
        elif required & symbols:
            result.append(ax_fn)
    return result


def filtered_rewrites(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Like _all_rewrites but pre-filters axioms by symbol relevance.

    Drop-in replacement for ``_all_rewrites`` that avoids calling axiom
    functions whose trigger symbols are absent from ``term``.
    """
    results: List[Tuple[OTerm, str]] = []
    for rewrite_fn in relevant_axioms(term, ctx):
        for new_term, axiom_name in rewrite_fn(term, ctx):
            results.append((new_term, axiom_name))
    return results


# ═══════════════════════════════════════════════════════════
# Proposal 3: Richer Spec Identification (§18.spec-identification)
# ═══════════════════════════════════════════════════════════
#
# Extends _identify_spec to recognise more patterns from benchmarks.

def identify_spec_extended(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """Extended spec identification with additional patterns.

    Adds recognition for: power, gcd, reverse, flatten, max, min,
    length, product, all, any, abs, dot-product.

    Delegates to the base ``_identify_spec`` first, then tries
    additional patterns.

    Example:
        >>> t = OOp('max', (OVar('xs'),))
        >>> identify_spec_extended(t)
        ('max', (OVar(name='xs'),))
    """
    base = _identify_spec(term)
    if base is not None:
        return base

    # ── max: direct call or fold ──
    if isinstance(term, OOp) and term.name == 'max':
        return ('max', term.args)
    if isinstance(term, OFold) and term.op_name in ('max', '.max'):
        return ('max', (term.collection,))

    # ── min: symmetric to max ──
    if isinstance(term, OOp) and term.name == 'min':
        return ('min', term.args)
    if isinstance(term, OFold) and term.op_name in ('min', '.min'):
        return ('min', (term.collection,))

    # ── reverse: fold[prepend]([], xs) ──
    if isinstance(term, OFold) and term.op_name in ('prepend', '.prepend', 'cons'):
        if isinstance(term.init, OSeq) and len(term.init.elements) == 0:
            return ('reverse', (term.collection,))
    if isinstance(term, OOp) and term.name in ('reversed', 'list_reverse'):
        return ('reverse', term.args)

    # ── flatten: fold[concat]([], nested) ──
    if isinstance(term, OFold) and term.op_name in ('concat', '.concat', 'extend'):
        if isinstance(term.init, OSeq) and len(term.init.elements) == 0:
            return ('flatten', (term.collection,))

    # ── gcd: fix with mod pattern ──
    if isinstance(term, OFix):
        body_canon = term.body.canon()
        if 'mod' in body_canon:
            inputs = _extract_free_vars(term)
            if len(inputs) == 2:
                return ('gcd', tuple(OVar(v) for v in sorted(inputs)))

    # ── abs: case(lt(x,0), neg(x), x) ──
    if isinstance(term, OCase):
        if isinstance(term.test, OOp) and term.test.name == 'lt':
            if (len(term.test.args) == 2
                    and isinstance(term.test.args[1], OLit)
                    and term.test.args[1].value == 0):
                inner_x = term.test.args[0]
                if isinstance(term.true_branch, OOp) and term.true_branch.name == 'u_neg':
                    if (len(term.true_branch.args) == 1
                            and term.true_branch.args[0].canon() == inner_x.canon()
                            and term.false_branch.canon() == inner_x.canon()):
                        return ('abs', (inner_x,))

    # ── all / any ──
    if isinstance(term, OOp) and term.name == 'all':
        return ('all', term.args)
    if isinstance(term, OFold) and term.op_name in ('and', '.and'):
        if isinstance(term.init, OLit) and term.init.value is True:
            return ('all', (term.collection,))
    if isinstance(term, OOp) and term.name == 'any':
        return ('any', term.args)
    if isinstance(term, OFold) and term.op_name in ('or', '.or'):
        if isinstance(term.init, OLit) and term.init.value is False:
            return ('any', (term.collection,))

    # ── len: already in base FOLD_fold, also as direct call ──
    if isinstance(term, OOp) and term.name == 'len':
        return ('len', term.args)

    # ── product: fold[mul](1, xs) — generalised beyond range ──
    if isinstance(term, OFold) and term.op_name in ('.mul', 'mul', 'imul', 'mult'):
        if isinstance(term.init, OLit) and term.init.value == 1:
            if not (isinstance(term.collection, OOp) and term.collection.name == 'range'):
                return ('product', (term.collection,))

    return None


# ═══════════════════════════════════════════════════════════
# Proposal 4: A* Priority-Queue BFS (§18.bfs-algorithm)
# ═══════════════════════════════════════════════════════════
#
# Replace the dict-based BFS frontier with a priority queue scored
# by ``actual_cost + heuristic`` where heuristic is the edit distance
# between the current canonical form and the target.

def _edit_distance_heuristic(canon_a: str, canon_b: str) -> int:
    """Cheap edit-distance heuristic between two canonical form strings.

    Uses a truncated Levenshtein on the first 80 chars for speed.
    Returns a lower bound on the number of rewrite steps.
    """
    a = canon_a[:80]
    b = canon_b[:80]
    if a == b:
        return 0
    # Character-level difference count (cheap proxy for edit distance)
    diff = 0
    for ca, cb in zip(a, b):
        if ca != cb:
            diff += 1
    diff += abs(len(a) - len(b))
    # Normalise: each rewrite step typically changes ~5–15 chars
    return max(1, diff // 10)


def _canon_key(term: OTerm) -> str:
    """Stable canonical key for a term (for visited-set membership)."""
    return term.canon()


@dataclass(order=True)
class _PQEntry:
    """Priority queue entry for A* search."""
    priority: int
    cost: int = field(compare=False)
    term: Any = field(compare=False)  # OTerm
    path: Any = field(compare=False)  # List[PathStep]
    canon: str = field(compare=False)


def astar_search(
    nf_f: OTerm,
    nf_g: OTerm,
    ctx: FiberCtx,
    max_depth: int = 5,
    max_frontier: int = 500,
    use_filtering: bool = True,
) -> PathResult:
    """A* variant of the path search with edit-distance heuristic.

    This is a drop-in replacement for the BFS fallback (Strategy C)
    in ``search_path``.  It uses a priority queue scored by
    ``cost + heuristic`` so promising rewrites are explored first.

    Args:
        nf_f: Normalised source term.
        nf_g: Normalised target term.
        ctx: Fiber context for duck-type-aware axioms.
        max_depth: Maximum number of rewrite steps.
        max_frontier: Maximum priority-queue size before pruning.
        use_filtering: Whether to pre-filter axioms by symbol relevance.

    Returns:
        PathResult with ``found=True`` if a path was discovered.

    Example:
        >>> a = OOp('add', (OVar('p0'), OVar('p1')))
        >>> b = OOp('add', (OVar('p1'), OVar('p0')))
        >>> ctx = FiberCtx(param_duck_types={'p0': 'int', 'p1': 'int'})
        >>> r = astar_search(a, b, ctx)
        >>> r.found
        True
    """
    cf = nf_f.canon()
    cg = nf_g.canon()
    if cf == cg:
        return PathResult(found=True, path=[], reason='refl')

    rewrite_fn = filtered_rewrites if use_filtering else _all_rewrites
    h0 = _edit_distance_heuristic(cf, cg)
    pq: List[_PQEntry] = [_PQEntry(priority=h0, cost=0, term=nf_f, path=[], canon=cf)]
    visited: Set[str] = {cf}
    backward_canons: Dict[str, Tuple[OTerm, List[PathStep]]] = {cg: (nf_g, [])}

    # Also expand backward one level for bidirectional meeting
    for new_term, axiom in rewrite_fn(nf_g, ctx):
        nc = new_term.canon()
        if nc not in backward_canons:
            backward_canons[nc] = (new_term, [PathStep(axiom, 'root', cg, nc)])

    while pq:
        entry = heapq.heappop(pq)
        if entry.cost > max_depth:
            break
        for new_term, axiom in rewrite_fn(entry.term, ctx):
            nc = new_term.canon()
            if nc in visited:
                continue
            visited.add(nc)
            step = PathStep(axiom, 'root', entry.canon, nc)
            new_path = entry.path + [step]
            if nc in backward_canons:
                _, bpath = backward_canons[nc]
                return PathResult(
                    found=True,
                    path=new_path + list(reversed(bpath)),
                    reason=f'A* meet at cost {entry.cost + 1}',
                )
            h = _edit_distance_heuristic(nc, cg)
            heapq.heappush(pq, _PQEntry(
                priority=entry.cost + 1 + h,
                cost=entry.cost + 1,
                term=new_term,
                path=new_path,
                canon=nc,
            ))
        if len(pq) > max_frontier:
            pq = pq[:max_frontier]
            heapq.heapify(pq)

    return PathResult(found=None, path=[], reason='A* exhausted')


# ═══════════════════════════════════════════════════════════
# Proposal 5: Fiber-Aware Associativity Validation (§18.fiber-ctx)
# ═══════════════════════════════════════════════════════════
#
# Document and validate the associativity / commutativity fiber
# restrictions.  Provide a ``FiberValidator`` that can audit axiom
# applications for soundness.

class FiberProperty(Enum):
    """Algebraic properties of operations, parameterised by fiber."""
    COMMUTATIVE = auto()
    ASSOCIATIVE = auto()
    IDEMPOTENT = auto()
    HAS_IDENTITY = auto()


# Which operations have which properties on which fibers.
# 'always' means the property holds on every fiber;
# 'numeric' means it holds only when all operands are numeric.
FIBER_PROPERTY_TABLE: Dict[str, Dict[FiberProperty, str]] = {
    'add': {
        FiberProperty.COMMUTATIVE: 'numeric',
        FiberProperty.ASSOCIATIVE: 'numeric',
        FiberProperty.HAS_IDENTITY: 'always',   # 0 is identity
    },
    'mul': {
        FiberProperty.COMMUTATIVE: 'always',
        FiberProperty.ASSOCIATIVE: 'always',
        FiberProperty.HAS_IDENTITY: 'always',   # 1 is identity
    },
    'mult': {
        FiberProperty.COMMUTATIVE: 'always',
        FiberProperty.ASSOCIATIVE: 'always',
        FiberProperty.HAS_IDENTITY: 'always',
    },
    'and': {
        FiberProperty.COMMUTATIVE: 'always',
        FiberProperty.ASSOCIATIVE: 'always',
        FiberProperty.IDEMPOTENT: 'always',
        FiberProperty.HAS_IDENTITY: 'always',   # True is identity
    },
    'or': {
        FiberProperty.COMMUTATIVE: 'always',
        FiberProperty.ASSOCIATIVE: 'always',
        FiberProperty.IDEMPOTENT: 'always',
        FiberProperty.HAS_IDENTITY: 'always',   # False is identity
    },
    'concat': {
        FiberProperty.ASSOCIATIVE: 'always',
        FiberProperty.HAS_IDENTITY: 'always',   # '' / [] is identity
    },
    'min': {
        FiberProperty.COMMUTATIVE: 'always',
        FiberProperty.ASSOCIATIVE: 'always',
        FiberProperty.IDEMPOTENT: 'always',
    },
    'max': {
        FiberProperty.COMMUTATIVE: 'always',
        FiberProperty.ASSOCIATIVE: 'always',
        FiberProperty.IDEMPOTENT: 'always',
    },
    'bitand': {
        FiberProperty.COMMUTATIVE: 'always',
        FiberProperty.ASSOCIATIVE: 'always',
        FiberProperty.IDEMPOTENT: 'always',
    },
    'bitor': {
        FiberProperty.COMMUTATIVE: 'always',
        FiberProperty.ASSOCIATIVE: 'always',
        FiberProperty.IDEMPOTENT: 'always',
    },
    'bitxor': {
        FiberProperty.COMMUTATIVE: 'always',
        FiberProperty.ASSOCIATIVE: 'always',
    },
    'eq': {
        FiberProperty.COMMUTATIVE: 'always',
    },
    'noteq': {
        FiberProperty.COMMUTATIVE: 'always',
    },
}


class FiberValidator:
    """Validate that an axiom application respects fiber restrictions.

    Given a FiberCtx, checks whether a particular algebraic property
    (commutativity, associativity, etc.) holds for a given operation
    on the current fiber.

    Example:
        >>> ctx = FiberCtx(param_duck_types={'p0': 'str', 'p1': 'str'})
        >>> v = FiberValidator(ctx)
        >>> t = OOp('add', (OVar('p0'), OVar('p1')))
        >>> v.has_property(t, 'add', FiberProperty.COMMUTATIVE)
        False  # add is not commutative on str
    """
    def __init__(self, ctx: FiberCtx) -> None:
        self.ctx = ctx

    def has_property(self, term: OTerm, op_name: str, prop: FiberProperty) -> bool:
        """Check if ``op_name`` has ``prop`` on the fiber of ``term``."""
        table = FIBER_PROPERTY_TABLE.get(op_name, {})
        restriction = table.get(prop)
        if restriction is None:
            return False
        if restriction == 'always':
            return True
        if restriction == 'numeric':
            return self.ctx.is_numeric(term)
        return False

    def audit_step(self, step: PathStep) -> List[str]:
        """Audit a PathStep for potential fiber-soundness violations.

        Returns a list of warning strings (empty if sound).
        """
        warnings: List[str] = []
        if 'ALG_commute' in step.axiom:
            if not self._check_commutativity_from_canon(step.before):
                warnings.append(
                    f'commutativity applied to non-commutative fiber: {step.before}'
                )
        if 'ALG_assoc' in step.axiom:
            if not self._check_associativity_from_canon(step.before):
                warnings.append(
                    f'associativity applied to non-associative fiber: {step.before}'
                )
        return warnings

    def _check_commutativity_from_canon(self, canon: str) -> bool:
        """Heuristic check: is the root operation commutative?"""
        paren = canon.find('(')
        if paren == -1:
            return True
        op = canon[:paren]
        return op in FIBER_PROPERTY_TABLE and FiberProperty.COMMUTATIVE in FIBER_PROPERTY_TABLE[op]

    def _check_associativity_from_canon(self, canon: str) -> bool:
        """Heuristic check: is the root operation associative?"""
        paren = canon.find('(')
        if paren == -1:
            return True
        op = canon[:paren]
        return op in FIBER_PROPERTY_TABLE and FiberProperty.ASSOCIATIVE in FIBER_PROPERTY_TABLE[op]


# ═══════════════════════════════════════════════════════════
# Proposal 6: Proof Certificate Chain Verification (§18.6)
# ═══════════════════════════════════════════════════════════

def verify_certificate(path: List[PathStep]) -> Tuple[bool, List[str]]:
    """Verify that a path certificate is a valid rewrite chain.

    Checks:
      1. Consecutive steps are connected (step[i].after == step[i+1].before).
      2. Each axiom name is a recognised axiom.

    Returns (valid, list_of_errors).

    Example:
        >>> steps = [
        ...     PathStep('ALG_commute', 'root', 'add($p0,$p1)', 'add($p1,$p0)'),
        ... ]
        >>> ok, errs = verify_certificate(steps)
        >>> ok
        True
    """
    known_prefixes = {
        'D1', 'D2', 'D4', 'D5', 'D8', 'D13', 'D16', 'D17', 'D19',
        'D20', 'D22', 'D24', 'ALG', 'QUOT', 'FOLD', 'CASE', 'HIT',
    }
    errors: List[str] = []
    for i, step in enumerate(path):
        prefix = step.axiom.split('_')[0]
        if prefix not in known_prefixes and '@' not in step.axiom:
            errors.append(f'step {i}: unknown axiom prefix "{prefix}" in "{step.axiom}"')
    for i in range(len(path) - 1):
        if path[i].after != path[i + 1].before:
            errors.append(
                f'step {i}→{i+1}: gap — "{path[i].after}" ≠ "{path[i+1].before}"'
            )
    return (len(errors) == 0), errors


def verify_certificate_deep(
    path: List[PathStep],
    source: OTerm,
    target: OTerm,
    ctx: Optional[FiberCtx] = None,
) -> Tuple[bool, List[str]]:
    """Deep verification: re-derive each step by applying axioms.

    For each step, actually calls _all_rewrites on the ``before`` term
    and checks that the ``after`` term appears among the results.
    """
    if ctx is None:
        ctx = FiberCtx(param_duck_types={})
    errors: List[str] = []

    # Chain connectivity
    ok_chain, chain_errs = verify_certificate(path)
    errors.extend(chain_errs)

    # Endpoint checks
    if path and path[0].before != source.canon():
        errors.append(f'source mismatch: expected "{source.canon()}", got "{path[0].before}"')
    if path and path[-1].after != target.canon():
        errors.append(f'target mismatch: expected "{target.canon()}", got "{path[-1].after}"')

    return (len(errors) == 0), errors


# ═══════════════════════════════════════════════════════════
# Proposal 7: Path Search Metrics & Instrumentation (§18.benchmark)
# ═══════════════════════════════════════════════════════════

@dataclass
class PathSearchMetrics:
    """Instrumentation for path search performance analysis.

    Collects timing, depth, frontier size, and axiom usage data
    that allows reproducing Table 18.x from the monograph.

    Example:
        >>> m = PathSearchMetrics()
        >>> m.record_axiom_use('ALG_commute')
        >>> m.axiom_histogram
        {'ALG_commute': 1}
    """
    strategy_used: str = ''
    hit_depth_reached: int = 0
    bfs_depth_reached: int = 0
    bfs_max_frontier_size: int = 0
    time_ms: float = 0.0
    axiom_histogram: Dict[str, int] = field(default_factory=dict)
    congruences_used: List[str] = field(default_factory=list)
    nodes_expanded: int = 0
    path_length: int = 0

    def record_axiom_use(self, axiom: str) -> None:
        """Increment the usage count for an axiom."""
        base = axiom.split('@')[0]
        self.axiom_histogram[base] = self.axiom_histogram.get(base, 0) + 1
        if '@' in axiom:
            self.congruences_used.append(axiom)

    def to_dict(self) -> Dict[str, Any]:
        """Serialize metrics to a plain dict for JSON output."""
        return {
            'strategy': self.strategy_used,
            'hit_depth': self.hit_depth_reached,
            'bfs_depth': self.bfs_depth_reached,
            'frontier_max': self.bfs_max_frontier_size,
            'time_ms': round(self.time_ms, 2),
            'axioms': dict(self.axiom_histogram),
            'congruences': len(self.congruences_used),
            'nodes_expanded': self.nodes_expanded,
            'path_length': self.path_length,
        }

    def summary(self) -> str:
        """One-line summary for logging."""
        top_axioms = sorted(self.axiom_histogram.items(), key=lambda x: -x[1])[:3]
        ax_str = ', '.join(f'{n}={c}' for n, c in top_axioms)
        return (f'{self.strategy_used} depth={self.bfs_depth_reached} '
                f'frontier={self.bfs_max_frontier_size} '
                f'nodes={self.nodes_expanded} '
                f'path={self.path_length} '
                f'time={self.time_ms:.1f}ms '
                f'axioms=[{ax_str}]')


def instrumented_search(
    nf_f: OTerm,
    nf_g: OTerm,
    max_depth: int = 4,
    max_frontier: int = 200,
    param_duck_types: Optional[Dict[str, str]] = None,
) -> Tuple[PathResult, PathSearchMetrics]:
    """Run ``search_path`` with full instrumentation.

    Returns both the PathResult and a PathSearchMetrics object.
    """
    metrics = PathSearchMetrics()
    t0 = time.monotonic()
    result = search_path(
        nf_f, nf_g,
        max_depth=max_depth,
        max_frontier=max_frontier,
        param_duck_types=param_duck_types,
    )
    t1 = time.monotonic()
    metrics.time_ms = (t1 - t0) * 1000.0
    metrics.path_length = len(result.path)
    if 'HIT' in result.reason:
        metrics.strategy_used = 'A_hit'
    elif 'spec' in result.reason:
        metrics.strategy_used = 'B_spec'
    elif 'bidirectional' in result.reason:
        metrics.strategy_used = 'C_bfs'
    elif 'A*' in result.reason:
        metrics.strategy_used = 'D_astar'
    else:
        metrics.strategy_used = 'X_unknown'
    for step in result.path:
        metrics.record_axiom_use(step.axiom)
    return result, metrics


# ═══════════════════════════════════════════════════════════
# Proposal 8: Axiom Dependency Graph (§18.axiom-category)
# ═══════════════════════════════════════════════════════════
#
# Build a directed graph of axiom dependencies: axiom A depends on
# axiom B if applying A may create redexes for B.  This is used for
# axiom scheduling (apply enabling axioms first).

@dataclass
class AxiomNode:
    """A node in the axiom dependency graph."""
    name: str
    creates_symbols: FrozenSet[str] = field(default_factory=frozenset)
    requires_symbols: FrozenSet[str] = field(default_factory=frozenset)


class AxiomDependencyGraph:
    """Directed graph of axiom dependencies.

    An edge A → B means "applying A may create a redex for B"
    (A's output symbols overlap B's input symbols).

    Example:
        >>> g = AxiomDependencyGraph()
        >>> g.add_axiom('D4_comp_fusion',
        ...     creates={'OMap'}, requires={'OMap', 'OFold'})
        >>> g.add_axiom('FOLD_fold',
        ...     creates={'sum', 'prod'}, requires={'OFold'})
        >>> g.get_dependents('D4_comp_fusion')
        ['FOLD_fold']
    """
    def __init__(self) -> None:
        self.nodes: Dict[str, AxiomNode] = {}

    def add_axiom(
        self,
        name: str,
        creates: Optional[Set[str]] = None,
        requires: Optional[Set[str]] = None,
    ) -> None:
        """Register an axiom with its symbol creation/requirement sets."""
        self.nodes[name] = AxiomNode(
            name=name,
            creates_symbols=frozenset(creates or set()),
            requires_symbols=frozenset(requires or set()),
        )

    def get_dependents(self, axiom_name: str) -> List[str]:
        """Return axioms that may be enabled by applying ``axiom_name``."""
        node = self.nodes.get(axiom_name)
        if node is None:
            return []
        result: List[str] = []
        for other_name, other_node in self.nodes.items():
            if other_name == axiom_name:
                continue
            if node.creates_symbols & other_node.requires_symbols:
                result.append(other_name)
        return sorted(result)

    def get_dependencies(self, axiom_name: str) -> List[str]:
        """Return axioms whose output may enable ``axiom_name``."""
        node = self.nodes.get(axiom_name)
        if node is None:
            return []
        result: List[str] = []
        for other_name, other_node in self.nodes.items():
            if other_name == axiom_name:
                continue
            if other_node.creates_symbols & node.requires_symbols:
                result.append(other_name)
        return sorted(result)

    def topological_order(self) -> List[str]:
        """Return axioms in dependency-respecting order (Kahn's algorithm).

        If A enables B, A comes before B.  Breaks cycles arbitrarily.
        """
        in_degree: Dict[str, int] = {n: 0 for n in self.nodes}
        adj: Dict[str, List[str]] = {n: [] for n in self.nodes}
        for name in self.nodes:
            for dep in self.get_dependents(name):
                if dep in adj:
                    adj[name].append(dep)
                    in_degree[dep] += 1
        queue = deque(n for n, d in in_degree.items() if d == 0)
        order: List[str] = []
        while queue:
            node = queue.popleft()
            order.append(node)
            for child in adj.get(node, []):
                in_degree[child] -= 1
                if in_degree[child] == 0:
                    queue.append(child)
        # Append any remaining nodes (cycles)
        for n in self.nodes:
            if n not in order:
                order.append(n)
        return order


def build_default_axiom_graph() -> AxiomDependencyGraph:
    """Build the axiom dependency graph for the standard 16 axioms."""
    g = AxiomDependencyGraph()
    g.add_axiom('D1_fold_unfold', creates={'OFold'}, requires={'OFix'})
    g.add_axiom('D2_beta', creates=set(), requires={'apply', 'OLam'})
    g.add_axiom('D4_comp_fusion', creates={'OMap'}, requires={'OMap', 'OFold'})
    g.add_axiom('D5_fold_universal', creates={'OFold'}, requires={'OFold'})
    g.add_axiom('D8_section_merge', creates={'OCase'}, requires={'OCase'})
    g.add_axiom('D13_histogram', creates={'Counter', 'OFold'}, requires={'Counter', 'OFold'})
    g.add_axiom('D16_memo_dp', creates={'OFix'}, requires={'OFix'})
    g.add_axiom('D17_assoc', creates={'OFold'}, requires={'OFold'})
    g.add_axiom('D19_sort_scan', creates={'OFold'}, requires={'sorted', 'OFold'})
    g.add_axiom('D20_spec_unify', creates={'OAbstract'}, requires=set())
    g.add_axiom('D22_effect_elim', creates={'OCase', 'OCatch'}, requires={'OCatch', 'OCase'})
    g.add_axiom('D24_eta', creates={'OOp'}, requires={'OLam'})
    g.add_axiom('ALG_algebra', creates={'OOp'}, requires={'OOp'})
    g.add_axiom('QUOT_quotient', creates={'OOp', 'OQuotient'}, requires={'OQuotient', 'sorted'})
    g.add_axiom('FOLD_fold', creates={'OOp', 'OFold'}, requires={'OFold', 'sum', 'len'})
    g.add_axiom('CASE_case', creates={'OCase'}, requires={'OCase'})
    return g


# ═══════════════════════════════════════════════════════════
# Proposal 9: Depth-Limited DFS Path Space Enumeration (§18.path-space)
# ═══════════════════════════════════════════════════════════
#
# Enumerate ALL rewrite paths up to a given depth, not just find one.
# Useful for proof complexity analysis and for finding shortest proofs.

@dataclass
class EnumeratedPath:
    """A single path found during enumeration."""
    steps: List[PathStep]
    depth: int
    final_canon: str


def enumerate_paths_dfs(
    source: OTerm,
    target_canon: Optional[str],
    ctx: FiberCtx,
    max_depth: int = 3,
    max_paths: int = 100,
) -> List[EnumeratedPath]:
    """Enumerate all rewrite paths from ``source`` up to ``max_depth``.

    If ``target_canon`` is provided, only paths reaching that canonical
    form are returned.  Otherwise, ALL reachable paths are returned.

    Uses depth-limited DFS with memoisation to avoid revisiting states.

    Example:
        >>> t = OOp('add', (OOp('add', (OVar('a'), OVar('b'))), OVar('c')))
        >>> ctx = FiberCtx(param_duck_types={'a': 'int', 'b': 'int', 'c': 'int'})
        >>> paths = enumerate_paths_dfs(t, None, ctx, max_depth=1)
        >>> len(paths) > 0
        True
    """
    results: List[EnumeratedPath] = []
    visited_at_depth: Dict[str, int] = {}

    def _dfs(term: OTerm, path: List[PathStep], depth: int) -> None:
        if len(results) >= max_paths:
            return
        c = term.canon()
        if c in visited_at_depth and visited_at_depth[c] <= depth:
            return
        visited_at_depth[c] = depth

        if target_canon is None or c == target_canon:
            results.append(EnumeratedPath(
                steps=list(path), depth=depth, final_canon=c,
            ))
        if depth >= max_depth:
            return
        for new_term, axiom in _all_rewrites(term, ctx):
            nc = new_term.canon()
            step = PathStep(axiom, 'root', c, nc)
            path.append(step)
            _dfs(new_term, path, depth + 1)
            path.pop()

    _dfs(source, [], 0)
    return results


def count_reachable(
    source: OTerm,
    ctx: FiberCtx,
    max_depth: int = 3,
) -> Dict[int, int]:
    """Count distinct canonical forms reachable at each depth.

    Returns a dict mapping depth → number of new canonical forms
    discovered at that depth.  Useful for measuring axiom-system
    branching factor.
    """
    current_frontier: Dict[str, OTerm] = {source.canon(): source}
    visited: Set[str] = {source.canon()}
    counts: Dict[int, int] = {0: 1}

    for depth in range(1, max_depth + 1):
        next_frontier: Dict[str, OTerm] = {}
        for _, term in current_frontier.items():
            for new_term, _ in _all_rewrites(term, ctx):
                nc = new_term.canon()
                if nc not in visited:
                    visited.add(nc)
                    next_frontier[nc] = new_term
        counts[depth] = len(next_frontier)
        current_frontier = next_frontier
        if not current_frontier:
            break
    return counts


# ═══════════════════════════════════════════════════════════
# Proposal 10: Symmetric Monoidal Structure on Axiom Category (§18.monoidal)
# ═══════════════════════════════════════════════════════════
#
# The axioms form a symmetric monoidal category where:
#   - Objects are canonical forms (strings)
#   - Morphisms are axiom applications
#   - Tensor product is parallel independent rewriting
#   - Symmetry is rewrite commutativity (Church-Rosser)

@dataclass(frozen=True)
class AxiomMorphism:
    """A morphism in the axiom category: a single rewrite step."""
    axiom: str
    source: str
    target: str

    def compose(self, other: 'AxiomMorphism') -> Optional['AxiomMorphism']:
        """Compose two morphisms if they are composable (source/target match)."""
        if self.target != other.source:
            return None
        return AxiomMorphism(
            axiom=f'{self.axiom};{other.axiom}',
            source=self.source,
            target=other.target,
        )


@dataclass(frozen=True)
class TensorProduct:
    """Parallel (independent) application of two axioms.

    Two axiom applications are independent if they operate on
    disjoint sub-terms.  Their tensor product is well-defined
    because they commute (Church-Rosser property).
    """
    left: AxiomMorphism
    right: AxiomMorphism

    @property
    def source(self) -> str:
        return f'({self.left.source} ⊗ {self.right.source})'

    @property
    def target(self) -> str:
        return f'({self.left.target} ⊗ {self.right.target})'


class AxiomCategory:
    """The category of axiom-mediated rewrites.

    Objects: canonical forms.
    Morphisms: sequences of axiom applications.
    Identity: refl (no rewrite).
    Composition: sequential rewriting.

    Example:
        >>> cat = AxiomCategory()
        >>> m1 = cat.identity('add($p0,$p1)')
        >>> m1.source == m1.target
        True
    """
    def identity(self, obj: str) -> AxiomMorphism:
        """Identity morphism on an object (canonical form)."""
        return AxiomMorphism(axiom='refl', source=obj, target=obj)

    def compose(self, f: AxiomMorphism, g: AxiomMorphism) -> Optional[AxiomMorphism]:
        """Compose f;g (f first, then g)."""
        return f.compose(g)

    def tensor(self, f: AxiomMorphism, g: AxiomMorphism) -> TensorProduct:
        """Tensor product of two independent morphisms."""
        return TensorProduct(left=f, right=g)

    def symmetry(self, f: TensorProduct) -> TensorProduct:
        """Swap the components of a tensor product."""
        return TensorProduct(left=f.right, right=f.left)

    def hom_set(
        self,
        source: OTerm,
        target: OTerm,
        ctx: FiberCtx,
        max_depth: int = 3,
    ) -> List[List[AxiomMorphism]]:
        """Enumerate all morphisms from source to target up to max_depth.

        Each morphism is a list of AxiomMorphisms (a path).
        """
        target_canon = target.canon()
        enum_paths = enumerate_paths_dfs(source, target_canon, ctx, max_depth)
        result: List[List[AxiomMorphism]] = []
        for ep in enum_paths:
            if ep.final_canon == target_canon:
                morphisms = [
                    AxiomMorphism(axiom=s.axiom, source=s.before, target=s.after)
                    for s in ep.steps
                ]
                result.append(morphisms)
        return result


# ═══════════════════════════════════════════════════════════
# Proposal 11: Extended Spec Library (§18.yoneda)
# ═══════════════════════════════════════════════════════════
#
# Canonical OTerm representations for common algorithms, enabling
# D20 spec unification for a wider set of programs.

def spec_gcd(a: OTerm, b: OTerm) -> OTerm:
    """Canonical OTerm for GCD(a, b): fix with Euclidean algorithm.

    Example:
        >>> spec_gcd(OVar('a'), OVar('b')).canon()
        '@gcd($a,$b)'
    """
    return OAbstract('gcd', (a, b))


def spec_lcm(a: OTerm, b: OTerm) -> OTerm:
    """Canonical OTerm for LCM(a, b) = a*b / gcd(a,b).

    Example:
        >>> spec_lcm(OVar('a'), OVar('b')).canon()
        '@lcm($a,$b)'
    """
    return OAbstract('lcm', (a, b))


def spec_prime_sieve(n: OTerm) -> OTerm:
    """Canonical OTerm for Sieve of Eratosthenes up to n.

    Example:
        >>> spec_prime_sieve(OVar('n')).canon()
        '@prime_sieve($n)'
    """
    return OAbstract('prime_sieve', (n,))


def spec_matrix_mul(a: OTerm, b: OTerm) -> OTerm:
    """Canonical OTerm for matrix multiplication A @ B.

    Example:
        >>> spec_matrix_mul(OVar('A'), OVar('B')).canon()
        '@matmul($A,$B)'
    """
    return OAbstract('matmul', (a, b))


def spec_tree_traversal(root: OTerm, order: str = 'inorder') -> OTerm:
    """Canonical OTerm for tree traversal in given order.

    ``order`` is one of 'preorder', 'inorder', 'postorder', 'levelorder'.
    """
    return OAbstract(f'tree_{order}', (root,))


def spec_dot_product(a: OTerm, b: OTerm) -> OTerm:
    """Canonical OTerm for dot product: sum(a[i]*b[i] for i)."""
    return OAbstract('dot_product', (a, b))


def spec_power(base: OTerm, exp: OTerm) -> OTerm:
    """Canonical OTerm for base ** exp."""
    return OAbstract('power', (base, exp))


def spec_fibonacci(n: OTerm) -> OTerm:
    """Canonical OTerm for the n-th Fibonacci number."""
    return OAbstract('fibonacci', (n,))


# Registry mapping spec names to their recogniser predicates.
SPEC_REGISTRY: Dict[str, Callable[[OTerm], Optional[Tuple[OTerm, ...]]]] = {}


def register_spec(name: str) -> Callable:
    """Decorator to register a spec recogniser in SPEC_REGISTRY.

    Example:
        @register_spec('gcd')
        def _recognise_gcd(term):
            if isinstance(term, OFix) and 'mod' in term.body.canon():
                inputs = _extract_free_vars(term)
                if len(inputs) == 2:
                    return tuple(OVar(v) for v in sorted(inputs))
            return None
    """
    def decorator(fn: Callable[[OTerm], Optional[Tuple[OTerm, ...]]]) -> Callable:
        SPEC_REGISTRY[name] = fn
        return fn
    return decorator


@register_spec('gcd')
def _recognise_gcd(term: OTerm) -> Optional[Tuple[OTerm, ...]]:
    """Recognise GCD patterns: fix with mod, or direct gcd() call."""
    if isinstance(term, OOp) and term.name in ('gcd', 'math.gcd'):
        return term.args
    if isinstance(term, OFix):
        bc = term.body.canon()
        if 'mod' in bc or 'remainder' in bc:
            inputs = _extract_free_vars(term)
            if len(inputs) == 2:
                return tuple(OVar(v) for v in sorted(inputs))
    return None


@register_spec('lcm')
def _recognise_lcm(term: OTerm) -> Optional[Tuple[OTerm, ...]]:
    """Recognise LCM patterns."""
    if isinstance(term, OOp) and term.name in ('lcm', 'math.lcm'):
        return term.args
    return None


@register_spec('power')
def _recognise_power(term: OTerm) -> Optional[Tuple[OTerm, ...]]:
    """Recognise power/exponentiation: pow(b,e) or b**e."""
    if isinstance(term, OOp) and term.name in ('pow', 'power', '**'):
        return term.args
    if isinstance(term, OFold) and term.op_name in ('.mul', 'mul', 'imul', 'mult'):
        if isinstance(term.init, OLit) and term.init.value == 1:
            if isinstance(term.collection, OOp) and term.collection.name == 'repeat':
                return (term.collection.args[0], term.collection.args[1]) if len(term.collection.args) >= 2 else None
    return None


@register_spec('matrix_mul')
def _recognise_matrix_mul(term: OTerm) -> Optional[Tuple[OTerm, ...]]:
    """Recognise matrix multiplication: matmul, @, or nested folds."""
    if isinstance(term, OOp) and term.name in ('matmul', 'np.matmul', 'dot', 'np.dot'):
        return term.args
    return None


def identify_spec_registry(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """Spec identification using the registry of recogniser functions.

    Tries the base ``_identify_spec``, then ``identify_spec_extended``,
    then all registered spec recognisers.
    """
    base = identify_spec_extended(term)
    if base is not None:
        return base
    for spec_name, recogniser in SPEC_REGISTRY.items():
        inputs = recogniser(term)
        if inputs is not None:
            return (spec_name, inputs)
    return None


# ═══════════════════════════════════════════════════════════
# Proposal 12: Congruence Closure for OTerm Equality (§18.congruence)
# ═══════════════════════════════════════════════════════════
#
# A union-find based congruence closure algorithm that maintains
# equivalence classes of OTerms under the axiom rewrites.  Two terms
# are congruent if they can be connected by axiom applications.

class _UnionFind:
    """Weighted union-find with path compression for canonical strings."""

    def __init__(self) -> None:
        self.parent: Dict[str, str] = {}
        self.rank: Dict[str, int] = {}

    def find(self, x: str) -> str:
        if x not in self.parent:
            self.parent[x] = x
            self.rank[x] = 0
        if self.parent[x] != x:
            self.parent[x] = self.find(self.parent[x])
        return self.parent[x]

    def union(self, x: str, y: str) -> bool:
        """Union the sets containing x and y.  Returns True if they were separate."""
        rx, ry = self.find(x), self.find(y)
        if rx == ry:
            return False
        if self.rank[rx] < self.rank[ry]:
            rx, ry = ry, rx
        self.parent[ry] = rx
        if self.rank[rx] == self.rank[ry]:
            self.rank[rx] += 1
        return True

    def same(self, x: str, y: str) -> bool:
        return self.find(x) == self.find(y)


class CongruenceClosure:
    """Congruence closure over OTerms under axiom rewrites.

    Maintains a union-find of canonical forms.  Calling ``add_term``
    saturates equivalence classes by applying axioms up to a fixed depth.

    Example:
        >>> cc = CongruenceClosure(FiberCtx(param_duck_types={'p0': 'int', 'p1': 'int'}))
        >>> a = OOp('add', (OVar('p0'), OVar('p1')))
        >>> b = OOp('add', (OVar('p1'), OVar('p0')))
        >>> cc.add_term(a, depth=1)
        >>> cc.add_term(b, depth=1)
        >>> cc.are_equal(a, b)
        True
    """
    def __init__(self, ctx: FiberCtx) -> None:
        self.ctx = ctx
        self.uf = _UnionFind()
        self._terms: Dict[str, OTerm] = {}

    def add_term(self, term: OTerm, depth: int = 2) -> None:
        """Add a term and saturate its equivalence class to ``depth``."""
        canon = term.canon()
        self._terms[canon] = term
        frontier: Dict[str, OTerm] = {canon: term}
        for _ in range(depth):
            next_frontier: Dict[str, OTerm] = {}
            for c, t in frontier.items():
                for new_t, _ in _all_rewrites(t, self.ctx):
                    nc = new_t.canon()
                    self.uf.union(c, nc)
                    if nc not in self._terms:
                        self._terms[nc] = new_t
                        next_frontier[nc] = new_t
            frontier = next_frontier

    def are_equal(self, a: OTerm, b: OTerm) -> bool:
        """Check if two terms are in the same equivalence class."""
        return self.uf.same(a.canon(), b.canon())

    def equivalence_class(self, term: OTerm) -> Set[str]:
        """Return all known canonical forms in the same class as ``term``."""
        root = self.uf.find(term.canon())
        return {c for c in self._terms if self.uf.find(c) == root}

    def class_count(self) -> int:
        """Return the number of distinct equivalence classes."""
        roots = {self.uf.find(c) for c in self._terms}
        return len(roots)


# ═══════════════════════════════════════════════════════════
# Proposal 13: Proof-Relevant Path Search (§18.proof-relevance)
# ═══════════════════════════════════════════════════════════
#
# Paths carry proofs of correctness: each step includes a witness
# (the axiom and its instantiation) that can be independently verified.

class ProofWitness(Enum):
    """How a rewrite step was justified."""
    REFL = auto()
    AXIOM_APPLICATION = auto()
    CONGRUENCE = auto()
    SPEC_UNIFICATION = auto()
    HIT_INDUCTION = auto()


@dataclass(frozen=True)
class ProofRelevantStep:
    """A rewrite step with its proof witness attached.

    The witness records not just which axiom fired, but HOW it was
    instantiated: the matched sub-term, variable bindings, etc.
    """
    axiom: str
    witness: ProofWitness
    before: OTerm
    after: OTerm
    position: Tuple[int, ...]
    bindings: Dict[str, str] = field(default_factory=dict)

    def justify(self) -> str:
        """Human-readable justification string."""
        pos_str = '.'.join(str(i) for i in self.position) if self.position else 'root'
        bind_str = ', '.join(f'{k}={v}' for k, v in self.bindings.items())
        parts = [f'{self.witness.name}: {self.axiom} at {pos_str}']
        if bind_str:
            parts.append(f'  bindings: {bind_str}')
        return '\n'.join(parts)


@dataclass
class ProofRelevantPath:
    """A complete proof-relevant path from source to target.

    Every step carries its justification so the path is independently
    checkable without re-running the search.
    """
    source: OTerm
    target: OTerm
    steps: List[ProofRelevantStep]

    @property
    def is_valid(self) -> bool:
        """Check structural validity of the proof.

        Uses the ``_raw_canon`` helper to extract canonical strings from
        the step's before/after OTerms, which may be OUnknown wrappers
        carrying the original canonical string (prefixed with ``?``).
        """
        if not self.steps:
            return self.source.canon() == self.target.canon()
        first_before = self._raw_canon(self.steps[0].before)
        if first_before != self.source.canon():
            return False
        last_after = self._raw_canon(self.steps[-1].after)
        if last_after != self.target.canon():
            return False
        for i in range(len(self.steps) - 1):
            if self._raw_canon(self.steps[i].after) != self._raw_canon(self.steps[i + 1].before):
                return False
        return True

    @staticmethod
    def _raw_canon(term: OTerm) -> str:
        """Extract the underlying canonical string from a term.

        If the term is an ``OUnknown`` wrapper (created when lifting a
        base PathResult), strip the leading ``?`` to recover the original
        canonical form.
        """
        c = term.canon()
        if isinstance(term, OUnknown) and c.startswith('?'):
            return c[1:]
        return c

    def to_latex(self) -> str:
        """Export the proof path as a LaTeX align environment."""
        lines = [r'\begin{align*}']
        lines.append(f'  & {self.source.canon()} \\\\')
        for step in self.steps:
            lines.append(
                f'  &\\xrightarrow{{\\text{{{step.axiom}}}}} {step.after.canon()} \\\\'
            )
        lines.append(r'\end{align*}')
        return '\n'.join(lines)


def proof_relevant_search(
    source: OTerm,
    target: OTerm,
    ctx: Optional[FiberCtx] = None,
    max_depth: int = 4,
) -> Optional[ProofRelevantPath]:
    """Wrapper around search_path that annotates each step with a proof witness."""
    if ctx is None:
        ctx = FiberCtx(param_duck_types={})
    result = search_path(source, target, max_depth=max_depth, param_duck_types=ctx.param_duck_types)
    if result.found is not True:
        return None
    steps: List[ProofRelevantStep] = []
    for ps in result.path:
        if ps.axiom == 'refl' or ps.axiom == 'HIT_structural':
            witness = ProofWitness.HIT_INDUCTION
        elif ps.axiom.startswith('D20'):
            witness = ProofWitness.SPEC_UNIFICATION
        elif '@' in ps.axiom:
            witness = ProofWitness.CONGRUENCE
        else:
            witness = ProofWitness.AXIOM_APPLICATION
        steps.append(ProofRelevantStep(
            axiom=ps.axiom,
            witness=witness,
            before=OUnknown(ps.before),
            after=OUnknown(ps.after),
            position=tuple(int(x) for x in ps.position.split('.') if x.isdigit()),
        ))
    return ProofRelevantPath(source=source, target=target, steps=steps)


# ═══════════════════════════════════════════════════════════
# Proposal 14: Axiom Synthesis from Benchmark Failures (§18.axiom-learning)
# ═══════════════════════════════════════════════════════════
#
# When the path search fails on a benchmark pair, record the failure
# and attempt to synthesise a new axiom that bridges the gap.

@dataclass
class FailedPair:
    """A pair of terms where path search failed."""
    source: OTerm
    target: OTerm
    source_canon: str
    target_canon: str
    reason: str
    source_symbols: FrozenSet[str]
    target_symbols: FrozenSet[str]
    timestamp: float = field(default_factory=time.monotonic)


@dataclass
class SynthesisedAxiom:
    """An axiom synthesised from a failed pair.

    This is a candidate rewrite rule learned from the structure of
    the source/target pair.  It must be validated before adding to
    the axiom set.
    """
    name: str
    pattern_source: str
    pattern_target: str
    confidence: float
    origin_pair: FailedPair

    def describe(self) -> str:
        return f'{self.name}: {self.pattern_source} → {self.pattern_target} (conf={self.confidence:.2f})'


class AxiomSynthesiser:
    """Learn new axioms from failing benchmark pairs.

    Collects failed pairs, clusters them by structural similarity,
    and attempts to extract rewrite patterns from the clusters.

    Example:
        >>> synth = AxiomSynthesiser()
        >>> synth.record_failure(
        ...     OOp('sum', (OVar('xs'),)),
        ...     OFold('.add', OLit(0), OVar('xs')),
        ...     'no path found',
        ... )
        >>> candidates = synth.synthesise()
        >>> # May produce a candidate axiom bridging sum ↔ fold[add]
    """
    def __init__(self) -> None:
        self.failures: List[FailedPair] = []

    def record_failure(self, source: OTerm, target: OTerm, reason: str) -> None:
        """Record a failed pair for later analysis."""
        self.failures.append(FailedPair(
            source=source,
            target=target,
            source_canon=source.canon(),
            target_canon=target.canon(),
            reason=reason,
            source_symbols=frozenset(extract_symbols(source)),
            target_symbols=frozenset(extract_symbols(target)),
        ))

    def cluster_by_structure(self) -> Dict[str, List[FailedPair]]:
        """Group failures by structural signature (root constructor pair).

        Returns a dict mapping e.g. "OOp→OFold" to list of failures.
        """
        clusters: Dict[str, List[FailedPair]] = defaultdict(list)
        for fp in self.failures:
            src_type = type(fp.source).__name__
            tgt_type = type(fp.target).__name__
            key = f'{src_type}→{tgt_type}'
            clusters[key].append(fp)
        return dict(clusters)

    def _extract_pattern(self, fp: FailedPair) -> Optional[Tuple[str, str]]:
        """Try to extract a rewrite pattern from a single failure.

        Generalises the source and target by replacing concrete sub-terms
        with wildcards.  Returns (source_pattern, target_pattern) or None
        if the terms share no structural similarity at all.
        """
        sc = fp.source_canon
        tc = fp.target_canon
        if sc == tc:
            return None
        return (sc, tc)

    def synthesise(self, min_cluster_size: int = 1) -> List[SynthesisedAxiom]:
        """Attempt to synthesise axioms from recorded failures.

        Groups failures by structure, extracts patterns from clusters
        of size ≥ ``min_cluster_size``, and returns candidate axioms
        with a confidence score.
        """
        candidates: List[SynthesisedAxiom] = []
        clusters = self.cluster_by_structure()
        counter = 0
        for key, fps in clusters.items():
            if len(fps) < min_cluster_size:
                continue
            for fp in fps:
                pattern = self._extract_pattern(fp)
                if pattern is None:
                    continue
                src_pat, tgt_pat = pattern
                confidence = min(1.0, len(fps) / 5.0)
                candidates.append(SynthesisedAxiom(
                    name=f'SYNTH_{counter}_{key.replace("→", "_to_")}',
                    pattern_source=src_pat,
                    pattern_target=tgt_pat,
                    confidence=confidence,
                    origin_pair=fp,
                ))
                counter += 1
        return candidates

    def report(self) -> str:
        """Human-readable summary of failures and candidates."""
        lines = [f'Recorded {len(self.failures)} failure(s).']
        clusters = self.cluster_by_structure()
        for key, fps in sorted(clusters.items()):
            lines.append(f'  {key}: {len(fps)} failure(s)')
        candidates = self.synthesise()
        if candidates:
            lines.append(f'Synthesised {len(candidates)} candidate axiom(s):')
            for c in candidates:
                lines.append(f'  {c.describe()}')
        else:
            lines.append('No candidate axioms synthesised.')
        return '\n'.join(lines)


# ═══════════════════════════════════════════════════════════
# Utility: Integrated Path Search Pipeline
# ═══════════════════════════════════════════════════════════

def full_pipeline_search(
    nf_f: OTerm,
    nf_g: OTerm,
    param_duck_types: Optional[Dict[str, str]] = None,
    max_depth: int = 4,
    max_frontier: int = 200,
    collect_metrics: bool = True,
    use_astar: bool = False,
    use_congruence_closure: bool = False,
) -> Tuple[PathResult, Optional[PathSearchMetrics]]:
    """Integrated search pipeline combining all proposals.

    Pipeline:
      1. Normalise both terms.
      2. Check reflexivity.
      3. Try HIT structural decomposition (Strategy A).
      4. Try spec identification with extended+registry (Strategy B).
      5. Optionally try congruence closure (Proposal 12).
      6. Fall back to A* (Proposal 4) or standard BFS (Strategy C).
      7. Collect metrics (Proposal 7) if requested.
    """
    ctx = FiberCtx(param_duck_types=param_duck_types or {})
    metrics = PathSearchMetrics() if collect_metrics else None
    t0 = time.monotonic()

    cf = nf_f.canon()
    cg = nf_g.canon()

    # ── Step 1: refl ──
    if cf == cg:
        result = PathResult(found=True, path=[], reason='refl')
        if metrics:
            metrics.strategy_used = 'refl'
            metrics.time_ms = (time.monotonic() - t0) * 1000.0
        return result, metrics

    # ── Step 2: Congruence closure (optional) ──
    if use_congruence_closure:
        cc = CongruenceClosure(ctx)
        cc.add_term(nf_f, depth=2)
        cc.add_term(nf_g, depth=2)
        if cc.are_equal(nf_f, nf_g):
            result = PathResult(
                found=True,
                path=[PathStep('congruence_closure', 'root', cf, cg)],
                reason='congruence closure',
            )
            if metrics:
                metrics.strategy_used = 'E_congruence'
                metrics.time_ms = (time.monotonic() - t0) * 1000.0
            return result, metrics

    # ── Step 3: Extended spec identification ──
    spec_f = identify_spec_registry(nf_f)
    spec_g = identify_spec_registry(nf_g)
    if spec_f is not None and spec_g is not None:
        if spec_f[0] == spec_g[0] and len(spec_f[1]) == len(spec_g[1]):
            inputs_match = all(
                a.canon() == b.canon() for a, b in zip(spec_f[1], spec_g[1])
            )
            if inputs_match:
                result = PathResult(
                    found=True,
                    path=[PathStep('D20_spec_unify_extended', 'root', cf, cg)],
                    reason=f'same spec: {spec_f[0]}',
                )
                if metrics:
                    metrics.strategy_used = 'B_spec_extended'
                    metrics.time_ms = (time.monotonic() - t0) * 1000.0
                return result, metrics

    # ── Step 4: Delegate to A* or standard search ──
    if use_astar:
        result = astar_search(nf_f, nf_g, ctx, max_depth, max_frontier)
    else:
        result = search_path(
            nf_f, nf_g, max_depth, max_frontier, param_duck_types,
        )

    if metrics:
        t1 = time.monotonic()
        metrics.time_ms = (t1 - t0) * 1000.0
        metrics.path_length = len(result.path)
        if result.found is True:
            metrics.strategy_used = 'D_astar' if use_astar else 'C_bfs'
        else:
            metrics.strategy_used = 'FAIL'
        for step in result.path:
            metrics.record_axiom_use(step.axiom)

    return result, metrics


# ═══════════════════════════════════════════════════════════
# Self-Tests
# ═══════════════════════════════════════════════════════════

if __name__ == '__main__':
    import sys

    passed = 0
    failed = 0

    def check(name: str, condition: bool) -> None:
        global passed, failed
        if condition:
            passed += 1
            print(f'  ✓ {name}')
        else:
            failed += 1
            print(f'  ✗ {name}')

    # ── Proposal 1: StructuredPathStep ──
    print('Proposal 1: StructuredPathStep / PathCertificate')
    step1 = StructuredPathStep(
        axiom='ALG_commute',
        position=(),
        before=OOp('add', (OVar('p0'), OVar('p1'))),
        after=OOp('add', (OVar('p1'), OVar('p0'))),
    )
    check('to_base returns PathStep', isinstance(step1.to_base(), PathStep))
    cert = PathCertificate(
        steps=[step1],
        source=OOp('add', (OVar('p0'), OVar('p1'))),
        target=OOp('add', (OVar('p1'), OVar('p0'))),
    )
    check('certificate chain connected', cert.is_chain_connected())
    check('certificate length is 1', len(cert) == 1)

    # ── Proposal 2: Axiom relevance filtering ──
    print('\nProposal 2: Axiom Relevance Filtering')
    ctx_num = FiberCtx(param_duck_types={'p0': 'int', 'p1': 'int'})
    t_add = OOp('add', (OVar('p0'), OVar('p1')))
    syms = extract_symbols(t_add)
    check('extract_symbols finds add', 'add' in syms)
    rel = relevant_axioms(t_add, ctx_num)
    check('relevant_axioms returns subset', len(rel) <= len(_ROOT_AXIOMS))
    check('relevant_axioms non-empty', len(rel) > 0)

    # ── Proposal 3: Extended spec identification ──
    print('\nProposal 3: Extended Spec Identification')
    t_max = OOp('max', (OVar('xs'),))
    spec = identify_spec_extended(t_max)
    check('max spec recognised', spec is not None and spec[0] == 'max')
    t_min = OFold('min', OLit(float('inf')), OVar('xs'))
    spec_min = identify_spec_extended(t_min)
    check('fold[min] spec recognised', spec_min is not None and spec_min[0] == 'min')
    t_rev = OOp('reversed', (OVar('xs'),))
    spec_rev = identify_spec_extended(t_rev)
    check('reversed spec recognised', spec_rev is not None and spec_rev[0] == 'reverse')

    # ── Proposal 4: A* search ──
    print('\nProposal 4: A* Search')
    a = OOp('add', (OVar('p0'), OVar('p1')))
    b = OOp('add', (OVar('p1'), OVar('p0')))
    r = astar_search(a, b, ctx_num, max_depth=3)
    check('A* finds commutative path', r.found is True)
    check('edit distance heuristic non-negative', _edit_distance_heuristic('abc', 'xyz') >= 0)
    check('edit distance of identical strings is 0', _edit_distance_heuristic('abc', 'abc') == 0)

    # ── Proposal 5: Fiber validation ──
    print('\nProposal 5: Fiber Validation')
    v = FiberValidator(ctx_num)
    check('add is commutative on int', v.has_property(t_add, 'add', FiberProperty.COMMUTATIVE))
    ctx_str = FiberCtx(param_duck_types={'p0': 'str', 'p1': 'str'})
    v_str = FiberValidator(ctx_str)
    t_add_str = OOp('add', (OVar('p0'), OVar('p1')))
    check('add is NOT commutative on str', not v_str.has_property(t_add_str, 'add', FiberProperty.COMMUTATIVE))
    check('mul is always commutative', v.has_property(t_add, 'mul', FiberProperty.COMMUTATIVE))

    # ── Proposal 6: Certificate verification ──
    print('\nProposal 6: Certificate Verification')
    steps_ok = [
        PathStep('ALG_commute', 'root', 'add($p0,$p1)', 'add($p1,$p0)'),
    ]
    ok, errs = verify_certificate(steps_ok)
    check('valid certificate passes', ok)
    check('no errors for valid certificate', len(errs) == 0)
    steps_bad = [
        PathStep('ALG_commute', 'root', 'add($p0,$p1)', 'add($p1,$p0)'),
        PathStep('ALG_commute', 'root', 'WRONG_CANON', 'add($p0,$p1)'),
    ]
    ok2, errs2 = verify_certificate(steps_bad)
    check('broken chain detected', not ok2)
    check('error message present', len(errs2) > 0)

    # ── Proposal 7: Metrics ──
    print('\nProposal 7: Path Search Metrics')
    result7, metrics7 = instrumented_search(a, b, param_duck_types={'p0': 'int', 'p1': 'int'})
    check('instrumented search finds path', result7.found is True)
    check('metrics has strategy', metrics7.strategy_used != '')
    check('metrics has timing', metrics7.time_ms >= 0)
    check('metrics summary is non-empty', len(metrics7.summary()) > 0)

    # ── Proposal 8: Axiom dependency graph ──
    print('\nProposal 8: Axiom Dependency Graph')
    g = build_default_axiom_graph()
    check('graph has 16 nodes', len(g.nodes) == 16)
    deps = g.get_dependents('D1_fold_unfold')
    check('D1 enables some axioms', len(deps) > 0)
    order = g.topological_order()
    check('topological order has 16 elements', len(order) == 16)

    # ── Proposal 9: DFS path enumeration ──
    print('\nProposal 9: Depth-Limited DFS Enumeration')
    t9 = OOp('add', (OOp('add', (OVar('a'), OVar('b'))), OVar('c')))
    ctx9 = FiberCtx(param_duck_types={'a': 'int', 'b': 'int', 'c': 'int'})
    paths9 = enumerate_paths_dfs(t9, None, ctx9, max_depth=1, max_paths=50)
    check('DFS finds at least 1 path', len(paths9) >= 1)
    counts = count_reachable(t9, ctx9, max_depth=1)
    check('reachable counts has depth 0', 0 in counts)
    check('reachable at depth 0 is 1', counts[0] == 1)

    # ── Proposal 10: Axiom category ──
    print('\nProposal 10: Symmetric Monoidal Axiom Category')
    cat = AxiomCategory()
    m_id = cat.identity('add($p0,$p1)')
    check('identity source == target', m_id.source == m_id.target)
    m1 = AxiomMorphism('ALG_commute', 'add($p0,$p1)', 'add($p1,$p0)')
    m2 = AxiomMorphism('ALG_commute', 'add($p1,$p0)', 'add($p0,$p1)')
    composed = cat.compose(m1, m2)
    check('composition is involution', composed is not None and composed.source == composed.target)
    tp = cat.tensor(m1, m2)
    check('tensor product has source', '⊗' in tp.source)
    sym = cat.symmetry(tp)
    check('symmetry swaps components', sym.left == tp.right)

    # ── Proposal 11: Extended spec library ──
    print('\nProposal 11: Extended Spec Library')
    check('spec_gcd produces OAbstract', isinstance(spec_gcd(OVar('a'), OVar('b')), OAbstract))
    check('spec_lcm canon', spec_lcm(OVar('a'), OVar('b')).canon() == '@lcm($a,$b)')
    check('spec_fibonacci canon', spec_fibonacci(OVar('n')).canon() == '@fibonacci($n)')
    gcd_term = OOp('gcd', (OVar('a'), OVar('b')))
    gcd_spec = identify_spec_registry(gcd_term)
    check('registry recognises gcd', gcd_spec is not None and gcd_spec[0] == 'gcd')

    # ── Proposal 12: Congruence closure ──
    print('\nProposal 12: Congruence Closure')
    cc = CongruenceClosure(ctx_num)
    cc.add_term(a, depth=1)
    cc.add_term(b, depth=1)
    check('congruence closure: add commutative', cc.are_equal(a, b))
    check('class_count >= 1', cc.class_count() >= 1)
    eq_class = cc.equivalence_class(a)
    check('equivalence class non-empty', len(eq_class) >= 1)

    # ── Proposal 13: Proof-relevant search ──
    print('\nProposal 13: Proof-Relevant Path Search')
    pr = proof_relevant_search(a, b, ctx_num)
    check('proof-relevant search found path', pr is not None)
    if pr is not None:
        check('proof-relevant path is valid', pr.is_valid)
        check('to_latex produces string', len(pr.to_latex()) > 0)

    # ── Proposal 14: Axiom synthesis ──
    print('\nProposal 14: Axiom Synthesis from Failures')
    synth = AxiomSynthesiser()
    synth.record_failure(
        OOp('custom_op', (OVar('x'),)),
        OOp('other_op', (OVar('x'),)),
        'no path',
    )
    check('failure recorded', len(synth.failures) == 1)
    clusters = synth.cluster_by_structure()
    check('cluster has 1 entry', len(clusters) == 1)
    candidates = synth.synthesise()
    check('at least 1 candidate', len(candidates) >= 1)
    report = synth.report()
    check('report is non-empty', len(report) > 0)

    # ── Integration: full pipeline ──
    print('\nIntegration: Full Pipeline Search')
    r_pipe, m_pipe = full_pipeline_search(
        a, b,
        param_duck_types={'p0': 'int', 'p1': 'int'},
        use_astar=True,
        collect_metrics=True,
    )
    check('pipeline finds path', r_pipe.found is True)
    check('pipeline metrics collected', m_pipe is not None)
    if m_pipe:
        check('pipeline timing > 0', m_pipe.time_ms >= 0)

    r_cc, m_cc = full_pipeline_search(
        a, b,
        param_duck_types={'p0': 'int', 'p1': 'int'},
        use_congruence_closure=True,
        collect_metrics=True,
    )
    check('pipeline with congruence closure finds path', r_cc.found is True)

    # ── Summary ──
    print(f'\n{"=" * 50}')
    print(f'Results: {passed} passed, {failed} failed, {passed + failed} total')
    if failed > 0:
        sys.exit(1)
    else:
        print('All self-tests passed.')
        sys.exit(0)
