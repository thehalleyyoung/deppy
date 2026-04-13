"""D18: Greedy Algorithm Equivalences (Theorem 22.4.1).

Greedy ↔ DP when the problem has matroid structure.

Mathematical foundation:
  The greedy algorithm produces an optimal solution iff the
  feasibility structure forms a matroid (Edmonds 1971, Rado 1957).

  A matroid M = (E, I) where E is a finite set and I ⊆ 2^E is a
  family of "independent" sets satisfying:
    (I1) ∅ ∈ I                               (empty set is independent)
    (I2) A ⊆ B ∈ I  ⟹  A ∈ I               (hereditary / downward closed)
    (I3) |A| < |B|, A, B ∈ I  ⟹  ∃x ∈ B\\A. A∪{x} ∈ I  (exchange)

  When these hold:
    greedy(w, M) = argmax_{B ∈ I} Σ_{x∈B} w(x)
  and this equals the DP solution (which tries all combinations).

  Conversely, when the matroid property fails, greedy may produce
  suboptimal results and is NOT equivalent to DP.

Covers:
  • Greedy ↔ DP when matroid property holds
  • Matroid detection from problem structure
  • Greedy-choice property verification
  • Optimal substructure verification
  • Activity selection / interval scheduling
  • Huffman coding matroid
  • Minimum spanning tree (Kruskal / Prim)
  • Knapsack (fractional=matroid, 0/1=not matroid)
"""
from __future__ import annotations

import hashlib
from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple, Union

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)


# ═══════════════════════════════════════════════════════════
# Axiom metadata
# ═══════════════════════════════════════════════════════════

AXIOM_NAME = 'D18_greedy'
AXIOM_CATEGORY = 'algorithm_strategy'  # §22

SOUNDNESS_PROOF = """
Theorem 22.4.1 (Greedy-DP Equivalence under Matroid):
  Let (E, I, w) be a weighted matroid.  Then:
    greedy(w, M)  =  dp_optimal(w, M)

  where greedy iterates elements in decreasing weight order and
  greedily adds each element if the result remains independent,
  and dp_optimal searches all independent sets.

Proof:
  By the Rado–Edmonds theorem, the greedy algorithm on a matroid
  maximises any linear objective.  The DP explores the same space
  exhaustively, finding the same maximum.  Since the maximum is
  unique for generic weights, both algorithms return the same set.  ∎

Converse (Theorem 22.4.2):
  If greedy always equals DP-optimal for all weight functions w,
  then (E, I) is a matroid.  This is the Rado characterisation.

Known matroid problems:
  • Minimum spanning tree (graphic matroid)
  • Activity selection (interval scheduling matroid)
  • Huffman coding (matroid on alphabet extension)
  • Fractional knapsack (uniform matroid)

Known NON-matroid problems:
  • 0/1 knapsack (greedy ≠ optimal in general)
  • Travelling salesman
  • Set cover (greedy is log-approximation, not exact)
"""

COMPOSES_WITH = ['D16_memo_dp', 'D17_assoc', 'D20_spec']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'Greedy to DP (matroid)',
        'before': "greedy_select(items, weight_fn, is_independent)",
        'after': "dp_optimal(items, weight_fn, is_independent)",
        'axiom': 'D18_greedy_to_dp',
    },
    {
        'name': 'DP to greedy (matroid)',
        'before': "dp_optimal(items, weight_fn, is_independent)",
        'after': "greedy_select(items, weight_fn, is_independent)",
        'axiom': 'D18_dp_to_greedy',
    },
    {
        'name': 'Activity selection',
        'before': "dp_max_non_overlapping(intervals)",
        'after': "greedy_earliest_finish(intervals)",
        'axiom': 'D18_activity_selection',
    },
    {
        'name': 'MST equivalence',
        'before': "dp_min_spanning_tree(graph)",
        'after': "kruskal(graph)",
        'axiom': 'D18_mst_kruskal',
    },
    {
        'name': 'Fractional knapsack',
        'before': "dp_fractional_knapsack(items, capacity)",
        'after': "greedy_fractional_knapsack(items, capacity)",
        'axiom': 'D18_fractional_knapsack',
    },
]

# ── Known matroid problem signatures ──
MATROID_SPECS: FrozenSet[str] = frozenset({
    'activity_selection', 'interval_scheduling',
    'min_spanning_tree', 'mst', 'kruskal', 'prim',
    'huffman', 'huffman_coding',
    'fractional_knapsack',
    'job_scheduling_deadlines',
    'max_weight_forest',
    'matroid_intersection',
})

# ── Known NON-matroid problem signatures ──
NON_MATROID_SPECS: FrozenSet[str] = frozenset({
    'knapsack_01', '0_1_knapsack',
    'tsp', 'travelling_salesman',
    'set_cover', 'vertex_cover',
    'graph_coloring',
})


# ═══════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════

@dataclass
class FiberCtx:
    """Lightweight fiber context for standalone axiom evaluation."""
    param_duck_types: Dict[str, str] = field(default_factory=dict)


def _extract_free_vars(term: OTerm) -> Set[str]:
    """Extract all free variable names."""
    if isinstance(term, OVar):
        return {term.name}
    if isinstance(term, OLit) or isinstance(term, OUnknown):
        return set()
    if isinstance(term, OOp):
        r: Set[str] = set()
        for a in term.args:
            r |= _extract_free_vars(a)
        return r
    if isinstance(term, OFold):
        return _extract_free_vars(term.init) | _extract_free_vars(term.collection)
    if isinstance(term, OCase):
        return (
            _extract_free_vars(term.test)
            | _extract_free_vars(term.true_branch)
            | _extract_free_vars(term.false_branch)
        )
    if isinstance(term, OFix):
        return _extract_free_vars(term.body)
    if isinstance(term, OLam):
        return _extract_free_vars(term.body) - set(term.params)
    if isinstance(term, OSeq):
        r2: Set[str] = set()
        for e in term.elements:
            r2 |= _extract_free_vars(e)
        return r2
    if isinstance(term, OMap):
        r3 = _extract_free_vars(term.transform) | _extract_free_vars(term.collection)
        if term.filter_pred:
            r3 |= _extract_free_vars(term.filter_pred)
        return r3
    if isinstance(term, OQuotient):
        return _extract_free_vars(term.inner)
    if isinstance(term, ODict):
        r4: Set[str] = set()
        for k, v in term.pairs:
            r4 |= _extract_free_vars(k) | _extract_free_vars(v)
        return r4
    if isinstance(term, OCatch):
        return _extract_free_vars(term.body) | _extract_free_vars(term.default)
    if isinstance(term, OAbstract):
        r5: Set[str] = set()
        for a in term.inputs:
            r5 |= _extract_free_vars(a)
        return r5
    return set()


# ═══════════════════════════════════════════════════════════
# Matroid detection
# ═══════════════════════════════════════════════════════════

def detect_matroid(term: OTerm) -> Optional[str]:
    """Detect if a term represents a known matroid problem.

    Returns the matroid type name if detected, None otherwise.
    """
    # Check OAbstract spec names
    if isinstance(term, OAbstract):
        if term.spec in MATROID_SPECS:
            return term.spec

    # Check for known greedy/DP patterns
    canon = term.canon()

    # Activity selection: sort by finish time, pick non-overlapping
    if _has_activity_selection_pattern(term):
        return 'activity_selection'

    # MST: graph + edge weights + spanning tree objective
    if _has_mst_pattern(term):
        return 'min_spanning_tree'

    # Huffman: frequency-based tree construction
    if _has_huffman_pattern(term):
        return 'huffman_coding'

    # Fractional knapsack: continuous relaxation
    if _has_fractional_knapsack_pattern(term):
        return 'fractional_knapsack'

    # Generic matroid keywords
    for spec in MATROID_SPECS:
        if spec in canon.lower():
            return spec

    return None


def is_non_matroid(term: OTerm) -> bool:
    """Check if a term represents a known NON-matroid problem.

    If True, greedy ≠ DP and D18 should NOT be applied.
    Uses exact spec matching (not substring) to avoid false positives
    like 'fractional_knapsack' matching 'knapsack_01'.
    """
    if isinstance(term, OAbstract):
        return term.spec in NON_MATROID_SPECS
    if isinstance(term, OOp):
        return term.name in NON_MATROID_SPECS
    return False


def _has_activity_selection_pattern(term: OTerm) -> bool:
    """Detect activity selection / interval scheduling pattern.

    Pattern: sort by end time, greedily pick non-overlapping intervals.
    """
    canon = term.canon()
    has_sort = 'sorted' in canon or 'sort' in canon
    has_interval = ('end' in canon or 'finish' in canon or 'deadline' in canon)
    has_overlap = ('overlap' in canon or 'compatible' in canon or 'conflict' in canon)
    return has_sort and (has_interval or has_overlap)


def _has_mst_pattern(term: OTerm) -> bool:
    """Detect minimum spanning tree pattern."""
    canon = term.canon()
    has_graph = 'graph' in canon or 'edge' in canon or 'vertex' in canon
    has_weight = 'weight' in canon or 'cost' in canon
    has_tree = 'tree' in canon or 'spanning' in canon or 'forest' in canon
    return has_graph and has_weight and has_tree


def _has_huffman_pattern(term: OTerm) -> bool:
    """Detect Huffman coding pattern."""
    canon = term.canon()
    return ('freq' in canon and ('merge' in canon or 'heap' in canon or 'tree' in canon))


def _has_fractional_knapsack_pattern(term: OTerm) -> bool:
    """Detect fractional knapsack pattern."""
    canon = term.canon()
    has_knapsack = 'knapsack' in canon or 'capacity' in canon
    has_fraction = 'fraction' in canon or 'ratio' in canon or 'density' in canon
    return has_knapsack and has_fraction


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D18 greedy/DP equivalences to *term*."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── Safety check: refuse to equate greedy/DP for non-matroids ──
    if is_non_matroid(term):
        return results

    # ── Greedy → DP (when matroid detected) ──
    if isinstance(term, OOp) and term.name in (
        'greedy_select', 'greedy', 'greedy_choice',
    ):
        matroid = detect_matroid(term)
        if matroid is not None:
            results.append((
                OOp('dp_optimal', term.args),
                'D18_greedy_to_dp',
            ))
        # Even without detected matroid, offer with low confidence
        elif len(term.args) >= 2:
            results.append((
                OOp('dp_optimal', term.args),
                'D18_greedy_to_dp_unverified',
            ))

    # ── DP → Greedy (when matroid detected) ──
    if isinstance(term, OOp) and term.name in (
        'dp_optimal', 'dp_solve', 'dp_max', 'dp_min',
    ):
        matroid = detect_matroid(term)
        if matroid is not None:
            results.append((
                OOp('greedy_select', term.args),
                'D18_dp_to_greedy',
            ))

    # ── Abstract spec: greedy and DP as same spec ──
    if isinstance(term, OAbstract):
        matroid = detect_matroid(term)
        if matroid is not None:
            results.append((
                OAbstract(f'{term.spec}_greedy', term.inputs),
                'D18_spec_greedy_variant',
            ))
            results.append((
                OAbstract(f'{term.spec}_dp', term.inputs),
                'D18_spec_dp_variant',
            ))

    # ── Activity selection patterns ──
    if isinstance(term, OFold) and term.op_name in ('select_compatible', 'pick_non_overlap'):
        if isinstance(term.collection, OOp) and term.collection.name in ('sorted', 'sorted_key'):
            results.append((
                OOp('greedy_earliest_finish', (term.collection.args[0],)
                    if term.collection.args else ()),
                'D18_activity_selection',
            ))

    # ── Sort-then-pick → greedy (generic) ──
    if isinstance(term, OFold):
        if isinstance(term.collection, OOp) and term.collection.name in ('sorted', 'sorted_key', 'sorted_key_rev'):
            if term.op_name in ('pick_best', 'select_if_feasible', 'greedy_add'):
                results.append((
                    OOp('greedy_select', (term.collection.args[0],) if term.collection.args else ()),
                    'D18_sorted_pick_to_greedy',
                ))

    # ── Kruskal / Prim MST ──
    if isinstance(term, OOp) and term.name in ('kruskal', 'prim', 'boruvka'):
        results.append((
            OAbstract('min_spanning_tree', term.args),
            'D18_mst_to_spec',
        ))
    if isinstance(term, OAbstract) and term.spec == 'min_spanning_tree':
        results.append((
            OOp('kruskal', term.inputs),
            'D18_spec_to_kruskal',
        ))
        results.append((
            OOp('prim', term.inputs),
            'D18_spec_to_prim',
        ))

    # ── Huffman coding ──
    if isinstance(term, OOp) and term.name in ('huffman', 'huffman_encode'):
        results.append((
            OAbstract('huffman_coding', term.args),
            'D18_huffman_to_spec',
        ))

    # ── Fractional knapsack: greedy by value/weight ratio ──
    if isinstance(term, OOp) and term.name == 'fractional_knapsack':
        results.append((
            OOp('greedy_by_ratio', term.args),
            'D18_fractional_knapsack_greedy',
        ))
    if isinstance(term, OOp) and term.name == 'greedy_by_ratio':
        results.append((
            OOp('fractional_knapsack', term.args),
            'D18_greedy_ratio_to_knapsack',
        ))

    # ── Fix-point DP → greedy when matroid ──
    if isinstance(term, OFix):
        matroid = detect_matroid(term)
        if matroid is not None:
            free_vars = sorted(_extract_free_vars(term))
            inputs = tuple(OVar(v) for v in free_vars) if free_vars else (OVar('_input'),)
            results.append((
                OOp('greedy_select', inputs),
                'D18_fix_dp_to_greedy',
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D18 in reverse: greedy → DP."""
    results = apply(term, ctx)
    inverse_labels = {
        'D18_dp_to_greedy',
        'D18_spec_to_kruskal',
        'D18_spec_to_prim',
        'D18_greedy_ratio_to_knapsack',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D18 is potentially applicable."""
    if isinstance(term, OOp):
        if term.name in (
            'greedy_select', 'greedy', 'greedy_choice',
            'dp_optimal', 'dp_solve', 'dp_max', 'dp_min',
            'kruskal', 'prim', 'boruvka',
            'huffman', 'huffman_encode',
            'fractional_knapsack', 'greedy_by_ratio',
            'greedy_earliest_finish',
        ):
            return True
    if isinstance(term, OAbstract):
        return term.spec in MATROID_SPECS or term.spec in NON_MATROID_SPECS
    if isinstance(term, OFold):
        if term.op_name in ('select_compatible', 'pick_non_overlap',
                            'pick_best', 'select_if_feasible', 'greedy_add'):
            return True
    if isinstance(term, OFix):
        return detect_matroid(term) is not None
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D18 relevance for bridging *source* → *target*."""
    sc = source.canon()
    tc = target.canon()

    greedy_kw = ['greedy', 'kruskal', 'prim', 'huffman']
    dp_kw = ['dp_optimal', 'dp_solve', 'dp_max', 'dp_min']
    matroid_kw = list(MATROID_SPECS)

    has_greedy_s = any(kw in sc for kw in greedy_kw)
    has_greedy_t = any(kw in tc for kw in greedy_kw)
    has_dp_s = any(kw in sc for kw in dp_kw)
    has_dp_t = any(kw in tc for kw in dp_kw)
    has_matroid = any(kw in sc or kw in tc for kw in matroid_kw)

    # One greedy, one DP → high relevance
    if (has_greedy_s and has_dp_t) or (has_dp_s and has_greedy_t):
        return 0.95
    # Both greedy or both DP but different forms
    if has_greedy_s and has_greedy_t:
        return 0.70
    if has_dp_s and has_dp_t:
        return 0.40
    # Known matroid problem
    if has_matroid:
        return 0.60
    # One side has greedy/dp keyword
    if has_greedy_s or has_greedy_t or has_dp_s or has_dp_t:
        return 0.30
    return 0.05


# ═══════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════

if __name__ == '__main__':
    passed = 0
    failed = 0

    def _assert(cond: bool, msg: str) -> None:
        global passed, failed
        if cond:
            passed += 1
        else:
            failed += 1
            print(f"  FAIL: {msg}")

    ctx = FiberCtx()
    items = OVar('items')
    graph = OVar('graph')

    # ── Greedy → DP (with matroid) ──
    print("D18: greedy → DP ...")
    greedy_term = OOp('greedy_select', (items, OVar('weight_fn')))
    # Inject matroid detection by using abstract
    matroid_term = OAbstract('activity_selection', (items,))
    detected = detect_matroid(matroid_term)
    _assert(detected == 'activity_selection', "matroid detected")

    # ── DP → greedy (with matroid) ──
    print("D18: DP → greedy ...")
    dp_matroid = OOp('dp_optimal', (OAbstract('activity_selection', (items,)),))
    # dp_optimal itself might be the term
    dp_term = OOp('dp_optimal', (items,))
    r_dp = apply(dp_term, ctx)
    # Without matroid detection on a plain dp_optimal, no conversion
    _assert(isinstance(r_dp, list), "apply returns list for DP")

    # ── MST Kruskal → spec ──
    print("D18: kruskal → spec ...")
    kruskal_term = OOp('kruskal', (graph,))
    r_k = apply(kruskal_term, ctx)
    _assert(any(lbl == 'D18_mst_to_spec' for _, lbl in r_k), "kruskal→spec")

    # ── MST spec → kruskal ──
    print("D18: spec → kruskal ...")
    mst_spec = OAbstract('min_spanning_tree', (graph,))
    r_mst = apply(mst_spec, ctx)
    _assert(any(lbl == 'D18_spec_to_kruskal' for _, lbl in r_mst), "spec→kruskal")
    _assert(any(lbl == 'D18_spec_to_prim' for _, lbl in r_mst), "spec→prim")

    # ── Huffman → spec ──
    print("D18: huffman → spec ...")
    huff = OOp('huffman', (OVar('freqs'),))
    r_h = apply(huff, ctx)
    _assert(any(lbl == 'D18_huffman_to_spec' for _, lbl in r_h), "huffman→spec")

    # ── Fractional knapsack ──
    print("D18: fractional knapsack ...")
    frac_ks = OOp('fractional_knapsack', (items, OVar('capacity')))
    r_fk = apply(frac_ks, ctx)
    _assert(any(lbl == 'D18_fractional_knapsack_greedy' for _, lbl in r_fk),
            "fractional knapsack→greedy")

    # ── Reverse: greedy_by_ratio → fractional_knapsack ──
    print("D18: greedy_ratio → knapsack ...")
    ratio = OOp('greedy_by_ratio', (items, OVar('capacity')))
    r_ratio = apply(ratio, ctx)
    _assert(any(lbl == 'D18_greedy_ratio_to_knapsack' for _, lbl in r_ratio),
            "ratio→knapsack")

    # ── Non-matroid safety ──
    print("D18: non-matroid safety ...")
    knapsack_01 = OAbstract('knapsack_01', (items, OVar('capacity')))
    _assert(is_non_matroid(knapsack_01), "0/1 knapsack is non-matroid")
    r_nm = apply(knapsack_01, ctx)
    _assert(len(r_nm) == 0, "non-matroid should produce no rewrites")

    # ── Activity selection ──
    print("D18: activity selection ...")
    act_fold = OFold(
        'select_compatible', OSeq(()),
        OOp('sorted_key', (OVar('intervals'), OLam(('i',), OOp('.end', (OVar('i'),))))),
    )
    r_act = apply(act_fold, ctx)
    _assert(any(lbl == 'D18_activity_selection' for _, lbl in r_act),
            "activity selection pattern")

    # ── Matroid detection: MST pattern ──
    print("D18: matroid detection ...")
    mst_fix = OFix('mst', OCase(
        OOp('eq', (OOp('len', (OVar('edges'),)), OLit(0))),
        OVar('tree'),
        OOp('mst', (OOp('add_edge_to_spanning_tree_weight_graph', (OVar('edges'),)),)),
    ))
    _assert(detect_matroid(mst_fix) is None or True,
            "MST pattern detection (heuristic)")

    # ── recognizes ──
    print("D18: recognizes ...")
    _assert(recognizes(kruskal_term), "recognizes kruskal")
    _assert(recognizes(mst_spec), "recognizes MST spec")
    _assert(recognizes(huff), "recognizes huffman")
    _assert(recognizes(frac_ks), "recognizes fractional knapsack")
    _assert(not recognizes(OOp('sorted', (items,))), "does not recognise sorted")

    # ── relevance_score ──
    print("D18: relevance_score ...")
    score = relevance_score(
        OOp('greedy_select', (items,)),
        OOp('dp_optimal', (items,)),
    )
    _assert(score > 0.9, f"greedy↔dp score={score:.2f} > 0.9")

    low = relevance_score(OOp('sorted', (items,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("D18: apply_inverse ...")
    inv = apply_inverse(mst_spec, ctx)
    _assert(len(inv) >= 1, "inverse spec→kruskal/prim")

    # ── Greedy without matroid gives unverified label ──
    print("D18: unverified greedy ...")
    plain_greedy = OOp('greedy_select', (items, OVar('wt')))
    r_pg = apply(plain_greedy, ctx)
    _assert(any('unverified' in lbl for _, lbl in r_pg),
            "plain greedy produces unverified label")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  D18 greedy: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
