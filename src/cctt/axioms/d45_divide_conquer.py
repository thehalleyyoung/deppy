"""D45: Divide-and-Conquer ↔ Iterative Equivalences (Theorem 29.3.1).

Recursive divide-and-conquer algorithms are equivalent to their
iterative (bottom-up or explicit-stack) implementations.

Mathematical foundation:
  Every recursive divide-and-conquer algorithm defines a recursion
  tree.  The recursive implementation traverses this tree top-down
  (DFS), while the iterative implementation traverses bottom-up
  (level-order) or uses an explicit stack.

  For a recurrence T(n) = a·T(n/b) + f(n) (Master Theorem form),
  both recursive and iterative implementations compute the same
  function — they differ only in traversal order of the recursion
  tree.

  Key principle: structural induction on the recursion tree shows
  that both implementations produce the same output at every node.

Covers:
  • Merge sort: recursive ↔ bottom-up iterative
  • Binary search: recursive ↔ iterative while loop
  • Power/exponentiation: recursive ↔ iterative squaring
  • Tree DFS: recursive ↔ explicit stack
  • Quick select: recursive ↔ iterative with stack
  • Generic D&C ↔ iterative with explicit stack
  • Master theorem: same recurrence, different traversal
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

AXIOM_NAME = 'D45_divide_conquer'
AXIOM_CATEGORY = 'algorithmic_patterns'  # §29

SOUNDNESS_PROOF = """
Theorem 29.3.1 (D&C Recursive ↔ Iterative):
  Let f be a divide-and-conquer function with recurrence:
    f(x) = combine(f(split_1(x)), ..., f(split_a(x)), base(x))
  Then:
    f_recursive(x) = f_iterative(x)

  where f_iterative uses bottom-up computation or an explicit stack.

Proof:
  By structural induction on the recursion tree T(x):
  - Base case: |x| ≤ threshold ⟹ both return base(x).
  - Inductive step: Assume f_recursive(split_i(x)) = f_iterative(split_i(x))
    for all i.  Then both compute combine(...) with the same arguments.
  The bottom-up iterative processes nodes in reverse topological order
  of T(x), ensuring all children are computed before their parent.  ∎

Theorem 29.3.2 (Merge Sort: Recursive ↔ Bottom-Up):
  merge_sort_recursive(xs) = merge_sort_bottom_up(xs)

Proof:
  Both produce a sorted permutation of xs via pairwise merges.
  The recursive version merges top-down; the iterative version
  starts with runs of size 1 and doubles.  At each level, the
  same pairs are merged (possibly in different order), and merge
  is associative on sorted subsequences.  ∎

Theorem 29.3.3 (Binary Search: Recursive ↔ Iterative):
  bsearch_recursive(xs, target) = bsearch_iterative(xs, target)

Proof:
  Both maintain invariant: target ∈ xs[lo:hi].  Each step halves
  the range.  The recursive version passes (lo, hi) as parameters;
  the iterative version updates them in a while loop.  The sequence
  of (lo, hi) pairs is identical.  ∎

Theorem 29.3.4 (Power: Recursive ↔ Iterative Squaring):
  power_recursive(x, n) = power_iterative(x, n) = x^n

Proof:
  The recursive version computes x^n = x^(n/2) · x^(n/2) (· x if n odd).
  The iterative version scans bits of n from LSB to MSB, accumulating
  squares.  Both compute the same product of powers of x.  ∎

Theorem 29.3.5 (Tree DFS: Recursive ↔ Explicit Stack):
  dfs_recursive(root) = dfs_stack(root)

Proof:
  The call stack in the recursive version is isomorphic to the
  explicit stack.  Both visit nodes in the same order (pre-order,
  in-order, or post-order depending on when the node is processed
  relative to recursive calls / stack pushes).  ∎
"""

COMPOSES_WITH = ['D07_tailrec', 'D09_stack_rec', 'D16_memo_dp', 'D19_sort_scan']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'Merge sort: recursive to bottom-up',
        'before': "merge_sort_recursive(xs)",
        'after': "merge_sort_bottom_up(xs)",
        'axiom': 'D45_mergesort_rec_to_iter',
    },
    {
        'name': 'Binary search: recursive to iterative',
        'before': "bsearch_recursive(xs, target)",
        'after': "bsearch_iterative(xs, target)",
        'axiom': 'D45_bsearch_rec_to_iter',
    },
    {
        'name': 'Power: recursive to iterative squaring',
        'before': "power_recursive(x, n)",
        'after': "power_iterative(x, n)",
        'axiom': 'D45_power_rec_to_iter',
    },
    {
        'name': 'Tree DFS: recursive to stack',
        'before': "dfs_recursive(root)",
        'after': "dfs_stack(root)",
        'axiom': 'D45_dfs_rec_to_stack',
    },
    {
        'name': 'Quick select: recursive to iterative',
        'before': "quickselect_recursive(xs, k)",
        'after': "quickselect_iterative(xs, k)",
        'axiom': 'D45_qselect_rec_to_iter',
    },
]

# ── Known recursive D&C operations ──
RECURSIVE_DC_OPS: FrozenSet[str] = frozenset({
    'merge_sort_recursive', 'mergesort_recursive', 'merge_sort_rec',
    'bsearch_recursive', 'binary_search_recursive', 'bsearch_rec',
    'power_recursive', 'pow_recursive', 'fast_pow_recursive',
    'dfs_recursive', 'dfs_rec', 'tree_dfs_recursive',
    'quickselect_recursive', 'qselect_recursive', 'quickselect_rec',
    'quicksort_recursive', 'quicksort_rec',
    'divide_conquer', 'dnc_recursive',
})

# ── Known iterative counterparts ──
ITERATIVE_DC_OPS: FrozenSet[str] = frozenset({
    'merge_sort_bottom_up', 'mergesort_iterative', 'merge_sort_iter',
    'bsearch_iterative', 'binary_search_iterative', 'bsearch_iter',
    'power_iterative', 'pow_iterative', 'fast_pow_iterative',
    'dfs_stack', 'dfs_iterative', 'tree_dfs_stack',
    'quickselect_iterative', 'qselect_iterative', 'quickselect_iter',
    'quicksort_iterative', 'quicksort_iter',
    'divide_conquer_iter', 'dnc_iterative',
})

# ── Mapping from recursive → iterative names ──
_REC_TO_ITER = {
    'merge_sort_recursive': 'merge_sort_bottom_up',
    'mergesort_recursive': 'mergesort_iterative',
    'merge_sort_rec': 'merge_sort_iter',
    'bsearch_recursive': 'bsearch_iterative',
    'binary_search_recursive': 'binary_search_iterative',
    'bsearch_rec': 'bsearch_iter',
    'power_recursive': 'power_iterative',
    'pow_recursive': 'pow_iterative',
    'fast_pow_recursive': 'fast_pow_iterative',
    'dfs_recursive': 'dfs_stack',
    'dfs_rec': 'dfs_iterative',
    'tree_dfs_recursive': 'tree_dfs_stack',
    'quickselect_recursive': 'quickselect_iterative',
    'qselect_recursive': 'qselect_iterative',
    'quickselect_rec': 'quickselect_iter',
    'quicksort_recursive': 'quicksort_iterative',
    'quicksort_rec': 'quicksort_iter',
    'divide_conquer': 'divide_conquer_iter',
    'dnc_recursive': 'dnc_iterative',
}

_ITER_TO_REC = {v: k for k, v in _REC_TO_ITER.items()}


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
# Pattern detection
# ═══════════════════════════════════════════════════════════

def _is_recursive_dc(term: OTerm) -> bool:
    """Detect recursive divide-and-conquer."""
    if isinstance(term, OOp) and term.name in RECURSIVE_DC_OPS:
        return True
    if isinstance(term, OFix):
        return True
    return False


def _is_iterative_dc(term: OTerm) -> bool:
    """Detect iterative divide-and-conquer."""
    if isinstance(term, OOp) and term.name in ITERATIVE_DC_OPS:
        return True
    return False


def _is_binary_split(term: OTerm) -> bool:
    """Detect binary splitting pattern: f(left_half) + f(right_half)."""
    if isinstance(term, OOp) and term.name in ('add', 'merge', 'combine', 'concat'):
        if len(term.args) == 2:
            a, b = term.args
            if isinstance(a, OFix) and isinstance(b, OFix):
                return a.name == b.name
    return False


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D45 divide-and-conquer ↔ iterative equivalences."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── Named recursive → iterative ──
    if isinstance(term, OOp) and term.name in _REC_TO_ITER:
        iter_name = _REC_TO_ITER[term.name]
        results.append((
            OOp(iter_name, term.args),
            'D45_rec_to_iter',
        ))

    # ── Named iterative → recursive ──
    if isinstance(term, OOp) and term.name in _ITER_TO_REC:
        rec_name = _ITER_TO_REC[term.name]
        results.append((
            OOp(rec_name, term.args),
            'D45_iter_to_rec',
        ))

    # ── OFix (structural recursion) → iterative ──
    if isinstance(term, OFix):
        free = sorted(_extract_free_vars(term))
        inputs = tuple(OVar(v) for v in free) if free else (OVar('_input'),)
        # Generic D&C recursion → explicit stack
        results.append((
            OOp('iterative_stack', inputs),
            'D45_fix_to_stack',
        ))
        # If it looks like binary split, also offer bottom-up
        if _is_binary_split(term.body):
            results.append((
                OOp('bottom_up_iter', inputs),
                'D45_fix_to_bottom_up',
            ))

    # ── Merge sort specific ──
    if isinstance(term, OOp) and term.name in ('merge_sort', 'mergesort'):
        results.append((
            OOp('merge_sort_recursive', term.args),
            'D45_mergesort_to_rec',
        ))
        results.append((
            OOp('merge_sort_bottom_up', term.args),
            'D45_mergesort_to_bottom_up',
        ))

    # ── Binary search specific ──
    if isinstance(term, OOp) and term.name in ('binary_search', 'bsearch', 'bisect'):
        results.append((
            OOp('bsearch_recursive', term.args),
            'D45_bsearch_to_rec',
        ))
        results.append((
            OOp('bsearch_iterative', term.args),
            'D45_bsearch_to_iter',
        ))

    # ── Power / exponentiation ──
    if isinstance(term, OOp) and term.name in ('pow', 'power', 'fast_pow'):
        results.append((
            OOp('power_recursive', term.args),
            'D45_power_to_rec',
        ))
        results.append((
            OOp('power_iterative', term.args),
            'D45_power_to_iter',
        ))

    # ── Tree DFS ──
    if isinstance(term, OOp) and term.name in ('dfs', 'tree_dfs', 'depth_first'):
        results.append((
            OOp('dfs_recursive', term.args),
            'D45_dfs_to_rec',
        ))
        results.append((
            OOp('dfs_stack', term.args),
            'D45_dfs_to_stack',
        ))

    # ── Quick select ──
    if isinstance(term, OOp) and term.name in ('quickselect', 'qselect', 'nth_element'):
        results.append((
            OOp('quickselect_recursive', term.args),
            'D45_qselect_to_rec',
        ))
        results.append((
            OOp('quickselect_iterative', term.args),
            'D45_qselect_to_iter',
        ))

    # ── Abstract specs ──
    if isinstance(term, OAbstract):
        if 'sort' in term.spec and 'merge' in term.spec:
            results.append((OOp('merge_sort_recursive', term.inputs), 'D45_spec_to_mergesort_rec'))
            results.append((OOp('merge_sort_bottom_up', term.inputs), 'D45_spec_to_mergesort_iter'))
        if 'search' in term.spec and 'binary' in term.spec:
            results.append((OOp('bsearch_recursive', term.inputs), 'D45_spec_to_bsearch_rec'))
            results.append((OOp('bsearch_iterative', term.inputs), 'D45_spec_to_bsearch_iter'))
        if 'divide' in term.spec and 'conquer' in term.spec:
            results.append((OOp('divide_conquer', term.inputs), 'D45_spec_to_dc_rec'))
            results.append((OOp('divide_conquer_iter', term.inputs), 'D45_spec_to_dc_iter'))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D45 in reverse: iterative → recursive."""
    results = apply(term, ctx)
    inverse_labels = {
        'D45_iter_to_rec',
        'D45_mergesort_to_rec',
        'D45_bsearch_to_rec',
        'D45_power_to_rec',
        'D45_dfs_to_rec',
        'D45_qselect_to_rec',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D45 is potentially applicable."""
    if isinstance(term, OOp):
        if term.name in RECURSIVE_DC_OPS | ITERATIVE_DC_OPS:
            return True
        if term.name in ('merge_sort', 'mergesort', 'binary_search',
                         'bsearch', 'bisect', 'pow', 'power', 'fast_pow',
                         'dfs', 'tree_dfs', 'depth_first',
                         'quickselect', 'qselect', 'nth_element'):
            return True
    if isinstance(term, OFix):
        return True
    if isinstance(term, OAbstract):
        spec = term.spec
        return any(kw in spec for kw in ('merge_sort', 'binary_search',
                                          'divide_conquer', 'power'))
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D45 relevance for bridging *source* → *target*."""
    sc = source.canon()
    tc = target.canon()

    rec_kw = ['recursive', '_rec', 'fix[']
    iter_kw = ['iterative', '_iter', 'bottom_up', 'stack', 'while']

    has_rec_s = any(kw in sc for kw in rec_kw)
    has_rec_t = any(kw in tc for kw in rec_kw)
    has_iter_s = any(kw in sc for kw in iter_kw)
    has_iter_t = any(kw in tc for kw in iter_kw)

    dc_kw = ['merge_sort', 'bsearch', 'binary_search', 'power', 'dfs',
             'quickselect', 'divide_conquer']
    has_dc_s = any(kw in sc for kw in dc_kw)
    has_dc_t = any(kw in tc for kw in dc_kw)

    # One recursive, one iterative → high relevance
    if (has_rec_s and has_iter_t) or (has_iter_s and has_rec_t):
        return 0.95
    # Same D&C algorithm, different forms
    if has_dc_s and has_dc_t:
        return 0.80
    # One side recursive or iterative
    if has_rec_s or has_rec_t or has_iter_s or has_iter_t:
        return 0.40
    if has_dc_s or has_dc_t:
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
    xs = OVar('xs')
    target = OVar('target')
    x = OVar('x')
    n = OVar('n')
    root = OVar('root')
    k = OVar('k')

    # ── Merge sort: recursive → bottom-up ──
    print("D45: merge sort recursive → bottom-up ...")
    ms_rec = OOp('merge_sort_recursive', (xs,))
    r_ms = apply(ms_rec, ctx)
    _assert(any(lbl == 'D45_rec_to_iter' for _, lbl in r_ms),
            "mergesort_rec→iter")

    # ── Merge sort: bottom-up → recursive ──
    print("D45: merge sort bottom-up → recursive ...")
    ms_iter = OOp('merge_sort_bottom_up', (xs,))
    r_mi = apply(ms_iter, ctx)
    _assert(any(lbl == 'D45_iter_to_rec' for _, lbl in r_mi),
            "mergesort_iter→rec")

    # ── Binary search: recursive → iterative ──
    print("D45: binary search recursive → iterative ...")
    bs_rec = OOp('bsearch_recursive', (xs, target))
    r_bs = apply(bs_rec, ctx)
    _assert(any(lbl == 'D45_rec_to_iter' for _, lbl in r_bs),
            "bsearch_rec→iter")

    # ── Power: recursive → iterative ──
    print("D45: power recursive → iterative ...")
    pw_rec = OOp('power_recursive', (x, n))
    r_pw = apply(pw_rec, ctx)
    _assert(any(lbl == 'D45_rec_to_iter' for _, lbl in r_pw),
            "power_rec→iter")

    # ── DFS: recursive → stack ──
    print("D45: DFS recursive → stack ...")
    dfs_rec = OOp('dfs_recursive', (root,))
    r_dfs = apply(dfs_rec, ctx)
    _assert(any(lbl == 'D45_rec_to_iter' for _, lbl in r_dfs),
            "dfs_rec→stack")

    # ── Quick select: recursive → iterative ──
    print("D45: quickselect recursive → iterative ...")
    qs_rec = OOp('quickselect_recursive', (xs, k))
    r_qs = apply(qs_rec, ctx)
    _assert(any(lbl == 'D45_rec_to_iter' for _, lbl in r_qs),
            "qselect_rec→iter")

    # ── OFix → iterative stack ──
    print("D45: OFix → iterative stack ...")
    fix_term = OFix('f', OCase(
        OOp('eq', (OVar('n'), OLit(0))),
        OLit(1),
        OOp('mult', (OVar('n'), OFix('f', OOp('sub', (OVar('n'), OLit(1)))))),
    ))
    r_fix = apply(fix_term, ctx)
    _assert(any(lbl == 'D45_fix_to_stack' for _, lbl in r_fix),
            "fix→stack")

    # ── Generic merge sort ──
    print("D45: generic merge_sort ...")
    ms_gen = OOp('merge_sort', (xs,))
    r_gen = apply(ms_gen, ctx)
    _assert(any(lbl == 'D45_mergesort_to_rec' for _, lbl in r_gen),
            "merge_sort→rec")
    _assert(any(lbl == 'D45_mergesort_to_bottom_up' for _, lbl in r_gen),
            "merge_sort→bottom_up")

    # ── Generic binary search ──
    print("D45: generic binary_search ...")
    bs_gen = OOp('binary_search', (xs, target))
    r_bsg = apply(bs_gen, ctx)
    _assert(any(lbl == 'D45_bsearch_to_rec' for _, lbl in r_bsg),
            "bsearch→rec")
    _assert(any(lbl == 'D45_bsearch_to_iter' for _, lbl in r_bsg),
            "bsearch→iter")

    # ── Generic DFS ──
    print("D45: generic dfs ...")
    dfs_gen = OOp('dfs', (root,))
    r_dfsg = apply(dfs_gen, ctx)
    _assert(any(lbl == 'D45_dfs_to_rec' for _, lbl in r_dfsg),
            "dfs→rec")
    _assert(any(lbl == 'D45_dfs_to_stack' for _, lbl in r_dfsg),
            "dfs→stack")

    # ── Abstract spec ──
    print("D45: abstract spec ...")
    spec_ms = OAbstract('merge_sort_stable', (xs,))
    r_spec = apply(spec_ms, ctx)
    _assert(any(lbl == 'D45_spec_to_mergesort_rec' for _, lbl in r_spec),
            "spec→mergesort_rec")
    _assert(any(lbl == 'D45_spec_to_mergesort_iter' for _, lbl in r_spec),
            "spec→mergesort_iter")

    # ── recognizes ──
    print("D45: recognizes ...")
    _assert(recognizes(ms_rec), "recognizes merge sort recursive")
    _assert(recognizes(ms_iter), "recognizes merge sort iterative")
    _assert(recognizes(fix_term), "recognizes OFix")
    _assert(recognizes(bs_gen), "recognizes binary search")
    _assert(not recognizes(OOp('sorted', (xs,))), "does not recognise sorted")

    # ── relevance_score ──
    print("D45: relevance_score ...")
    score = relevance_score(
        OOp('merge_sort_recursive', (xs,)),
        OOp('merge_sort_bottom_up', (xs,)),
    )
    _assert(score > 0.9, f"rec↔iter score={score:.2f} > 0.9")

    low = relevance_score(OOp('sorted', (xs,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("D45: apply_inverse ...")
    inv = apply_inverse(ms_iter, ctx)
    _assert(len(inv) >= 1, "inverse iter→rec")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  D45 divide_conquer: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
