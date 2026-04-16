"""D34: Precomputation / Lookup Table (Theorem 34.1).

Compute-on-demand ↔ precomputed lookup table.

Mathematical foundation:
  For a function  f: D → C  where D is finite (or bounded), the
  extensional representation  TABLE = {x: f(x) for x in D}  is
  equal to f as a morphism in Set:

    TABLE[x] = f(x)   for all x ∈ D.

  This is the tautological equivalence of intensional (rule-based)
  and extensional (table-based) function representation.

  Prefix sums are the special case where f(i) = Σ_{j<i} a[j]:
    prefix[i] = sum(a[:i])  by definition,
  and partial_sum[i] = partial_sum[i-1] + a[i]  by the recurrence.

Covers:
  • f(x) ↔ TABLE[x] where TABLE = {x: f(x) for x in domain}
  • Prefix sum: sum(a[:i]) ↔ prefix[i]
  • Cumulative product, running min/max
  • Fibonacci via precomputed table vs recursive
  • Memoization table (static, not dynamic — see D16 for memo)
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

AXIOM_NAME = 'D34_precompute'
AXIOM_CATEGORY = 'algebraic_simplification'

SOUNDNESS_PROOF = """
Theorem 34.1 (Extensional-Intensional Equivalence):
  For f: D → C with D finite,
    f  ≡  (λx. TABLE[x])  where TABLE = {x: f(x) for x in D}
  as morphisms in Set.

Proof:
  For any x ∈ D:
    TABLE[x] = f(x)   (by construction of TABLE)
  Hence the two morphisms agree on all inputs.  ∎

Corollary 34.1.1 (Prefix Sum):
  Let prefix[0] = 0, prefix[i] = prefix[i-1] + a[i-1].
  Then prefix[i] = sum(a[:i]) for all 0 ≤ i ≤ n.

Proof by induction on i:
  Base: prefix[0] = 0 = sum(a[:0]).  ✓
  Step: prefix[i] = prefix[i-1] + a[i-1]
      = sum(a[:i-1]) + a[i-1]   (IH)
      = sum(a[:i]).  ✓  ∎

Corollary 34.1.2 (Cumulative Fold):
  For any associative binary op ⊕ with identity e,
    cumulative[i] = fold(⊕, e, a[:i])
  can be computed by the recurrence:
    cumulative[0] = e
    cumulative[i] = cumulative[i-1] ⊕ a[i-1].
"""

COMPOSES_WITH = ['D16_memo', 'D05_fold_universal', 'D14_indexing']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'function to lookup table',
        'before': "f(x)",
        'after': "TABLE[x]  # TABLE = {x: f(x) for x in domain}",
        'axiom': 'D34_func_to_table',
    },
    {
        'name': 'lookup table to function',
        'before': "TABLE[x]",
        'after': "f(x)",
        'axiom': 'D34_table_to_func',
    },
    {
        'name': 'sum(a[:i]) to prefix sum',
        'before': "sum(a[:i])",
        'after': "prefix[i]",
        'axiom': 'D34_sum_slice_to_prefix',
    },
    {
        'name': 'prefix sum to sum slice',
        'before': "prefix[i]",
        'after': "sum(a[:i])",
        'axiom': 'D34_prefix_to_sum_slice',
    },
    {
        'name': 'range sum via prefix difference',
        'before': "sum(a[i:j])",
        'after': "prefix[j] - prefix[i]",
        'axiom': 'D34_range_sum_to_prefix_diff',
    },
    {
        'name': 'cumulative product',
        'before': "product(a[:i])",
        'after': "cum_prod[i]",
        'axiom': 'D34_cumulative_product',
    },
]


# ═══════════════════════════════════════════════════════════
# Helper: fiber context
# ═══════════════════════════════════════════════════════════

@dataclass
class FiberCtx:
    """Lightweight fiber context for standalone axiom evaluation."""
    param_duck_types: Dict[str, str] = field(default_factory=dict)


def _extract_free_vars(term: OTerm) -> Set[str]:
    """All free variable names in *term*."""
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
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D34 precomputation / lookup table equivalences.

    Returns list of (rewritten_term, axiom_label) pairs.
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── sum(a[:i]) → prefix_sum[i] ──
    # Pattern: OOp('sum', (OOp('slice', (a,)) or OOp('getitem', (a, slice_op)),))
    if isinstance(term, OOp) and term.name == 'sum' and len(term.args) == 1:
        inner = term.args[0]
        slice_arr, slice_end = _extract_prefix_slice(inner)
        if slice_arr is not None and slice_end is not None:
            results.append((
                OOp('getitem', (OOp('prefix_sum', (slice_arr,)), slice_end)),
                'D34_sum_slice_to_prefix',
            ))

    # ── prefix_sum[i] → sum(a[:i]) (reverse) ──
    if isinstance(term, OOp) and term.name == 'getitem' and len(term.args) == 2:
        base, idx = term.args
        if isinstance(base, OOp) and base.name == 'prefix_sum' and len(base.args) == 1:
            arr = base.args[0]
            results.append((
                OOp('sum', (OOp('getitem', (arr, OOp('slice', (OLit(None), idx)))),)),
                'D34_prefix_to_sum_slice',
            ))

    # ── sum(a[i:j]) → prefix[j] - prefix[i] (range sum) ──
    if isinstance(term, OOp) and term.name == 'sum' and len(term.args) == 1:
        inner = term.args[0]
        range_info = _extract_range_slice(inner)
        if range_info is not None:
            arr, start, end = range_info
            prefix = OOp('prefix_sum', (arr,))
            results.append((
                OOp('sub', (
                    OOp('getitem', (prefix, end)),
                    OOp('getitem', (prefix, start)),
                )),
                'D34_range_sum_to_prefix_diff',
            ))

    # ── prefix[j] - prefix[i] → sum(a[i:j]) (reverse) ──
    if isinstance(term, OOp) and term.name == 'sub' and len(term.args) == 2:
        lhs, rhs = term.args
        if (isinstance(lhs, OOp) and lhs.name == 'getitem' and len(lhs.args) == 2
                and isinstance(rhs, OOp) and rhs.name == 'getitem' and len(rhs.args) == 2):
            base_l, j = lhs.args
            base_r, i = rhs.args
            if (isinstance(base_l, OOp) and base_l.name == 'prefix_sum'
                    and isinstance(base_r, OOp) and base_r.name == 'prefix_sum'
                    and base_l.canon() == base_r.canon()):
                arr = base_l.args[0]
                results.append((
                    OOp('sum', (OOp('getitem', (arr, OOp('slice', (i, j)))),)),
                    'D34_prefix_diff_to_range_sum',
                ))

    # ── fold[add](0, a[:i]) → prefix_sum[i] ──
    if isinstance(term, OFold) and term.op_name in ('add', 'plus', 'sum'):
        if isinstance(term.init, OLit) and term.init.value == 0:
            slice_info = _extract_prefix_slice(term.collection)
            if slice_info[0] is not None:
                arr, end = slice_info
                results.append((
                    OOp('getitem', (OOp('prefix_sum', (arr,)), end)),
                    'D34_fold_sum_to_prefix',
                ))

    # ── fold[mul](1, a[:i]) → cumulative_product[i] ──
    if isinstance(term, OFold) and term.op_name in ('mul', 'mult', 'multiply'):
        if isinstance(term.init, OLit) and term.init.value == 1:
            slice_info = _extract_prefix_slice(term.collection)
            if slice_info[0] is not None:
                arr, end = slice_info
                results.append((
                    OOp('getitem', (OOp('cumulative_product', (arr,)), end)),
                    'D34_fold_mul_to_cum_prod',
                ))

    # ── Precomputed table: dict-comp {x: f(x) for x in domain} ──
    # This represents a lookup-table construction
    # Only valid when there's no filter (filter_map ≠ lookup_table)
    if isinstance(term, OMap) and term.filter_pred is None:
        tf = term.transform
        coll = term.collection
        if isinstance(tf, OLam) and len(tf.params) == 1:
            # The map builds {x: f(x) for x in domain}
            results.append((
                OOp('lookup_table', (tf, coll)),
                'D34_map_to_lookup_table',
            ))

    # ── lookup_table access: getitem(lookup_table(f, domain), x) → f(x) ──
    if isinstance(term, OOp) and term.name == 'getitem' and len(term.args) == 2:
        base, key = term.args
        if isinstance(base, OOp) and base.name == 'lookup_table' and len(base.args) == 2:
            f_lam, _domain = base.args
            if isinstance(f_lam, OLam) and len(f_lam.params) == 1:
                # Inline: TABLE[x] → f(x) via substitution
                results.append((
                    OOp('apply_func', (f_lam, key)),
                    'D34_table_to_func',
                ))

    # ── Running min/max: min(a[:i]) ↔ running_min[i] ──
    if isinstance(term, OOp) and term.name in ('min', 'max') and len(term.args) == 1:
        inner = term.args[0]
        slice_arr, slice_end = _extract_prefix_slice(inner)
        if slice_arr is not None and slice_end is not None:
            op = 'running_min' if term.name == 'min' else 'running_max'
            results.append((
                OOp('getitem', (OOp(op, (slice_arr,)), slice_end)),
                f'D34_{term.name}_slice_to_running',
            ))

    # ── OFix (recursion) with memoizable pattern → lookup table ──
    if isinstance(term, OFix):
        results.append((
            OOp('precomputed_fix', (OLit(term.name), term.body)),
            'D34_recursive_to_precomputed',
        ))

    # ── itertools.accumulate(a, op) → cumulative fold ──
    if isinstance(term, OOp) and term.name == 'accumulate' and len(term.args) >= 1:
        arr = term.args[0]
        op = term.args[1] if len(term.args) > 1 else OLit('add')
        results.append((
            OOp('cumulative_fold', (op, arr)),
            'D34_accumulate_to_cumulative',
        ))

    return results


def _extract_prefix_slice(term: OTerm) -> Tuple[Optional[OTerm], Optional[OTerm]]:
    """Extract (array, end_index) from a[:i] patterns."""
    # Pattern: OOp('getitem', (arr, OOp('slice', (OLit(None), end))))
    if isinstance(term, OOp) and term.name == 'getitem' and len(term.args) == 2:
        arr, idx = term.args
        if isinstance(idx, OOp) and idx.name == 'slice' and len(idx.args) == 2:
            start, end = idx.args
            if isinstance(start, OLit) and start.value is None:
                return (arr, end)
    # Pattern: OOp('slice', (arr,)) — simplified slice
    if isinstance(term, OOp) and term.name == 'slice' and len(term.args) == 1:
        return (term.args[0], OUnknown('end'))
    return (None, None)


def _extract_range_slice(term: OTerm) -> Optional[Tuple[OTerm, OTerm, OTerm]]:
    """Extract (array, start, end) from a[i:j] patterns."""
    if isinstance(term, OOp) and term.name == 'getitem' and len(term.args) == 2:
        arr, idx = term.args
        if isinstance(idx, OOp) and idx.name == 'slice' and len(idx.args) == 2:
            start, end = idx.args
            if not (isinstance(start, OLit) and start.value is None):
                return (arr, start, end)
    return None


# ═══════════════════════════════════════════════════════════
# Inverse axiom
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D34 in reverse: precomputed → on-demand."""
    results = apply(term, ctx)
    inverse_labels = {
        'D34_prefix_to_sum_slice',
        'D34_prefix_diff_to_range_sum',
        'D34_table_to_func',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D34 is potentially applicable to *term*."""
    if isinstance(term, OOp):
        if term.name in ('sum', 'min', 'max', 'accumulate'):
            return True
        if term.name in ('prefix_sum', 'cumulative_product',
                         'running_min', 'running_max',
                         'lookup_table', 'precomputed_fix',
                         'cumulative_fold'):
            return True
        if term.name == 'getitem' and len(term.args) == 2:
            base = term.args[0]
            if isinstance(base, OOp) and base.name in (
                'prefix_sum', 'cumulative_product',
                'running_min', 'running_max', 'lookup_table',
            ):
                return True
        if term.name == 'sub' and len(term.args) == 2:
            lhs, rhs = term.args
            if (isinstance(lhs, OOp) and lhs.name == 'getitem'
                    and isinstance(rhs, OOp) and rhs.name == 'getitem'):
                return True
    if isinstance(term, OFold):
        if term.op_name in ('add', 'plus', 'sum', 'mul', 'mult', 'multiply'):
            return True
    if isinstance(term, OFix):
        return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score how relevant D34 is for bridging *source* → *target*."""
    sc = source.canon()
    tc = target.canon()

    precomp_kw = ('prefix_sum(', 'cumulative_product(', 'running_min(',
                  'running_max(', 'lookup_table(', 'precomputed_fix(',
                  'cumulative_fold(', 'accumulate(')
    demand_kw = ('sum(', 'fold[add]', 'fold[mul]', 'min(', 'max(', 'fix[')

    has_precomp_s = any(k in sc for k in precomp_kw)
    has_precomp_t = any(k in tc for k in precomp_kw)
    has_demand_s = any(k in sc for k in demand_kw)
    has_demand_t = any(k in tc for k in demand_kw)

    if (has_precomp_s and has_demand_t) or (has_demand_s and has_precomp_t):
        return 0.95
    if has_precomp_s != has_precomp_t:
        return 0.85
    if has_demand_s and has_demand_t:
        return 0.50
    if has_precomp_s or has_precomp_t or has_demand_s or has_demand_t:
        return 0.40
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
    a = OVar('a')
    i = OVar('i')
    j = OVar('j')

    # ── sum(a[:i]) → prefix_sum[i] ──
    print("D34: sum(a[:i]) → prefix_sum[i] ...")
    sum_slice = OOp('sum', (OOp('getitem', (a, OOp('slice', (OLit(None), i)))),))
    r = apply(sum_slice, ctx)
    _assert(any(lbl == 'D34_sum_slice_to_prefix' for _, lbl in r), "sum→prefix")
    prefix_results = [t for t, lbl in r if lbl == 'D34_sum_slice_to_prefix']
    _assert(len(prefix_results) >= 1, "got prefix result")

    # ── prefix_sum[i] → sum(a[:i]) (reverse) ──
    print("D34: prefix_sum[i] → sum(a[:i]) ...")
    prefix_access = OOp('getitem', (OOp('prefix_sum', (a,)), i))
    r2 = apply(prefix_access, ctx)
    _assert(any(lbl == 'D34_prefix_to_sum_slice' for _, lbl in r2), "prefix→sum")

    # ── Roundtrip ──
    print("D34: roundtrip sum↔prefix ...")
    fwd = [t for t, lbl in r if lbl == 'D34_sum_slice_to_prefix']
    _assert(len(fwd) >= 1, "roundtrip step 1")
    back = apply(fwd[0], ctx)
    _assert(any(lbl == 'D34_prefix_to_sum_slice' for _, lbl in back), "roundtrip step 2")

    # ── sum(a[i:j]) → prefix[j] - prefix[i] ──
    print("D34: range sum → prefix diff ...")
    range_sum = OOp('sum', (OOp('getitem', (a, OOp('slice', (i, j)))),))
    r3 = apply(range_sum, ctx)
    _assert(any(lbl == 'D34_range_sum_to_prefix_diff' for _, lbl in r3), "range→diff")

    # ── prefix[j] - prefix[i] → sum(a[i:j]) (reverse) ──
    print("D34: prefix diff → range sum ...")
    prefix_diff = OOp('sub', (
        OOp('getitem', (OOp('prefix_sum', (a,)), j)),
        OOp('getitem', (OOp('prefix_sum', (a,)), i)),
    ))
    r4 = apply(prefix_diff, ctx)
    _assert(any(lbl == 'D34_prefix_diff_to_range_sum' for _, lbl in r4), "diff→range")

    # ── fold[add](0, a[:i]) → prefix_sum[i] ──
    print("D34: fold[add] → prefix_sum ...")
    fold_sum = OFold('add', OLit(0), OOp('getitem', (a, OOp('slice', (OLit(None), i)))))
    r5 = apply(fold_sum, ctx)
    _assert(any(lbl == 'D34_fold_sum_to_prefix' for _, lbl in r5), "fold→prefix")

    # ── fold[mul](1, a[:i]) → cumulative_product[i] ──
    print("D34: fold[mul] → cumulative_product ...")
    fold_mul = OFold('mul', OLit(1), OOp('getitem', (a, OOp('slice', (OLit(None), i)))))
    r6 = apply(fold_mul, ctx)
    _assert(any(lbl == 'D34_fold_mul_to_cum_prod' for _, lbl in r6), "fold→cum_prod")

    # ── min(a[:i]) → running_min[i] ──
    print("D34: min(a[:i]) → running_min[i] ...")
    min_slice = OOp('min', (OOp('getitem', (a, OOp('slice', (OLit(None), i)))),))
    r7 = apply(min_slice, ctx)
    _assert(any(lbl == 'D34_min_slice_to_running' for _, lbl in r7), "min→running")

    # ── max(a[:i]) → running_max[i] ──
    print("D34: max(a[:i]) → running_max[i] ...")
    max_slice = OOp('max', (OOp('getitem', (a, OOp('slice', (OLit(None), i)))),))
    r8 = apply(max_slice, ctx)
    _assert(any(lbl == 'D34_max_slice_to_running' for _, lbl in r8), "max→running")

    # ── Recursive → precomputed ──
    print("D34: recursive → precomputed ...")
    rec = OFix('fib', OCase(
        OOp('lt', (OVar('n'), OLit(2))),
        OVar('n'),
        OOp('add', (OFix('fib', OOp('sub', (OVar('n'), OLit(1)))),
                     OFix('fib', OOp('sub', (OVar('n'), OLit(2)))))),
    ))
    r9 = apply(rec, ctx)
    _assert(any(lbl == 'D34_recursive_to_precomputed' for _, lbl in r9), "rec→precomp")

    # ── accumulate → cumulative fold ──
    print("D34: accumulate → cumulative fold ...")
    accum = OOp('accumulate', (a, OLit('add')))
    r10 = apply(accum, ctx)
    _assert(any(lbl == 'D34_accumulate_to_cumulative' for _, lbl in r10), "accum→cum")

    # ── Map → lookup table ──
    print("D34: map → lookup table ...")
    table_build = OMap(
        OLam(('x',), OOp('f', (OVar('x'),))),
        OVar('domain'),
    )
    r11 = apply(table_build, ctx)
    _assert(any(lbl == 'D34_map_to_lookup_table' for _, lbl in r11), "map→table")

    # ── lookup_table access → function call ──
    print("D34: table access → function call ...")
    table_access = OOp('getitem', (
        OOp('lookup_table', (
            OLam(('x',), OOp('f', (OVar('x'),))),
            OVar('domain'),
        )),
        OVar('key'),
    ))
    r12 = apply(table_access, ctx)
    _assert(any(lbl == 'D34_table_to_func' for _, lbl in r12), "table→func")

    # ── recognizes() ──
    print("D34: recognizes ...")
    _assert(recognizes(sum_slice), "recognizes sum")
    _assert(recognizes(prefix_access), "recognizes prefix_sum access")
    _assert(recognizes(fold_sum), "recognizes fold[add]")
    _assert(recognizes(rec), "recognizes OFix")
    _assert(recognizes(accum), "recognizes accumulate")
    _assert(not recognizes(OOp('sorted', (a,))), "does not recognise sorted")

    # ── relevance_score ──
    print("D34: relevance_score ...")
    score = relevance_score(sum_slice, prefix_access)
    _assert(score > 0.8, f"sum↔prefix score={score:.2f} > 0.8")
    low = relevance_score(OOp('sorted', (a,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("D34: apply_inverse ...")
    inv = apply_inverse(prefix_access, ctx)
    _assert(len(inv) >= 1, "inverse produces sum slice")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  D34 precompute: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
