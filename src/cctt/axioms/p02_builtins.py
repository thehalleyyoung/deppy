"""P2: Built-in Function Equivalences (Theorem 30.2.1).

Python built-in aggregators ↔ fold / reduce / comprehension expansions.

Mathematical foundation:
  Built-in aggregators (sum, max, min, len, any, all, zip, enumerate,
  reversed) are catamorphisms — instances of the universal fold on
  the free monoid (list).  Each built-in is characterised by its
  algebra (carrier + binary operation + unit):

    sum  = fold(+, 0, xs)
    max  = fold(max₂, -∞, xs)
    len  = fold(λ(n,_). n+1, 0, xs)
    any  = fold(∨, False, xs)
    all  = fold(∧, True, xs)

  The equivalences are natural isomorphisms in the category of
  F-algebras for the list functor  F(X) = 1 + A × X.

Covers:
  • sum ↔ reduce(add, xs, 0)
  • max ↔ reduce(max_op, xs)
  • min ↔ sorted(xs)[0]
  • len ↔ sum(1 for _ in xs)
  • any ↔ reduce(or_, xs, False)
  • all ↔ not any(not x for x in xs)
  • zip ↔ index-based comprehension
  • enumerate ↔ zip(range(len(xs)), xs)
  • reversed ↔ xs[::-1]
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

AXIOM_NAME = 'P2_builtins'
AXIOM_CATEGORY = 'python_idiom'

SOUNDNESS_PROOF = """
Theorem 30.2.1 (Built-in Fold Equivalence):
  For any finite iterable xs,
    sum(xs)       ≡  fold(+, 0, xs)
    max(xs)       ≡  fold(max₂, -∞, xs)  (for non-empty xs)
    min(xs)       ≡  fold(min₂, +∞, xs)  (for non-empty xs)
    len(xs)       ≡  fold(λ(n,_). n+1, 0, xs)
    any(xs)       ≡  fold(∨, False, xs)
    all(xs)       ≡  fold(∧, True, xs)
  as morphisms  A* → B  in the category of F-algebras.

Proof sketch:
  Each built-in is defined by structural recursion on lists:
    sum([])     = 0,       sum(x:xs)  = x + sum(xs)
    len([])     = 0,       len(x:xs)  = 1 + len(xs)
    any([])     = False,   any(x:xs)  = x ∨ any(xs)
    all([])     = True,    all(x:xs)  = x ∧ all(xs)
  These are exactly the fold equations.  ∎

Corollary (Derived identities):
    all(xs) ≡ not any(not x for x in xs)     (De Morgan)
    min(xs) ≡ sorted(xs)[0]                   (sort-select)
    enumerate(xs) ≡ zip(range(len(xs)), xs)   (index pairing)
    reversed(xs) ≡ xs[::-1]                   (slice reversal)
"""

COMPOSES_WITH = ['D05_fold_universal', 'P1_comprehension', 'D01_fold_unfold']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'sum to fold',
        'before': "sum(xs)",
        'after': "fold(add, 0, xs)",
        'axiom': 'P2_sum_to_fold',
    },
    {
        'name': 'fold(add) to sum',
        'before': "fold(add, 0, xs)",
        'after': "sum(xs)",
        'axiom': 'P2_fold_to_sum',
    },
    {
        'name': 'max to fold',
        'before': "max(xs)",
        'after': "fold(max_op, -∞, xs)",
        'axiom': 'P2_max_to_fold',
    },
    {
        'name': 'min to sorted[0]',
        'before': "min(xs)",
        'after': "sorted(xs)[0]",
        'axiom': 'P2_min_to_sorted_index',
    },
    {
        'name': 'len to fold(count)',
        'before': "len(xs)",
        'after': "fold(count, 0, xs)",
        'axiom': 'P2_len_to_fold',
    },
    {
        'name': 'any to fold(or)',
        'before': "any(xs)",
        'after': "fold(or, False, xs)",
        'axiom': 'P2_any_to_fold',
    },
    {
        'name': 'all to not any(not ...)',
        'before': "all(xs)",
        'after': "not any(not x for x in xs)",
        'axiom': 'P2_all_to_not_any_not',
    },
    {
        'name': 'enumerate to zip+range',
        'before': "enumerate(xs)",
        'after': "zip(range(len(xs)), xs)",
        'axiom': 'P2_enumerate_to_zip_range',
    },
    {
        'name': 'reversed to slice',
        'before': "reversed(xs)",
        'after': "xs[::-1]",
        'axiom': 'P2_reversed_to_slice',
    },
]


# ═══════════════════════════════════════════════════════════
# Helper: extract params for fiber-awareness
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
    """Apply P2 built-in equivalences to *term*.

    Returns list of (rewritten_term, axiom_label) pairs.
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── sum(xs) → OFold('add', OLit(0), xs) ──
    if isinstance(term, OOp) and term.name == 'sum' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OFold('add', OLit(0), xs),
            'P2_sum_to_fold',
        ))

    # ── OFold('add', OLit(0), xs) → sum(xs) ──
    if isinstance(term, OFold) and term.op_name == 'add':
        if isinstance(term.init, OLit) and term.init.value == 0:
            results.append((
                OOp('sum', (term.collection,)),
                'P2_fold_to_sum',
            ))

    # ── max(xs) → OFold('max_op', ..., xs) ──
    if isinstance(term, OOp) and term.name == 'max' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OFold('max_op', OOp('neg_inf', ()), xs),
            'P2_max_to_fold',
        ))

    # ── OFold('max_op', ..., xs) → max(xs) ──
    if isinstance(term, OFold) and term.op_name == 'max_op':
        results.append((
            OOp('max', (term.collection,)),
            'P2_fold_to_max',
        ))

    # ── min(xs) → sorted(xs)[0] ──
    if isinstance(term, OOp) and term.name == 'min' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OOp('getitem', (OOp('sorted', (xs,)), OLit(0))),
            'P2_min_to_sorted_index',
        ))
        # Also: min → fold
        results.append((
            OFold('min_op', OOp('pos_inf', ()), xs),
            'P2_min_to_fold',
        ))

    # ── sorted(xs)[0] → min(xs) ──
    if isinstance(term, OOp) and term.name == 'getitem' and len(term.args) == 2:
        collection, index = term.args
        if (isinstance(collection, OOp) and collection.name == 'sorted'
                and len(collection.args) == 1
                and isinstance(index, OLit) and index.value == 0):
            results.append((
                OOp('min', (collection.args[0],)),
                'P2_sorted_index_to_min',
            ))

    # ── OFold('min_op', ..., xs) → min(xs) ──
    if isinstance(term, OFold) and term.op_name == 'min_op':
        results.append((
            OOp('min', (term.collection,)),
            'P2_fold_to_min',
        ))

    # ── len(xs) → OFold('count', OLit(0), xs) ──
    if isinstance(term, OOp) and term.name == 'len' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OFold('count', OLit(0), xs),
            'P2_len_to_fold',
        ))

    # ── OFold('count', OLit(0), xs) → len(xs) ──
    if isinstance(term, OFold) and term.op_name == 'count':
        if isinstance(term.init, OLit) and term.init.value == 0:
            results.append((
                OOp('len', (term.collection,)),
                'P2_fold_to_len',
            ))

    # ── any(xs) → OFold('or', OLit(False), xs) ──
    if isinstance(term, OOp) and term.name == 'any' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OFold('or', OLit(False), xs),
            'P2_any_to_fold',
        ))

    # ── OFold('or', OLit(False), xs) → any(xs) ──
    if isinstance(term, OFold) and term.op_name == 'or':
        if isinstance(term.init, OLit) and term.init.value is False:
            results.append((
                OOp('any', (term.collection,)),
                'P2_fold_to_any',
            ))

    # ── all(xs) → not any(not x for x in xs) (De Morgan) ──
    if isinstance(term, OOp) and term.name == 'all' and len(term.args) == 1:
        xs = term.args[0]
        negated_map = OMap(
            transform=OLam(('x',), OOp('u_not', (OVar('x'),))),
            collection=xs,
        )
        results.append((
            OOp('u_not', (OOp('any', (negated_map,)),)),
            'P2_all_to_not_any_not',
        ))
        # Also: all → fold(and, True, xs)
        results.append((
            OFold('and', OLit(True), xs),
            'P2_all_to_fold',
        ))

    # ── not any(not x for x in xs) → all(xs) ──
    if isinstance(term, OOp) and term.name == 'u_not' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'any' and len(inner.args) == 1:
            any_arg = inner.args[0]
            if isinstance(any_arg, OMap) and isinstance(any_arg.transform, OLam):
                lam = any_arg.transform
                if (isinstance(lam.body, OOp) and lam.body.name == 'u_not'
                        and len(lam.body.args) == 1):
                    results.append((
                        OOp('all', (any_arg.collection,)),
                        'P2_not_any_not_to_all',
                    ))

    # ── OFold('and', OLit(True), xs) → all(xs) ──
    if isinstance(term, OFold) and term.op_name == 'and':
        if isinstance(term.init, OLit) and term.init.value is True:
            results.append((
                OOp('all', (term.collection,)),
                'P2_fold_to_all',
            ))

    # ── zip(xs, ys) → index-based OMap ──
    if isinstance(term, OOp) and term.name == 'zip' and len(term.args) == 2:
        xs, ys = term.args
        idx_var = OVar('_i')
        pair = OOp('tuple', (
            OOp('getitem', (xs, idx_var)),
            OOp('getitem', (ys, idx_var)),
        ))
        index_map = OMap(
            transform=OLam(('_i',), pair),
            collection=OOp('range', (OOp('min', (
                OOp('len', (xs,)),
                OOp('len', (ys,)),
            )),)),
        )
        results.append((index_map, 'P2_zip_to_index_map'))

    # ── enumerate(xs) → zip(range(len(xs)), xs) ──
    if isinstance(term, OOp) and term.name == 'enumerate' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OOp('zip', (OOp('range', (OOp('len', (xs,)),)), xs)),
            'P2_enumerate_to_zip_range',
        ))

    # ── zip(range(len(xs)), xs) → enumerate(xs) ──
    if isinstance(term, OOp) and term.name == 'zip' and len(term.args) == 2:
        lhs, rhs = term.args
        if isinstance(lhs, OOp) and lhs.name == 'range' and len(lhs.args) == 1:
            range_arg = lhs.args[0]
            if isinstance(range_arg, OOp) and range_arg.name == 'len' and len(range_arg.args) == 1:
                if _terms_equal(range_arg.args[0], rhs):
                    results.append((
                        OOp('enumerate', (rhs,)),
                        'P2_zip_range_to_enumerate',
                    ))

    # ── reversed(xs) → xs[::-1] ──
    if isinstance(term, OOp) and term.name == 'reversed' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OOp('slice_step', (xs, OLit(None), OLit(None), OLit(-1))),
            'P2_reversed_to_slice',
        ))

    # ── xs[::-1] → reversed(xs) ──
    if isinstance(term, OOp) and term.name == 'slice_step' and len(term.args) == 4:
        xs, start, stop, step = term.args
        if (_is_none_lit(start) and _is_none_lit(stop)
                and isinstance(step, OLit) and step.value == -1):
            results.append((
                OOp('reversed', (xs,)),
                'P2_slice_to_reversed',
            ))

    # ── sorted(xs)[-1] → max(xs) ──
    if isinstance(term, OOp) and term.name == 'getitem' and len(term.args) == 2:
        collection, index = term.args
        if (isinstance(collection, OOp) and collection.name == 'sorted'
                and len(collection.args) == 1
                and isinstance(index, OLit) and index.value == -1):
            results.append((
                OOp('max', (collection.args[0],)),
                'P2_sorted_last_to_max',
            ))

    return results


def _is_none_lit(term: OTerm) -> bool:
    """Check if term is OLit(None)."""
    return isinstance(term, OLit) and term.value is None


def _terms_equal(a: OTerm, b: OTerm) -> bool:
    """Structural equality check for OTerms via canonical form."""
    return a.canon() == b.canon()


# ═══════════════════════════════════════════════════════════
# Inverse axiom
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply P2 in reverse: fold-based → built-in forms.

    Inverse rewrites are already embedded in apply() as bidirectional
    rules; this function filters for only the reverse direction.
    """
    results = apply(term, ctx)
    inverse_labels = {
        'P2_fold_to_sum',
        'P2_fold_to_max',
        'P2_fold_to_min',
        'P2_fold_to_len',
        'P2_fold_to_any',
        'P2_fold_to_all',
        'P2_not_any_not_to_all',
        'P2_sorted_index_to_min',
        'P2_sorted_last_to_max',
        'P2_zip_range_to_enumerate',
        'P2_slice_to_reversed',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

_BUILTIN_NAMES = frozenset({
    'sum', 'max', 'min', 'len', 'any', 'all',
    'zip', 'enumerate', 'reversed',
})

_FOLD_OPS = frozenset({
    'add', 'max_op', 'min_op', 'count', 'or', 'and',
})


def recognizes(term: OTerm) -> bool:
    """Return True if P2 is potentially applicable to *term*."""
    if isinstance(term, OOp):
        if term.name in _BUILTIN_NAMES:
            return True
        if term.name == 'u_not' and len(term.args) == 1:
            inner = term.args[0]
            if isinstance(inner, OOp) and inner.name == 'any':
                return True
        if term.name == 'getitem' and len(term.args) == 2:
            coll = term.args[0]
            if isinstance(coll, OOp) and coll.name == 'sorted':
                return True
        if term.name == 'slice_step' and len(term.args) == 4:
            return True
    if isinstance(term, OFold):
        if term.op_name in _FOLD_OPS:
            return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score how relevant P2 is for bridging *source* → *target*.

    Returns a float in [0, 1].
    """
    sc = source.canon()
    tc = target.canon()

    builtin_kws = ('sum(', 'max(', 'min(', 'len(', 'any(', 'all(',
                   'zip(', 'enumerate(', 'reversed(')
    fold_kws = ('fold[add]', 'fold[max_op]', 'fold[min_op]',
                'fold[count]', 'fold[or]', 'fold[and]')

    has_builtin_s = any(kw in sc for kw in builtin_kws)
    has_builtin_t = any(kw in tc for kw in builtin_kws)
    has_fold_s = any(kw in sc for kw in fold_kws)
    has_fold_t = any(kw in tc for kw in fold_kws)

    # One side built-in, other side fold → high relevance
    if has_builtin_s and has_fold_t:
        return 0.95
    if has_builtin_t and has_fold_s:
        return 0.95

    # Different built-in representations
    if has_builtin_s != has_builtin_t:
        return 0.85

    # Both have folds but different ops
    if has_fold_s and has_fold_t:
        return 0.75

    # reversed / slice patterns
    if 'reversed(' in sc or 'reversed(' in tc:
        return 0.70
    if 'slice_step(' in sc or 'slice_step(' in tc:
        return 0.65

    # enumerate / zip patterns
    if 'enumerate(' in sc or 'enumerate(' in tc:
        return 0.70

    # Generic signal
    if has_builtin_s or has_builtin_t or has_fold_s or has_fold_t:
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
    xs = OVar('xs')

    # ── sum(xs) → fold(add, 0, xs) ──
    print("P2: sum → fold ...")
    sum_term = OOp('sum', (xs,))
    r = apply(sum_term, ctx)
    _assert(any(lbl == 'P2_sum_to_fold' for _, lbl in r), "sum(xs) rewrites to fold")
    fold_result = [t for t, lbl in r if lbl == 'P2_sum_to_fold'][0]
    _assert(isinstance(fold_result, OFold), "result is OFold")
    _assert(fold_result.op_name == 'add', "fold op is add")

    # ── fold(add, 0, xs) → sum(xs) ──
    print("P2: fold(add) → sum ...")
    fold_add = OFold('add', OLit(0), xs)
    r2 = apply(fold_add, ctx)
    _assert(any(lbl == 'P2_fold_to_sum' for _, lbl in r2), "fold(add) → sum")

    # ── Roundtrip sum ──
    print("P2: sum roundtrip ...")
    rt = apply(fold_result, ctx)
    _assert(any(lbl == 'P2_fold_to_sum' for _, lbl in rt), "sum roundtrip works")

    # ── max(xs) → fold(max_op, ...) ──
    print("P2: max → fold ...")
    max_term = OOp('max', (xs,))
    r3 = apply(max_term, ctx)
    _assert(any(lbl == 'P2_max_to_fold' for _, lbl in r3), "max(xs) rewrites")

    # ── fold(max_op) → max(xs) ──
    print("P2: fold(max_op) → max ...")
    fold_max = OFold('max_op', OOp('neg_inf', ()), xs)
    r4 = apply(fold_max, ctx)
    _assert(any(lbl == 'P2_fold_to_max' for _, lbl in r4), "fold(max_op) → max")

    # ── min(xs) → sorted(xs)[0] ──
    print("P2: min → sorted[0] ...")
    min_term = OOp('min', (xs,))
    r5 = apply(min_term, ctx)
    _assert(any(lbl == 'P2_min_to_sorted_index' for _, lbl in r5), "min → sorted[0]")
    _assert(any(lbl == 'P2_min_to_fold' for _, lbl in r5), "min → fold")

    # ── sorted(xs)[0] → min(xs) ──
    print("P2: sorted[0] → min ...")
    sorted_idx = OOp('getitem', (OOp('sorted', (xs,)), OLit(0)))
    r6 = apply(sorted_idx, ctx)
    _assert(any(lbl == 'P2_sorted_index_to_min' for _, lbl in r6), "sorted[0] → min")

    # ── sorted(xs)[-1] → max(xs) ──
    print("P2: sorted[-1] → max ...")
    sorted_last = OOp('getitem', (OOp('sorted', (xs,)), OLit(-1)))
    r6b = apply(sorted_last, ctx)
    _assert(any(lbl == 'P2_sorted_last_to_max' for _, lbl in r6b), "sorted[-1] → max")

    # ── len(xs) → fold(count, 0, xs) ──
    print("P2: len → fold ...")
    len_term = OOp('len', (xs,))
    r7 = apply(len_term, ctx)
    _assert(any(lbl == 'P2_len_to_fold' for _, lbl in r7), "len → fold")

    # ── fold(count, 0, xs) → len(xs) ──
    print("P2: fold(count) → len ...")
    fold_count = OFold('count', OLit(0), xs)
    r8 = apply(fold_count, ctx)
    _assert(any(lbl == 'P2_fold_to_len' for _, lbl in r8), "fold(count) → len")

    # ── any(xs) → fold(or, False, xs) ──
    print("P2: any → fold ...")
    any_term = OOp('any', (xs,))
    r9 = apply(any_term, ctx)
    _assert(any(lbl == 'P2_any_to_fold' for _, lbl in r9), "any → fold")

    # ── fold(or, False, xs) → any(xs) ──
    print("P2: fold(or) → any ...")
    fold_or = OFold('or', OLit(False), xs)
    r10 = apply(fold_or, ctx)
    _assert(any(lbl == 'P2_fold_to_any' for _, lbl in r10), "fold(or) → any")

    # ── all(xs) → not any(not x for x in xs) ──
    print("P2: all → not any(not ...) ...")
    all_term = OOp('all', (xs,))
    r11 = apply(all_term, ctx)
    _assert(any(lbl == 'P2_all_to_not_any_not' for _, lbl in r11), "all → not any not")
    _assert(any(lbl == 'P2_all_to_fold' for _, lbl in r11), "all → fold(and)")

    # ── not any(not x for x in xs) → all(xs) ──
    print("P2: not any(not ...) → all ...")
    neg_map = OMap(
        transform=OLam(('x',), OOp('u_not', (OVar('x'),))),
        collection=xs,
    )
    not_any_not = OOp('u_not', (OOp('any', (neg_map,)),))
    r12 = apply(not_any_not, ctx)
    _assert(any(lbl == 'P2_not_any_not_to_all' for _, lbl in r12),
            "not any(not) → all")

    # ── fold(and, True, xs) → all(xs) ──
    print("P2: fold(and) → all ...")
    fold_and = OFold('and', OLit(True), xs)
    r13 = apply(fold_and, ctx)
    _assert(any(lbl == 'P2_fold_to_all' for _, lbl in r13), "fold(and) → all")

    # ── zip(xs, ys) → index-based map ──
    print("P2: zip → index map ...")
    ys = OVar('ys')
    zip_term = OOp('zip', (xs, ys))
    r14 = apply(zip_term, ctx)
    _assert(any(lbl == 'P2_zip_to_index_map' for _, lbl in r14), "zip → index map")

    # ── enumerate(xs) → zip(range(len(xs)), xs) ──
    print("P2: enumerate → zip+range ...")
    enum_term = OOp('enumerate', (xs,))
    r15 = apply(enum_term, ctx)
    _assert(any(lbl == 'P2_enumerate_to_zip_range' for _, lbl in r15),
            "enumerate → zip+range")

    # ── zip(range(len(xs)), xs) → enumerate(xs) ──
    print("P2: zip+range → enumerate ...")
    zip_range = OOp('zip', (OOp('range', (OOp('len', (xs,)),)), xs))
    r16 = apply(zip_range, ctx)
    _assert(any(lbl == 'P2_zip_range_to_enumerate' for _, lbl in r16),
            "zip+range → enumerate")

    # ── reversed(xs) → xs[::-1] ──
    print("P2: reversed → slice ...")
    rev_term = OOp('reversed', (xs,))
    r17 = apply(rev_term, ctx)
    _assert(any(lbl == 'P2_reversed_to_slice' for _, lbl in r17), "reversed → slice")

    # ── xs[::-1] → reversed(xs) ──
    print("P2: slice → reversed ...")
    slice_term = OOp('slice_step', (xs, OLit(None), OLit(None), OLit(-1)))
    r18 = apply(slice_term, ctx)
    _assert(any(lbl == 'P2_slice_to_reversed' for _, lbl in r18), "slice → reversed")

    # ── recognizes() ──
    print("P2: recognizes ...")
    _assert(recognizes(sum_term), "recognizes sum")
    _assert(recognizes(max_term), "recognizes max")
    _assert(recognizes(min_term), "recognizes min")
    _assert(recognizes(len_term), "recognizes len")
    _assert(recognizes(any_term), "recognizes any")
    _assert(recognizes(all_term), "recognizes all")
    _assert(recognizes(zip_term), "recognizes zip")
    _assert(recognizes(enum_term), "recognizes enumerate")
    _assert(recognizes(rev_term), "recognizes reversed")
    _assert(recognizes(fold_add), "recognizes fold(add)")
    _assert(recognizes(fold_or), "recognizes fold(or)")
    _assert(recognizes(not_any_not), "recognizes not any(not)")
    _assert(recognizes(sorted_idx), "recognizes sorted[0]")
    _assert(recognizes(slice_term), "recognizes slice_step")
    _assert(not recognizes(OOp('Counter', (xs,))), "does not recognise Counter")
    _assert(not recognizes(OLit(42)), "does not recognise literal")

    # ── relevance_score ──
    print("P2: relevance_score ...")
    score = relevance_score(sum_term, fold_add)
    _assert(score > 0.8, f"sum↔fold score={score:.2f} > 0.8")
    low = relevance_score(OOp('Counter', (xs,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("P2: apply_inverse ...")
    inv = apply_inverse(fold_add, ctx)
    _assert(len(inv) >= 1, "inverse of fold(add) produces sum")
    inv2 = apply_inverse(sorted_idx, ctx)
    _assert(len(inv2) >= 1, "inverse of sorted[0] produces min")
    inv3 = apply_inverse(not_any_not, ctx)
    _assert(len(inv3) >= 1, "inverse of not any(not) produces all")
    inv4 = apply_inverse(slice_term, ctx)
    _assert(len(inv4) >= 1, "inverse of slice produces reversed")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  P2 builtins: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
