"""P5: Sorting Variations (Theorem P.5.1).

sorted(xs) ↔ list(xs); xs.sort(); return xs — and higher-level variants.

Mathematical foundation:
  Sorting is a morphism  s: List(X) → SortedList(X)  where SortedList(X)
  is the subobject of List(X) satisfying the total-order predicate.  All
  Python representations (sorted(), .sort(), Schwartzian transform,
  heapq.nsmallest/nlargest) compute the same underlying order morphism —
  they differ only in evaluation strategy and auxiliary data structures.

  The Schwartzian transform decorates, sorts, then undecorates.  This is
  a Beck–Chevalley reindexing along the key projection π₂.

  Stable-sort composition:
    sorted(sorted(xs, key=f), key=g)  ≡  sorted(xs, key=λx.(g(x), f(x)))
  follows from the lexicographic order being the product order in the
  slice category Over(TotalOrder).

Covers:
  • sorted(xs) ↔ in-place sort
  • sorted(xs, key=f) ↔ Schwartzian transform
  • sorted(xs, reverse=True) ↔ list(reversed(sorted(xs)))
  • heapq.nsmallest(k, xs) ↔ sorted(xs)[:k]
  • heapq.nlargest(k, xs) ↔ sorted(xs, reverse=True)[:k]
  • Stable sort composition (double-sort → composite key)
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

AXIOM_NAME = 'P5_sort_variants'
AXIOM_CATEGORY = 'python_idiom'

SOUNDNESS_PROOF = """
Theorem P.5.1 (Sorting Variation Equivalence):
  For any list xs: X* and total order ≤ on X,
    sorted(xs)  ≡  (lambda l: (l.sort(), l)[1])(list(xs))
  as morphisms List(X) → SortedList(X).

Proof sketch:
  1. sorted(xs) returns a new list with elements of xs in non-decreasing
     order.  list.sort() mutates in-place and returns None; wrapping
     recovers the sorted list.  Both compute the same permutation.
  2. Schwartzian transform:
       [x for _, x in sorted((f(x), x) for x in xs)]
     is equivalent to sorted(xs, key=f) because the primary sort key is
     f(x) and ties are broken by insertion order (stability).
  3. sorted(xs, reverse=True) ≡ list(reversed(sorted(xs))) because
     reversing a sorted sequence yields the reverse-sorted sequence.
  4. heapq.nsmallest(k, xs) ≡ sorted(xs)[:k] by the heap selection
     algorithm computing the same prefix of the sorted output.
  5. Stable sort composition: sorted(sorted(xs, key=f), key=g)
     ≡ sorted(xs, key=λx.(g(x), f(x))) by the lexicographic order on
     product types and stability preservation.  ∎
"""

COMPOSES_WITH = ['D19_sort', 'D13_histogram', 'D14_indexing']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'sorted to in-place sort',
        'before': "sorted(xs)",
        'after': "(lambda l: (l.sort(), l)[1])(list(xs))",
        'axiom': 'P5_sorted_to_inplace',
    },
    {
        'name': 'sorted_key to Schwartzian',
        'before': "sorted(xs, key=f)",
        'after': "[x for _, x in sorted((f(x), x) for x in xs)]",
        'axiom': 'P5_sorted_key_to_schwartzian',
    },
    {
        'name': 'sorted_rev to reversed(sorted)',
        'before': "sorted(xs, reverse=True)",
        'after': "list(reversed(sorted(xs)))",
        'axiom': 'P5_sorted_rev_to_reversed',
    },
    {
        'name': 'heapq.nsmallest to sorted slice',
        'before': "heapq.nsmallest(k, xs)",
        'after': "sorted(xs)[:k]",
        'axiom': 'P5_nsmallest_to_sorted_slice',
    },
    {
        'name': 'heapq.nlargest to sorted_rev slice',
        'before': "heapq.nlargest(k, xs)",
        'after': "sorted(xs, reverse=True)[:k]",
        'axiom': 'P5_nlargest_to_sorted_rev_slice',
    },
    {
        'name': 'Double sort to composite key',
        'before': "sorted(sorted(xs, key=f), key=g)",
        'after': "sorted(xs, key=lambda x: (g(x), f(x)))",
        'axiom': 'P5_double_sort_to_composite_key',
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
    """Apply P5 sorting-variation equivalences to *term*.

    Returns list of (rewritten_term, axiom_label) pairs.
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── sorted(xs) → in-place sort wrapper ──
    if isinstance(term, OOp) and term.name == 'sorted' and len(term.args) == 1:
        xs = term.args[0]
        inplace = OOp('inplace_sort_wrap', (xs,))
        results.append((inplace, 'P5_sorted_to_inplace'))

    # ── in-place sort wrapper → sorted(xs) ──
    if isinstance(term, OOp) and term.name == 'inplace_sort_wrap' and len(term.args) == 1:
        xs = term.args[0]
        results.append((OOp('sorted', (xs,)), 'P5_inplace_to_sorted'))

    # ── sorted(xs, key=f) → Schwartzian transform ──
    if isinstance(term, OOp) and term.name == 'sorted_key' and len(term.args) == 2:
        xs, f = term.args
        # Schwartzian: [x for _, x in sorted((f(x), x) for x in xs)]
        decorate = OMap(
            OLam(('x',), OSeq((OOp('apply', (f, OVar('x'))), OVar('x')))),
            xs,
        )
        undecorate = OMap(
            OLam(('p',), OOp('getitem', (OVar('p'), OLit(1)))),
            OOp('sorted', (decorate,)),
        )
        results.append((undecorate, 'P5_sorted_key_to_schwartzian'))

    # ── Schwartzian transform → sorted(xs, key=f) ──
    if isinstance(term, OMap) and isinstance(term.transform, OLam):
        lam = term.transform
        if (isinstance(lam.body, OOp) and lam.body.name == 'getitem'
                and len(lam.body.args) == 2
                and isinstance(lam.body.args[1], OLit)
                and lam.body.args[1].value == 1):
            inner = term.collection
            if isinstance(inner, OOp) and inner.name == 'sorted' and len(inner.args) == 1:
                decorated_map = inner.args[0]
                if isinstance(decorated_map, OMap) and isinstance(decorated_map.transform, OLam):
                    dec_body = decorated_map.transform.body
                    if isinstance(dec_body, OSeq) and len(dec_body.elements) == 2:
                        key_app = dec_body.elements[0]
                        if isinstance(key_app, OOp) and key_app.name == 'apply' and len(key_app.args) == 2:
                            f = key_app.args[0]
                            xs = decorated_map.collection
                            results.append((
                                OOp('sorted_key', (xs, f)),
                                'P5_schwartzian_to_sorted_key',
                            ))

    # ── sorted(xs, reverse=True) → list(reversed(sorted(xs))) ──
    if isinstance(term, OOp) and term.name == 'sorted_rev' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OOp('list', (OOp('reversed', (OOp('sorted', (xs,)),)),)),
            'P5_sorted_rev_to_reversed',
        ))

    # ── list(reversed(sorted(xs))) → sorted_rev(xs) ──
    if isinstance(term, OOp) and term.name == 'list' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'reversed' and len(inner.args) == 1:
            rev_inner = inner.args[0]
            if isinstance(rev_inner, OOp) and rev_inner.name == 'sorted' and len(rev_inner.args) == 1:
                xs = rev_inner.args[0]
                results.append((
                    OOp('sorted_rev', (xs,)),
                    'P5_reversed_sorted_to_sorted_rev',
                ))

    # ── heapq.nsmallest(k, xs) → sorted(xs)[:k] ──
    if isinstance(term, OOp) and term.name == 'heapq.nsmallest' and len(term.args) == 2:
        k, xs = term.args
        sliced = OOp('getitem', (
            OOp('sorted', (xs,)),
            OOp('slice', (OLit(None), k)),
        ))
        results.append((sliced, 'P5_nsmallest_to_sorted_slice'))

    # ── sorted(xs)[:k] → heapq.nsmallest(k, xs) ──
    if isinstance(term, OOp) and term.name == 'getitem' and len(term.args) == 2:
        body, sl = term.args
        if (isinstance(body, OOp) and body.name == 'sorted' and len(body.args) == 1
                and isinstance(sl, OOp) and sl.name == 'slice'
                and len(sl.args) == 2
                and isinstance(sl.args[0], OLit) and sl.args[0].value is None):
            xs = body.args[0]
            k = sl.args[1]
            results.append((
                OOp('heapq.nsmallest', (k, xs)),
                'P5_sorted_slice_to_nsmallest',
            ))

    # ── heapq.nlargest(k, xs) → sorted_rev(xs)[:k] ──
    if isinstance(term, OOp) and term.name == 'heapq.nlargest' and len(term.args) == 2:
        k, xs = term.args
        sliced = OOp('getitem', (
            OOp('sorted_rev', (xs,)),
            OOp('slice', (OLit(None), k)),
        ))
        results.append((sliced, 'P5_nlargest_to_sorted_rev_slice'))

    # ── sorted_rev(xs)[:k] → heapq.nlargest(k, xs) ──
    if isinstance(term, OOp) and term.name == 'getitem' and len(term.args) == 2:
        body, sl = term.args
        if (isinstance(body, OOp) and body.name == 'sorted_rev' and len(body.args) == 1
                and isinstance(sl, OOp) and sl.name == 'slice'
                and len(sl.args) == 2
                and isinstance(sl.args[0], OLit) and sl.args[0].value is None):
            xs = body.args[0]
            k = sl.args[1]
            results.append((
                OOp('heapq.nlargest', (k, xs)),
                'P5_sorted_rev_slice_to_nlargest',
            ))

    # ── Stable sort composition: sorted(sorted(xs, key=f), key=g) →
    #    sorted(xs, key=λx.(g(x), f(x))) ──
    if isinstance(term, OOp) and term.name == 'sorted_key' and len(term.args) == 2:
        inner, g = term.args
        if isinstance(inner, OOp) and inner.name == 'sorted_key' and len(inner.args) == 2:
            xs, f = inner.args
            composite_key = OLam(
                ('x',),
                OSeq((OOp('apply', (g, OVar('x'))), OOp('apply', (f, OVar('x'))))),
            )
            results.append((
                OOp('sorted_key', (xs, composite_key)),
                'P5_double_sort_to_composite_key',
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse axiom
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply P5 in reverse: expanded forms → canonical sorted() calls.

    Inverse rewrites are already embedded in apply() as bidirectional
    rules; this function filters for only the reverse direction.
    """
    results = apply(term, ctx)
    inverse_labels = {
        'P5_inplace_to_sorted',
        'P5_schwartzian_to_sorted_key',
        'P5_reversed_sorted_to_sorted_rev',
        'P5_sorted_slice_to_nsmallest',
        'P5_sorted_rev_slice_to_nlargest',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if P5 is potentially applicable to *term*."""
    if isinstance(term, OOp):
        if term.name in ('sorted', 'sorted_key', 'sorted_rev',
                         'inplace_sort_wrap',
                         'heapq.nsmallest', 'heapq.nlargest'):
            return True
        # list(reversed(sorted(...))) pattern
        if term.name == 'list' and len(term.args) == 1:
            inner = term.args[0]
            if isinstance(inner, OOp) and inner.name == 'reversed' and len(inner.args) == 1:
                ri = inner.args[0]
                if isinstance(ri, OOp) and ri.name == 'sorted':
                    return True
        # sorted(xs)[:k] pattern
        if term.name == 'getitem' and len(term.args) == 2:
            body = term.args[0]
            if isinstance(body, OOp) and body.name in ('sorted', 'sorted_rev'):
                return True
    # Schwartzian OMap pattern
    if isinstance(term, OMap) and isinstance(term.collection, OOp):
        if term.collection.name == 'sorted':
            return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score how relevant P5 is for bridging *source* → *target*.

    Returns a float in [0, 1].
    """
    sc = source.canon()
    tc = target.canon()

    sort_keywords = ('sorted', 'sort', 'heapq', 'nsmallest', 'nlargest')
    has_sort_s = any(kw in sc for kw in sort_keywords)
    has_sort_t = any(kw in tc for kw in sort_keywords)

    # Both sides involve sorting with different representations
    if has_sort_s and has_sort_t:
        # Different sorting idioms → high relevance
        if ('heapq' in sc) != ('heapq' in tc):
            return 0.95
        if ('sorted_key' in sc) != ('sorted_key' in tc):
            return 0.90
        if ('sorted_rev' in sc) != ('sorted_rev' in tc):
            return 0.90
        return 0.70

    # One side has sorting, the other doesn't
    if has_sort_s or has_sort_t:
        if 'reversed' in sc or 'reversed' in tc:
            return 0.80
        if 'getitem' in sc or 'getitem' in tc:
            return 0.60
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
    f = OVar('f')
    g = OVar('g')
    k = OLit(3)

    # ── sorted(xs) → inplace sort ──
    print("P5: sorted(xs) → inplace_sort_wrap ...")
    sorted_term = OOp('sorted', (xs,))
    r = apply(sorted_term, ctx)
    _assert(len(r) >= 1, "sorted(xs) should rewrite")
    _assert(r[0][1] == 'P5_sorted_to_inplace', "axiom label")
    _assert(isinstance(r[0][0], OOp) and r[0][0].name == 'inplace_sort_wrap',
            "result is inplace_sort_wrap")

    # ── inplace → sorted (inverse) ──
    print("P5: inplace_sort_wrap → sorted ...")
    inplace_term = OOp('inplace_sort_wrap', (xs,))
    r2 = apply(inplace_term, ctx)
    _assert(any(lbl == 'P5_inplace_to_sorted' for _, lbl in r2), "inplace→sorted")

    # ── sorted_key → Schwartzian ──
    print("P5: sorted_key → Schwartzian ...")
    sorted_key_term = OOp('sorted_key', (xs, f))
    r3 = apply(sorted_key_term, ctx)
    _assert(any(lbl == 'P5_sorted_key_to_schwartzian' for _, lbl in r3),
            "sorted_key→Schwartzian")

    # ── Schwartzian → sorted_key (roundtrip) ──
    print("P5: Schwartzian → sorted_key ...")
    schwartzian_results = [(t, l) for t, l in r3 if l == 'P5_sorted_key_to_schwartzian']
    if schwartzian_results:
        schwartz_term = schwartzian_results[0][0]
        r3b = apply(schwartz_term, ctx)
        _assert(any(lbl == 'P5_schwartzian_to_sorted_key' for _, lbl in r3b),
                "Schwartzian→sorted_key roundtrip")

    # ── sorted_rev → list(reversed(sorted)) ──
    print("P5: sorted_rev → reversed(sorted) ...")
    sorted_rev_term = OOp('sorted_rev', (xs,))
    r4 = apply(sorted_rev_term, ctx)
    _assert(any(lbl == 'P5_sorted_rev_to_reversed' for _, lbl in r4),
            "sorted_rev→reversed")

    # ── list(reversed(sorted(xs))) → sorted_rev ──
    print("P5: reversed(sorted) → sorted_rev ...")
    list_rev_sorted = OOp('list', (OOp('reversed', (OOp('sorted', (xs,)),)),))
    r5 = apply(list_rev_sorted, ctx)
    _assert(any(lbl == 'P5_reversed_sorted_to_sorted_rev' for _, lbl in r5),
            "reversed(sorted)→sorted_rev")

    # ── heapq.nsmallest → sorted slice ──
    print("P5: heapq.nsmallest → sorted[:k] ...")
    nsmallest = OOp('heapq.nsmallest', (k, xs))
    r6 = apply(nsmallest, ctx)
    _assert(any(lbl == 'P5_nsmallest_to_sorted_slice' for _, lbl in r6),
            "nsmallest→sorted slice")

    # ── sorted[:k] → heapq.nsmallest ──
    print("P5: sorted[:k] → heapq.nsmallest ...")
    sorted_slice = OOp('getitem', (
        OOp('sorted', (xs,)),
        OOp('slice', (OLit(None), k)),
    ))
    r7 = apply(sorted_slice, ctx)
    _assert(any(lbl == 'P5_sorted_slice_to_nsmallest' for _, lbl in r7),
            "sorted slice→nsmallest")

    # ── heapq.nlargest → sorted_rev slice ──
    print("P5: heapq.nlargest → sorted_rev[:k] ...")
    nlargest = OOp('heapq.nlargest', (k, xs))
    r8 = apply(nlargest, ctx)
    _assert(any(lbl == 'P5_nlargest_to_sorted_rev_slice' for _, lbl in r8),
            "nlargest→sorted_rev slice")

    # ── sorted_rev[:k] → heapq.nlargest ──
    print("P5: sorted_rev[:k] → heapq.nlargest ...")
    sorted_rev_slice = OOp('getitem', (
        OOp('sorted_rev', (xs,)),
        OOp('slice', (OLit(None), k)),
    ))
    r9 = apply(sorted_rev_slice, ctx)
    _assert(any(lbl == 'P5_sorted_rev_slice_to_nlargest' for _, lbl in r9),
            "sorted_rev slice→nlargest")

    # ── Double sort → composite key ──
    print("P5: double sort → composite key ...")
    double_sort = OOp('sorted_key', (OOp('sorted_key', (xs, f)), g))
    r10 = apply(double_sort, ctx)
    _assert(any(lbl == 'P5_double_sort_to_composite_key' for _, lbl in r10),
            "double sort→composite key")

    # ── recognizes() ──
    print("P5: recognizes ...")
    _assert(recognizes(sorted_term), "recognizes sorted")
    _assert(recognizes(sorted_key_term), "recognizes sorted_key")
    _assert(recognizes(sorted_rev_term), "recognizes sorted_rev")
    _assert(recognizes(nsmallest), "recognizes heapq.nsmallest")
    _assert(recognizes(nlargest), "recognizes heapq.nlargest")
    _assert(recognizes(list_rev_sorted), "recognizes list(reversed(sorted))")
    _assert(recognizes(sorted_slice), "recognizes sorted[:k]")
    _assert(not recognizes(OOp('Counter', (xs,))), "does not recognise Counter")

    # ── relevance_score ──
    print("P5: relevance_score ...")
    score = relevance_score(sorted_term, nsmallest)
    _assert(score > 0.8, f"sorted↔nsmallest score={score:.2f} > 0.8")
    low = relevance_score(OOp('Counter', (xs,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("P5: apply_inverse ...")
    inv = apply_inverse(inplace_term, ctx)
    _assert(len(inv) >= 1, "inverse of inplace produces sorted")
    _assert(inv[0][1] == 'P5_inplace_to_sorted', "inverse label")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  P5 sort_variants: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
