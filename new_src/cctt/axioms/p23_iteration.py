"""P23 Axiom: Iteration Protocol Equivalences.

Establishes equivalences between Python iteration patterns:
enumerate, next/filter, for-loop search, iterator protocol,
zip_longest, iter(callable, sentinel).

Mathematical basis: Iteration is a fold over a sequence with
early termination (short-circuit).  The iterator protocol
defines a sequence as a morphism  next : State → Maybe(T).

Key rewrites:
  • for i, x in enumerate(xs): ...  ↔  i=0; for x in xs: ...; i+=1
  • for x in xs: if p(x): return x  ↔  next(filter(p, xs), None)
  • while True: x=next(it); if x is None: break  ↔  for x in it:
  • iter(callable, sentinel) patterns
  • zip_longest ↔ manual padding

(§P23, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P23_iteration"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["D1_fold_unfold", "D4_comp_fusion", "D5_fold_universal",
                 "P14_slicing"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P23 Iteration Protocol Equivalence).

1. for i, x in enumerate(xs): body(i, x)
   ≡ i = 0; for x in xs: body(i, x); i += 1
   enumerate(xs) produces (index, element) pairs starting at 0.
   A manual counter achieves the same.

2. for x in xs: if p(x): return x; return None
   ≡ next(filter(p, xs), None)
   ≡ next((x for x in xs if p(x)), None)
   Linear search for the first element satisfying predicate p.
   filter(p, xs) lazily yields matching elements; next() gets first.

3. for x in xs: if p(x): break
   ≡ next(filter(p, xs), None)
   Early exit from a loop is equivalent to taking the first
   element from a filtered iterator.

4. while True: x = next(it, None); if x is None: break; body(x)
   ≡ for x in it: body(x)
   Manual next() polling is equivalent to the for-loop protocol.

5. iter(callable, sentinel)
   Creates an iterator that calls callable() until sentinel is
   returned.  Equivalent to a while loop with break on sentinel.

6. zip_longest(xs, ys, fillvalue=v)
   ≡ manual padding to max length then zip
"""

EXAMPLES = [
    ("fold_enumerate($f, $xs)", "fold_counter($f, $xs)", "P23_enumerate"),
    ("fold_search($p, $xs, None)", "next(filter($p, $xs), None)", "P23_search"),
    ("while_next($it, $body)", "for_iter($x, $it, $body)", "P23_while_to_for"),
]

# Iteration operation names
_ITER_OPS = frozenset({
    'enumerate', 'fold_enumerate', 'fold_counter',
    'fold_search', 'find_first',
    'while_next', 'for_iter',
    'iter_callable', 'zip_longest',
})


def _is_search_fold(term: OTerm) -> Optional[Tuple[OTerm, OTerm, OTerm]]:
    """Detect fold_search(pred, collection, default)."""
    if isinstance(term, OOp) and term.name == 'fold_search' and len(term.args) == 3:
        return (term.args[0], term.args[1], term.args[2])
    return None


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P23: Iteration protocol rewrites.

    Handles:
      1. fold_enumerate(f, xs) → fold_counter(f, xs)
      2. fold_counter(f, xs) → fold_enumerate(f, xs)
      3. fold_search(p, xs, default) → next(filter(p, xs), default)
      4. next(filter(p, xs), default) → fold_search(p, xs, default)
      5. while_next(it, body) → for_iter(x, it, body)
      6. for_iter(x, it, body) → while_next(it, body)
      7. iter_callable(fn, sentinel) → while_sentinel(fn, sentinel)
      8. zip_longest(xs, ys, fill) → pad_zip(xs, ys, fill)
      9. enumerate(xs) ↔ zip(range(len(xs)), xs)
     10. find_first(p, xs) → next(filter(p, xs), None)
    """
    results: List[Tuple[OTerm, str]] = []

    # ── 1-2. fold_enumerate ↔ fold_counter ──
    if isinstance(term, OOp) and term.name == 'fold_enumerate' and len(term.args) >= 2:
        results.append((
            OOp('fold_counter', term.args),
            'P23_enumerate_to_counter',
        ))

    if isinstance(term, OOp) and term.name == 'fold_counter' and len(term.args) >= 2:
        results.append((
            OOp('fold_enumerate', term.args),
            'P23_counter_to_enumerate',
        ))

    # ── 3. fold_search(p, xs, default) → next(filter(p, xs), default) ──
    search = _is_search_fold(term)
    if search is not None:
        pred, xs, default = search
        results.append((
            OOp('next', (OOp('filter', (pred, xs)), default)),
            'P23_search_to_next_filter',
        ))

    # ── 4. next(filter(p, xs), default) → fold_search(p, xs, default) ──
    if isinstance(term, OOp) and term.name == 'next' and len(term.args) == 2:
        source, default = term.args
        if isinstance(source, OOp) and source.name == 'filter' and len(source.args) == 2:
            pred, xs = source.args
            results.append((
                OOp('fold_search', (pred, xs, default)),
                'P23_next_filter_to_search',
            ))
        # Also handle generator expression: next(genexpr, default)
        if isinstance(source, OMap) and source.filter_pred is not None:
            results.append((
                OOp('fold_search', (source.filter_pred, source.collection, default)),
                'P23_next_genexpr_to_search',
            ))

    # ── 5-6. while_next ↔ for_iter ──
    if isinstance(term, OOp) and term.name == 'while_next' and len(term.args) >= 2:
        it, body = term.args[0], term.args[1]
        results.append((
            OOp('for_iter', (OVar('_x'), it, body)),
            'P23_while_next_to_for',
        ))

    if isinstance(term, OOp) and term.name == 'for_iter' and len(term.args) == 3:
        x, it, body = term.args
        results.append((
            OOp('while_next', (it, body)),
            'P23_for_to_while_next',
        ))

    # ── 7. iter_callable(fn, sentinel) → while_sentinel ──
    if isinstance(term, OOp) and term.name == 'iter_callable' and len(term.args) == 2:
        fn, sentinel = term.args
        results.append((
            OOp('while_sentinel', (fn, sentinel)),
            'P23_iter_callable_to_while',
        ))

    if isinstance(term, OOp) and term.name == 'while_sentinel' and len(term.args) == 2:
        fn, sentinel = term.args
        results.append((
            OOp('iter_callable', (fn, sentinel)),
            'P23_while_to_iter_callable',
        ))

    # ── 8. zip_longest ↔ pad_zip ──
    if isinstance(term, OOp) and term.name == 'zip_longest' and len(term.args) >= 2:
        results.append((
            OOp('pad_zip', term.args),
            'P23_zip_longest_to_pad_zip',
        ))

    if isinstance(term, OOp) and term.name == 'pad_zip' and len(term.args) >= 2:
        results.append((
            OOp('zip_longest', term.args),
            'P23_pad_zip_to_zip_longest',
        ))

    # ── 9. enumerate(xs) ↔ zip(range(len(xs)), xs) ──
    if isinstance(term, OOp) and term.name == 'enumerate' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OOp('zip', (OOp('range', (OOp('len', (xs,)),)), xs)),
            'P23_enumerate_to_zip_range',
        ))

    if isinstance(term, OOp) and term.name == 'zip' and len(term.args) == 2:
        first, second = term.args
        if (isinstance(first, OOp) and first.name == 'range'
                and len(first.args) == 1
                and isinstance(first.args[0], OOp)
                and first.args[0].name == 'len'
                and len(first.args[0].args) == 1
                and first.args[0].args[0].canon() == second.canon()):
            results.append((
                OOp('enumerate', (second,)),
                'P23_zip_range_to_enumerate',
            ))

    # ── 10. find_first(p, xs) → next(filter(p, xs), None) ──
    if isinstance(term, OOp) and term.name == 'find_first' and len(term.args) == 2:
        pred, xs = term.args
        results.append((
            OOp('next', (OOp('filter', (pred, xs)), OLit(None))),
            'P23_find_first_to_next_filter',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Recognizer & scoring
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    if isinstance(term, OOp):
        if term.name in _ITER_OPS:
            return True
        if term.name == 'next' and len(term.args) == 2:
            source = term.args[0]
            if isinstance(source, OOp) and source.name == 'filter':
                return True
            if isinstance(source, OMap) and source.filter_pred is not None:
                return True
        if term.name == 'zip' and len(term.args) == 2:
            first = term.args[0]
            if isinstance(first, OOp) and first.name == 'range':
                return True
        if term.name in ('while_sentinel', 'pad_zip', 'find_first',
                         'fold_search', 'fold_counter'):
            return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    sc, tc = source.canon(), target.canon()
    for kw in ('enumerate', 'filter', 'next', 'iter', 'zip_longest',
               'fold_search', 'while_next', 'for_iter', 'find_first'):
        if kw in sc and kw in tc:
            return 0.8
    if 'enumerate' in sc and 'zip' in tc:
        return 0.7
    if 'fold_search' in sc and 'next' in tc:
        return 0.75
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse: introduce verbose iteration forms."""
    results: List[Tuple[OTerm, str]] = []

    # next(filter(p, xs), default) → fold_search
    if isinstance(term, OOp) and term.name == 'next' and len(term.args) == 2:
        source, default = term.args
        if isinstance(source, OOp) and source.name == 'filter' and len(source.args) == 2:
            pred, xs = source.args
            results.append((
                OOp('fold_search', (pred, xs, default)),
                'P23_inv_next_filter_to_search',
            ))

    # enumerate(xs) → fold_enumerate(body, xs)
    if isinstance(term, OOp) and term.name == 'enumerate' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OOp('zip', (OOp('range', (OOp('len', (xs,)),)), xs)),
            'P23_inv_enumerate_to_zip',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════

if __name__ == '__main__':
    _pass = 0
    _fail = 0

    def _assert(cond: bool, msg: str) -> None:
        global _pass, _fail
        if cond:
            _pass += 1
        else:
            _fail += 1
            print(f"  FAIL: {msg}")

    # 1. fold_enumerate → fold_counter
    t1 = OOp('fold_enumerate', (OVar('f'), OVar('xs')))
    r1 = apply(t1)
    _assert(any(a == 'P23_enumerate_to_counter' for _, a in r1), "enumerate → counter")

    # 2. fold_counter → fold_enumerate
    t2 = OOp('fold_counter', (OVar('f'), OVar('xs')))
    r2 = apply(t2)
    _assert(any(a == 'P23_counter_to_enumerate' for _, a in r2), "counter → enumerate")

    # 3. fold_search → next(filter)
    t3 = OOp('fold_search', (OVar('p'), OVar('xs'), OLit(None)))
    r3 = apply(t3)
    _assert(any(a == 'P23_search_to_next_filter' for _, a in r3), "search → next(filter)")

    # 4. next(filter(p, xs), default) → fold_search
    t4 = OOp('next', (OOp('filter', (OVar('p'), OVar('xs'))), OLit(None)))
    r4 = apply(t4)
    _assert(any(a == 'P23_next_filter_to_search' for _, a in r4), "next(filter) → search")

    # 5. while_next → for_iter
    t5 = OOp('while_next', (OVar('it'), OVar('body')))
    r5 = apply(t5)
    _assert(any(a == 'P23_while_next_to_for' for _, a in r5), "while_next → for")

    # 6. for_iter → while_next
    t6 = OOp('for_iter', (OVar('x'), OVar('it'), OVar('body')))
    r6 = apply(t6)
    _assert(any(a == 'P23_for_to_while_next' for _, a in r6), "for → while_next")

    # 7. iter_callable → while_sentinel
    t7 = OOp('iter_callable', (OVar('fn'), OLit('')))
    r7 = apply(t7)
    _assert(any(a == 'P23_iter_callable_to_while' for _, a in r7), "iter_callable → while")

    # 8. while_sentinel → iter_callable
    t8 = OOp('while_sentinel', (OVar('fn'), OLit('')))
    r8 = apply(t8)
    _assert(any(a == 'P23_while_to_iter_callable' for _, a in r8), "while → iter_callable")

    # 9. zip_longest → pad_zip
    t9 = OOp('zip_longest', (OVar('xs'), OVar('ys'), OLit(0)))
    r9 = apply(t9)
    _assert(any(a == 'P23_zip_longest_to_pad_zip' for _, a in r9), "zip_longest → pad_zip")

    # 10. pad_zip → zip_longest
    t10 = OOp('pad_zip', (OVar('xs'), OVar('ys'), OLit(0)))
    r10 = apply(t10)
    _assert(any(a == 'P23_pad_zip_to_zip_longest' for _, a in r10), "pad_zip → zip_longest")

    # 11. enumerate → zip(range(len), xs)
    t11 = OOp('enumerate', (OVar('xs'),))
    r11 = apply(t11)
    _assert(any(a == 'P23_enumerate_to_zip_range' for _, a in r11), "enumerate → zip(range)")

    # 12. zip(range(len(xs)), xs) → enumerate
    t12 = OOp('zip', (OOp('range', (OOp('len', (OVar('xs'),)),)), OVar('xs')))
    r12 = apply(t12)
    _assert(any(a == 'P23_zip_range_to_enumerate' for _, a in r12), "zip(range) → enumerate")

    # 13. find_first → next(filter)
    t13 = OOp('find_first', (OVar('p'), OVar('xs')))
    r13 = apply(t13)
    _assert(any(a == 'P23_find_first_to_next_filter' for _, a in r13), "find_first → next")

    # 14. next(genexpr, default) → fold_search
    t14 = OOp('next', (OMap(OLam(('x',), OVar('x')), OVar('xs'),
                             OLam(('x',), OOp('gt', (OVar('x'), OLit(0))))),
                        OLit(None)))
    r14 = apply(t14)
    _assert(any(a == 'P23_next_genexpr_to_search' for _, a in r14), "next(genexpr) → search")

    # 15. recognizes
    _assert(recognizes(t3), "recognizes fold_search")
    _assert(recognizes(t4), "recognizes next(filter)")
    _assert(recognizes(t11), "recognizes enumerate")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # 16. relevance
    _assert(relevance_score(t3, t4) > 0.5, "search/next relevance")

    # 17. inverse
    r17 = apply_inverse(t4)
    _assert(any(a == 'P23_inv_next_filter_to_search' for _, a in r17), "inv next → search")

    print(f"P23 iteration: {_pass} passed, {_fail} failed")
