"""P35 Axiom: Map / Filter / Reduce Equivalences.

Establishes equivalences between functional higher-order operations
and their imperative or comprehension-based counterparts: map vs
list comprehensions, filter vs guarded comprehensions, reduce vs
loop accumulators, and fused map-filter chains.

Mathematical basis: Map, filter, and reduce are the canonical
morphisms of the List functor in the category of types:

  map(f) : List(A) → List(B)           — functorial lift of f : A → B
  filter(p) : List(A) → List(A)        — subfunctor inclusion
  reduce(⊕, e) : List(A) → B          — catamorphism (fold)

The equivalences:
  map(f, xs) ≡ [f(x) for x in xs]     — by definition of the list functor
  filter(p, xs) ≡ [x for x in xs if p(x)]  — subfunctor via comprehension
  reduce(f, xs, e) ≡ loop accumulation — catamorphism unfolded

Map-filter fusion is a naturality condition:
  map(f, filter(p, xs)) ≡ [f(x) for x in xs if p(x)]

Successive maps compose by functoriality:
  map(g, map(f, xs)) ≡ map(g∘f, xs)

Successive filters intersect predicates:
  filter(q, filter(p, xs)) ≡ filter(p∧q, xs)

Key rewrites:
  • map(f, xs) ↔ [f(x) for x in xs]
  • filter(p, xs) ↔ [x for x in xs if p(x)]
  • reduce(f, xs) ↔ loop accumulator
  • map(f, filter(p, xs)) ↔ [f(x) for x in xs if p(x)]
  • map(g, map(f, xs)) ↔ map(g∘f, xs)
  • filter(q, filter(p, xs)) ↔ filter(p∧q, xs)
  • starmap(f, xs) ↔ map with unpacking
  • map(lambda x: x, xs) ↔ list(xs)  (identity functor)
  • filter(None, xs) ↔ filter(bool, xs)
  • map(f, xs) with named fn ↔ map(lambda, xs)

(§P35, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P35_map_filter_reduce"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P01_comprehension", "P06_itertools", "P11_functional"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P35 Map / Filter / Reduce Equivalences).

1. map_fn(f, xs) ≡ listcomp_map(f, xs)
   map(f, xs) and [f(x) for x in xs] both compute the image of
   the list xs under f.  By the universal property of the free
   monoid (list), both are the unique list homomorphism lifting f.

2. filter_fn(p, xs) ≡ listcomp_filter(p, xs)
   filter(p, xs) and [x for x in xs if p(x)] both compute the
   sublist of xs satisfying p.  The filter is the equaliser of
   p and the constant-true predicate restricted to xs.

3. reduce_fn(f, xs, e) ≡ loop_accumulate(f, xs, e)
   functools.reduce(f, xs, e) and the explicit loop
   acc = e; for x in xs: acc = f(acc, x) both compute the
   catamorphism (fold) of xs with operation f and initial e.

4. map_filter_chain(f, p, xs) ≡ listcomp_map_filter(f, p, xs)
   map(f, filter(p, xs)) and [f(x) for x in xs if p(x)] are
   equal by combining rewrites (1) and (2) — naturality of map
   with respect to the subobject inclusion defined by filter.

5. map_map_fuse(g, f, xs) ≡ map_fn(compose(g, f), xs)
   map(g, map(f, xs)) = map(g∘f, xs) by functoriality of List.

6. filter_filter_fuse(q, p, xs) ≡ filter_fn(and(p, q), xs)
   filter(q, filter(p, xs)) = filter(λx. p(x)∧q(x), xs) since
   iterated equalisers compose via conjunction.

7. starmap(f, xs) ≡ map_unpack(f, xs)
   itertools.starmap(f, xs) and [f(*args) for args in xs] both
   apply f to unpacked elements of xs.

8. map_lambda(f_body, xs) ≡ map_named(f_name, xs)
   map(lambda x: expr, xs) ≡ map(named_fn, xs) when named_fn
   is defined as def named_fn(x): return expr.

9. filter_none(xs) ≡ filter_identity(xs)
   filter(None, xs) ≡ filter(bool, xs) — both remove falsy values.

10. map_fn(identity, xs) ≡ list(xs)
    map(lambda x: x, xs) ≡ list(xs) — the identity functor
    applied to a list is the list itself.
"""

EXAMPLES = [
    ("map_fn($f, $xs)", "listcomp_map($f, $xs)", "P35_map_to_listcomp"),
    ("filter_fn($p, $xs)", "listcomp_filter($p, $xs)", "P35_filter_to_listcomp"),
    ("reduce_fn($f, $xs, $e)", "loop_accumulate($f, $xs, $e)", "P35_reduce_to_loop"),
    ("map_filter_chain($f, $p, $xs)", "listcomp_map_filter($f, $p, $xs)",
     "P35_map_filter_to_listcomp"),
    ("starmap($f, $xs)", "map_unpack($f, $xs)", "P35_starmap_to_unpack"),
]

_MAP_FILTER_REDUCE_OPS = frozenset({
    'map_fn', 'listcomp_map', 'filter_fn', 'listcomp_filter',
    'reduce_fn', 'loop_accumulate', 'map_filter_chain',
    'listcomp_map_filter', 'map_map_fuse', 'filter_filter_fuse',
    'starmap', 'map_unpack', 'map_lambda', 'map_named',
    'filter_none', 'filter_identity',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P35: Map/filter/reduce equivalence rewrites (forward)."""
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp):
        return results

    # ── 1. map_fn ↔ listcomp_map ──
    if term.name == 'map_fn' and len(term.args) == 2:
        results.append((
            OOp('listcomp_map', term.args),
            'P35_map_to_listcomp',
        ))

    if term.name == 'listcomp_map' and len(term.args) == 2:
        results.append((
            OOp('map_fn', term.args),
            'P35_listcomp_to_map',
        ))

    # ── 2. filter_fn ↔ listcomp_filter ──
    if term.name == 'filter_fn' and len(term.args) == 2:
        results.append((
            OOp('listcomp_filter', term.args),
            'P35_filter_to_listcomp',
        ))

    if term.name == 'listcomp_filter' and len(term.args) == 2:
        results.append((
            OOp('filter_fn', term.args),
            'P35_listcomp_to_filter',
        ))

    # ── 3. reduce_fn ↔ loop_accumulate ──
    if term.name == 'reduce_fn' and len(term.args) >= 2:
        results.append((
            OOp('loop_accumulate', term.args),
            'P35_reduce_to_loop',
        ))

    if term.name == 'loop_accumulate' and len(term.args) >= 2:
        results.append((
            OOp('reduce_fn', term.args),
            'P35_loop_to_reduce',
        ))

    # ── 4. map_filter_chain ↔ listcomp_map_filter ──
    if term.name == 'map_filter_chain' and len(term.args) == 3:
        results.append((
            OOp('listcomp_map_filter', term.args),
            'P35_map_filter_to_listcomp',
        ))

    if term.name == 'listcomp_map_filter' and len(term.args) == 3:
        results.append((
            OOp('map_filter_chain', term.args),
            'P35_listcomp_to_map_filter',
        ))

    # ── 5. map_map_fuse: map(g, map(f, xs)) → map(g∘f, xs) ──
    if term.name == 'map_map_fuse' and len(term.args) == 3:
        g, f, xs = term.args
        composed = OOp('compose', (g, f))
        results.append((
            OOp('map_fn', (composed, xs)),
            'P35_map_map_fuse',
        ))

    # detect nested map_fn(g, map_fn(f, xs)) → map_map_fuse
    if term.name == 'map_fn' and len(term.args) == 2:
        g, inner = term.args
        if isinstance(inner, OOp) and inner.name == 'map_fn' and \
                len(inner.args) == 2:
            f, xs = inner.args
            results.append((
                OOp('map_map_fuse', (g, f, xs)),
                'P35_detect_map_map_fuse',
            ))

    # ── 6. filter_filter_fuse: filter(q, filter(p, xs)) → filter(p∧q, xs) ──
    if term.name == 'filter_filter_fuse' and len(term.args) == 3:
        q, p, xs = term.args
        conj = OOp('and_pred', (p, q))
        results.append((
            OOp('filter_fn', (conj, xs)),
            'P35_filter_filter_fuse',
        ))

    # detect nested filter_fn(q, filter_fn(p, xs)) → filter_filter_fuse
    if term.name == 'filter_fn' and len(term.args) == 2:
        q, inner = term.args
        if isinstance(inner, OOp) and inner.name == 'filter_fn' and \
                len(inner.args) == 2:
            p, xs = inner.args
            results.append((
                OOp('filter_filter_fuse', (q, p, xs)),
                'P35_detect_filter_filter_fuse',
            ))

    # ── 7. starmap ↔ map_unpack ──
    if term.name == 'starmap' and len(term.args) == 2:
        results.append((
            OOp('map_unpack', term.args),
            'P35_starmap_to_unpack',
        ))

    if term.name == 'map_unpack' and len(term.args) == 2:
        results.append((
            OOp('starmap', term.args),
            'P35_unpack_to_starmap',
        ))

    # ── 8. map_lambda ↔ map_named ──
    if term.name == 'map_lambda' and len(term.args) == 2:
        results.append((
            OOp('map_named', term.args),
            'P35_lambda_to_named',
        ))

    if term.name == 'map_named' and len(term.args) == 2:
        results.append((
            OOp('map_lambda', term.args),
            'P35_named_to_lambda',
        ))

    # ── 9. filter_none ↔ filter_identity ──
    if term.name == 'filter_none' and len(term.args) == 1:
        results.append((
            OOp('filter_identity', term.args),
            'P35_none_to_identity',
        ))

    if term.name == 'filter_identity' and len(term.args) == 1:
        results.append((
            OOp('filter_none', term.args),
            'P35_identity_to_none',
        ))

    # ── 10. map_fn(identity, xs) → list(xs) ──
    if term.name == 'map_fn' and len(term.args) == 2:
        fn_arg, xs = term.args
        if isinstance(fn_arg, OLam) and len(fn_arg.params) == 1 and \
                isinstance(fn_arg.body, OVar) and \
                fn_arg.body.name == fn_arg.params[0]:
            results.append((
                OOp('list_call', (xs,)),
                'P35_map_identity_to_list',
            ))

    # ── 11. map_filter_chain → decompose to map(f, filter(p, xs)) ──
    if term.name == 'map_filter_chain' and len(term.args) == 3:
        f, p, xs = term.args
        results.append((
            OOp('map_fn', (f, OOp('filter_fn', (p, xs)))),
            'P35_chain_to_composed',
        ))

    # ── 12. reduce_fn → OFold ──
    if term.name == 'reduce_fn' and len(term.args) >= 2:
        f = term.args[0]
        xs = term.args[1]
        init = term.args[2] if len(term.args) > 2 else OLit(None)
        results.append((
            OFold('reduce', init, xs),
            'P35_reduce_to_fold',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Return reverse rewrites (comprehension → functional form)."""
    inverse_labels = {
        'P35_listcomp_to_map', 'P35_listcomp_to_filter',
        'P35_loop_to_reduce', 'P35_listcomp_to_map_filter',
        'P35_unpack_to_starmap', 'P35_named_to_lambda',
        'P35_identity_to_none',
    }
    return [(t, l) for t, l in apply(term, ctx) if l in inverse_labels]


def recognizes(term: OTerm) -> bool:
    """Return True if the term's root operator is a map/filter/reduce op."""
    if isinstance(term, OOp) and term.name in _MAP_FILTER_REDUCE_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Heuristic relevance for search-guided rewriting."""
    sc, tc = source.canon(), target.canon()
    for kw in ('map', 'filter', 'reduce', 'listcomp', 'starmap',
               'comprehension', 'accumulate', 'fold'):
        if kw in sc and kw in tc:
            return 0.9
    if ('map' in sc and 'listcomp' in tc) or \
       ('listcomp' in sc and 'map' in tc):
        return 0.85
    if ('filter' in sc and 'listcomp' in tc) or \
       ('listcomp' in sc and 'filter' in tc):
        return 0.85
    if ('reduce' in sc and 'loop' in tc) or \
       ('loop' in sc and 'reduce' in tc):
        return 0.8
    if any(k in sc for k in ('map', 'filter', 'reduce', 'starmap', 'fold')):
        return 0.3
    return 0.05


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

    # 1. map_fn → listcomp_map
    t = OOp('map_fn', (OVar('f'), OVar('xs')))
    r = apply(t)
    _assert(any(l == 'P35_map_to_listcomp' for _, l in r),
            "map → listcomp")

    # 2. listcomp_map → map_fn
    t2 = OOp('listcomp_map', (OVar('f'), OVar('xs')))
    r2 = apply(t2)
    _assert(any(l == 'P35_listcomp_to_map' for _, l in r2),
            "listcomp → map")

    # 3. filter_fn → listcomp_filter
    t3 = OOp('filter_fn', (OVar('p'), OVar('xs')))
    r3 = apply(t3)
    _assert(any(l == 'P35_filter_to_listcomp' for _, l in r3),
            "filter → listcomp")

    # 4. listcomp_filter → filter_fn
    t4 = OOp('listcomp_filter', (OVar('p'), OVar('xs')))
    r4 = apply(t4)
    _assert(any(l == 'P35_listcomp_to_filter' for _, l in r4),
            "listcomp → filter")

    # 5. reduce_fn → loop_accumulate
    t5 = OOp('reduce_fn', (OVar('f'), OVar('xs'), OLit(0)))
    r5 = apply(t5)
    _assert(any(l == 'P35_reduce_to_loop' for _, l in r5),
            "reduce → loop")

    # 6. loop_accumulate → reduce_fn
    t6 = OOp('loop_accumulate', (OVar('f'), OVar('xs'), OLit(0)))
    r6 = apply(t6)
    _assert(any(l == 'P35_loop_to_reduce' for _, l in r6),
            "loop → reduce")

    # 7. map_filter_chain → listcomp_map_filter
    t7 = OOp('map_filter_chain', (OVar('f'), OVar('p'), OVar('xs')))
    r7 = apply(t7)
    _assert(any(l == 'P35_map_filter_to_listcomp' for _, l in r7),
            "map_filter → listcomp")

    # 8. listcomp_map_filter → map_filter_chain
    t8 = OOp('listcomp_map_filter', (OVar('f'), OVar('p'), OVar('xs')))
    r8 = apply(t8)
    _assert(any(l == 'P35_listcomp_to_map_filter' for _, l in r8),
            "listcomp → map_filter")

    # 9. starmap → map_unpack
    t9 = OOp('starmap', (OVar('f'), OVar('xs')))
    r9 = apply(t9)
    _assert(any(l == 'P35_starmap_to_unpack' for _, l in r9),
            "starmap → unpack")

    # 10. map_unpack → starmap
    t10 = OOp('map_unpack', (OVar('f'), OVar('xs')))
    r10 = apply(t10)
    _assert(any(l == 'P35_unpack_to_starmap' for _, l in r10),
            "unpack → starmap")

    # 11. filter_none → filter_identity
    t11 = OOp('filter_none', (OVar('xs'),))
    r11 = apply(t11)
    _assert(any(l == 'P35_none_to_identity' for _, l in r11),
            "filter_none → identity")

    # 12. filter_identity → filter_none
    t12 = OOp('filter_identity', (OVar('xs'),))
    r12 = apply(t12)
    _assert(any(l == 'P35_identity_to_none' for _, l in r12),
            "identity → filter_none")

    # 13. map_lambda → map_named
    t13 = OOp('map_lambda', (OVar('body'), OVar('xs')))
    r13 = apply(t13)
    _assert(any(l == 'P35_lambda_to_named' for _, l in r13),
            "lambda → named")

    # 14. map_named → map_lambda
    t14 = OOp('map_named', (OVar('fn'), OVar('xs')))
    r14 = apply(t14)
    _assert(any(l == 'P35_named_to_lambda' for _, l in r14),
            "named → lambda")

    # 15. map_map_fuse → composed map
    t15 = OOp('map_map_fuse', (OVar('g'), OVar('f'), OVar('xs')))
    r15 = apply(t15)
    _assert(any(l == 'P35_map_map_fuse' for _, l in r15),
            "map_map_fuse → composed")

    # 16. nested map_fn → detect map_map_fuse
    t16 = OOp('map_fn', (OVar('g'), OOp('map_fn', (OVar('f'), OVar('xs')))))
    r16 = apply(t16)
    _assert(any(l == 'P35_detect_map_map_fuse' for _, l in r16),
            "nested map → fuse detected")

    # 17. filter_filter_fuse → conjoined filter
    t17 = OOp('filter_filter_fuse', (OVar('q'), OVar('p'), OVar('xs')))
    r17 = apply(t17)
    _assert(any(l == 'P35_filter_filter_fuse' for _, l in r17),
            "filter_filter_fuse → conjoined")

    # 18. nested filter_fn → detect filter_filter_fuse
    t18 = OOp('filter_fn', (OVar('q'), OOp('filter_fn', (OVar('p'), OVar('xs')))))
    r18 = apply(t18)
    _assert(any(l == 'P35_detect_filter_filter_fuse' for _, l in r18),
            "nested filter → fuse detected")

    # 19. map_fn(identity_lambda, xs) → list_call
    t19 = OOp('map_fn', (OLam(('x',), OVar('x')), OVar('xs')))
    r19 = apply(t19)
    _assert(any(l == 'P35_map_identity_to_list' for _, l in r19),
            "map(id) → list")

    # 20. reduce_fn → OFold
    _assert(any(l == 'P35_reduce_to_fold' for _, l in r5),
            "reduce → fold")

    # 21. map_filter_chain → decomposed chain
    _assert(any(l == 'P35_chain_to_composed' for _, l in r7),
            "chain → composed map(f, filter(p, xs))")

    # 22. inverse: listcomp_map → map_fn
    r22_inv = apply_inverse(OOp('listcomp_map', (OVar('f'), OVar('xs'))))
    _assert(any(l == 'P35_listcomp_to_map' for _, l in r22_inv),
            "inv: listcomp → map")

    # 23. inverse: loop_accumulate → reduce_fn
    r23_inv = apply_inverse(OOp('loop_accumulate', (OVar('f'), OVar('xs'))))
    _assert(any(l == 'P35_loop_to_reduce' for _, l in r23_inv),
            "inv: loop → reduce")

    # 24. recognizes map/filter/reduce ops
    _assert(recognizes(OOp('map_fn', (OVar('f'), OVar('xs')))),
            "recognizes map_fn")
    _assert(recognizes(OOp('filter_fn', (OVar('p'), OVar('xs')))),
            "recognizes filter_fn")
    _assert(recognizes(OOp('reduce_fn', (OVar('f'), OVar('xs')))),
            "recognizes reduce_fn")
    _assert(recognizes(OOp('starmap', (OVar('f'), OVar('xs')))),
            "recognizes starmap")
    _assert(not recognizes(OLit(42)), "!recognizes literal")
    _assert(not recognizes(OVar('x')), "!recognizes var")

    # 25. relevance: map ↔ listcomp high
    _assert(relevance_score(
        OOp('map_fn', (OVar('f'), OVar('xs'))),
        OOp('listcomp_map', (OVar('f'), OVar('xs'))),
    ) > 0.7, "map/listcomp relevance high")

    # 26. relevance: reduce ↔ loop high
    _assert(relevance_score(
        OOp('reduce_fn', (OVar('f'), OVar('xs'))),
        OOp('loop_accumulate', (OVar('f'), OVar('xs'))),
    ) > 0.7, "reduce/loop relevance high")

    # 27. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2,
            "unrelated relevance low")

    print(f"P35 map_filter_reduce: {_pass} passed, {_fail} failed")
