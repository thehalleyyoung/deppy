"""P45 Axiom: Functools Advanced Equivalences.

Establishes equivalences between Python's functools module utilities
and their manual equivalents: functools.partial ↔ lambda wrapper,
functools.reduce ↔ explicit loop, @functools.wraps ↔ manual
__name__/__doc__ assignment, @functools.total_ordering ↔ manual
comparison methods, functools.cache ↔ lru_cache(maxsize=None),
and @singledispatch ↔ isinstance chain.

Mathematical basis: functools.partial implements the currying
isomorphism in the category of Python callables:

  curry : (A × B → C) ≅ (A → (B → C))
  partial(f, a) = curry(f)(a)

functools.reduce is the unique catamorphism (fold) over lists:

  reduce(op, [x₁, …, xₙ], init) = op(…op(op(init, x₁), x₂)…, xₙ)

@total_ordering extends a partial order (given __eq__ and one of
__lt__, __le__, __gt__, __ge__) to the total order by computing
the remaining comparisons.

Key rewrites:
  • partial(f, a) ↔ lambda x: f(a, x)
  • reduce(op, xs, init) ↔ loop accumulation
  • @wraps(f) ↔ manual __name__/__doc__
  • @total_ordering ↔ all comparison methods
  • cache ↔ lru_cache(maxsize=None)
  • @singledispatch ↔ isinstance chain
  • partial_method ↔ lambda on self
  • reduce without init ↔ loop with xs[0]
  • lru_cache(n) ↔ manual memo dict with eviction

(§P45, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P45_functools"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P11_functional", "P35_map_filter_reduce", "P40_curry"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P45 Functools Advanced Equivalences).

1. partial_fn(f, a) ≡ lambda_partial(f, a)
   functools.partial(f, a) ≡ lambda x: f(a, x).
   Both fix the first argument of f to a.

2. reduce_fn(op, xs, init) ≡ loop_reduce(op, xs, init)
   functools.reduce(op, xs, init) ≡ for x in xs: init = op(init, x).
   Both fold left over xs with op.

3. wraps_decorator(f) ≡ manual_wraps(f)
   @wraps(f) copies __name__, __doc__, __module__, etc.
   Manual assignment achieves the same.

4. total_ordering(cls) ≡ manual_ordering(cls)
   @total_ordering generates missing comparison methods.
   Manual definition of __lt__, __le__, __gt__, __ge__ is equivalent.

5. cache_fn(f) ≡ lru_cache_none(f)
   @cache ≡ @lru_cache(maxsize=None).
   Both memoize without eviction.

6. singledispatch(f) ≡ isinstance_chain(f)
   @singledispatch dispatches by type of first argument.
   isinstance chain performs the same dispatch manually.

7. partial_method(f, a) ≡ lambda_method(f, a)
   functools.partialmethod(f, a) ≡ lambda self, x: f(self, a, x).
   partialmethod for descriptors.

8. reduce_init(op, xs) ≡ loop_reduce_init(op, xs)
   reduce(op, xs) without init ≡ loop starting with xs[0].

9. lru_cache_fn(f, n) ≡ manual_memo_dict(f, n)
   @lru_cache(maxsize=n) ≡ manual dict with LRU eviction.

10. partial(f, a)(b) → f(a, b)  (beta-reduction of partial).

11. reduce(op, [x], init) → op(init, x)  (single-element fold).

12. cache(f) is idempotent: cache(cache(f)) ≡ cache(f).
"""

EXAMPLES = [
    ("partial_fn($f, $a)", "lambda_partial($f, $a)",
     "P45_partial_to_lambda"),
    ("reduce_fn($op, $xs, $init)", "loop_reduce($op, $xs, $init)",
     "P45_reduce_to_loop"),
    ("cache_fn($f)", "lru_cache_none($f)",
     "P45_cache_to_lru_cache"),
    ("singledispatch($f)", "isinstance_chain($f)",
     "P45_singledispatch_to_isinstance"),
    ("total_ordering($cls)", "manual_ordering($cls)",
     "P45_total_ordering_to_manual"),
]

_FUNCTOOLS_OPS = frozenset({
    'partial_fn', 'lambda_partial', 'reduce_fn', 'loop_reduce',
    'wraps_decorator', 'manual_wraps', 'total_ordering',
    'manual_ordering', 'cache_fn', 'lru_cache_none',
    'singledispatch', 'isinstance_chain', 'partial_method',
    'lambda_method', 'reduce_init', 'loop_reduce_init',
    'lru_cache_fn', 'manual_memo_dict',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P45: Functools equivalence rewrites (forward)."""
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp):
        return results

    # ── 1. partial_fn(f, a) ↔ lambda_partial(f, a) ──
    if term.name == 'partial_fn' and len(term.args) == 2:
        results.append((
            OOp('lambda_partial', term.args),
            'P45_partial_to_lambda',
        ))

    if term.name == 'lambda_partial' and len(term.args) == 2:
        results.append((
            OOp('partial_fn', term.args),
            'P45_lambda_to_partial',
        ))

    # ── 2. reduce_fn(op, xs, init) ↔ loop_reduce(op, xs, init) ──
    if term.name == 'reduce_fn' and len(term.args) == 3:
        results.append((
            OOp('loop_reduce', term.args),
            'P45_reduce_to_loop',
        ))

    if term.name == 'loop_reduce' and len(term.args) == 3:
        results.append((
            OOp('reduce_fn', term.args),
            'P45_loop_to_reduce',
        ))

    # ── 3. wraps_decorator(f) ↔ manual_wraps(f) ──
    if term.name == 'wraps_decorator' and len(term.args) >= 1:
        results.append((
            OOp('manual_wraps', term.args),
            'P45_wraps_to_manual',
        ))

    if term.name == 'manual_wraps' and len(term.args) >= 1:
        results.append((
            OOp('wraps_decorator', term.args),
            'P45_manual_to_wraps',
        ))

    # ── 4. total_ordering(cls) ↔ manual_ordering(cls) ──
    if term.name == 'total_ordering' and len(term.args) == 1:
        results.append((
            OOp('manual_ordering', term.args),
            'P45_total_ordering_to_manual',
        ))

    if term.name == 'manual_ordering' and len(term.args) == 1:
        results.append((
            OOp('total_ordering', term.args),
            'P45_manual_to_total_ordering',
        ))

    # ── 5. cache_fn(f) ↔ lru_cache_none(f) ──
    if term.name == 'cache_fn' and len(term.args) == 1:
        results.append((
            OOp('lru_cache_none', term.args),
            'P45_cache_to_lru_cache',
        ))

    if term.name == 'lru_cache_none' and len(term.args) == 1:
        results.append((
            OOp('cache_fn', term.args),
            'P45_lru_cache_to_cache',
        ))

    # ── 6. singledispatch(f) ↔ isinstance_chain(f) ──
    if term.name == 'singledispatch' and len(term.args) == 1:
        results.append((
            OOp('isinstance_chain', term.args),
            'P45_singledispatch_to_isinstance',
        ))

    if term.name == 'isinstance_chain' and len(term.args) == 1:
        results.append((
            OOp('singledispatch', term.args),
            'P45_isinstance_to_singledispatch',
        ))

    # ── 7. partial_method(f, a) ↔ lambda_method(f, a) ──
    if term.name == 'partial_method' and len(term.args) == 2:
        results.append((
            OOp('lambda_method', term.args),
            'P45_partial_method_to_lambda',
        ))

    if term.name == 'lambda_method' and len(term.args) == 2:
        results.append((
            OOp('partial_method', term.args),
            'P45_lambda_to_partial_method',
        ))

    # ── 8. reduce_init(op, xs) ↔ loop_reduce_init(op, xs) ──
    if term.name == 'reduce_init' and len(term.args) == 2:
        results.append((
            OOp('loop_reduce_init', term.args),
            'P45_reduce_init_to_loop',
        ))

    if term.name == 'loop_reduce_init' and len(term.args) == 2:
        results.append((
            OOp('reduce_init', term.args),
            'P45_loop_to_reduce_init',
        ))

    # ── 9. lru_cache_fn(f, n) ↔ manual_memo_dict(f, n) ──
    if term.name == 'lru_cache_fn' and len(term.args) == 2:
        results.append((
            OOp('manual_memo_dict', term.args),
            'P45_lru_cache_to_memo_dict',
        ))

    if term.name == 'manual_memo_dict' and len(term.args) == 2:
        results.append((
            OOp('lru_cache_fn', term.args),
            'P45_memo_dict_to_lru_cache',
        ))

    # ── 10. partial_fn(f, a) → OLam structural form ──
    if term.name == 'partial_fn' and len(term.args) == 2:
        f, a = term.args
        results.append((
            OLam(('x',), OOp('call', (f, a, OVar('x')))),
            'P45_partial_to_olam',
        ))

    # ── 11. reduce_fn → OFold structural form ──
    if term.name == 'reduce_fn' and len(term.args) == 3:
        op, xs, init = term.args
        results.append((
            OFold(op.canon() if hasattr(op, 'canon') else 'op', init, xs),
            'P45_reduce_to_ofold',
        ))

    # ── 12. reduce_fn(op, [x], init) → op(init, x) ──
    if term.name == 'reduce_fn' and len(term.args) == 3:
        op, xs, init = term.args
        if isinstance(xs, OSeq) and len(xs.elements) == 1:
            results.append((
                OOp('call', (op, init, xs.elements[0])),
                'P45_reduce_single_element',
            ))

    # ── 13. cache(cache(f)) → cache(f) (idempotent) ──
    if term.name == 'cache_fn' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'cache_fn':
            results.append((
                inner,
                'P45_cache_idempotent',
            ))

    # ── 14. singledispatch → OCase chain structural form ──
    if term.name == 'singledispatch' and len(term.args) == 1:
        f = term.args[0]
        results.append((
            OCase(
                OOp('isinstance', (OVar('arg'), OVar('type1'))),
                OOp('dispatch_1', (OVar('arg'),)),
                OCase(
                    OOp('isinstance', (OVar('arg'), OVar('type2'))),
                    OOp('dispatch_2', (OVar('arg'),)),
                    OOp('call', (f, OVar('arg'))),
                ),
            ),
            'P45_singledispatch_to_case_chain',
        ))

    # ── 15. reduce_init(op, xs) → OCase (empty check) + OFold ──
    if term.name == 'reduce_init' and len(term.args) == 2:
        op, xs = term.args
        results.append((
            OCase(
                OOp('len', (xs,)),
                OFold(op.canon() if hasattr(op, 'canon') else 'op',
                      OOp('getitem', (xs, OLit(0))),
                      OOp('slice', (xs, OLit(1)))),
                OUnknown('TypeError: reduce() of empty sequence'),
            ),
            'P45_reduce_init_to_case_fold',
        ))

    # ── 16. lru_cache_fn → OCatch (memo lookup) structural ──
    if term.name == 'lru_cache_fn' and len(term.args) == 2:
        f, n = term.args
        results.append((
            OLam(('args',), OCatch(
                OOp('dict_get', (OVar('_cache'), OVar('args'))),
                OOp('call_and_store', (f, OVar('args'), OVar('_cache'))),
            )),
            'P45_lru_cache_to_memo_lambda',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Return reverse rewrites (manual → functools form)."""
    inverse_labels = {
        'P45_lambda_to_partial', 'P45_loop_to_reduce',
        'P45_manual_to_wraps', 'P45_manual_to_total_ordering',
        'P45_lru_cache_to_cache', 'P45_isinstance_to_singledispatch',
        'P45_lambda_to_partial_method', 'P45_loop_to_reduce_init',
        'P45_memo_dict_to_lru_cache',
    }
    return [(t, l) for t, l in apply(term, ctx) if l in inverse_labels]


def recognizes(term: OTerm) -> bool:
    """Return True if the term's root operator is a functools op."""
    if isinstance(term, OOp) and term.name in _FUNCTOOLS_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Heuristic relevance for search-guided rewriting."""
    sc, tc = source.canon(), target.canon()
    for kw in ('partial_fn', 'lambda_partial', 'reduce_fn', 'loop_reduce',
               'wraps_decorator', 'manual_wraps', 'total_ordering',
               'manual_ordering', 'cache_fn', 'lru_cache_none',
               'singledispatch', 'isinstance_chain', 'partial_method',
               'lambda_method', 'reduce_init', 'loop_reduce_init',
               'lru_cache_fn', 'manual_memo_dict'):
        if kw in sc and kw in tc:
            return 0.9
    if ('partial_fn' in sc and 'lambda_partial' in tc) or \
       ('lambda_partial' in sc and 'partial_fn' in tc):
        return 0.85
    if ('reduce_fn' in sc and 'loop_reduce' in tc) or \
       ('loop_reduce' in sc and 'reduce_fn' in tc):
        return 0.85
    if ('cache_fn' in sc and 'lru_cache' in tc) or \
       ('lru_cache' in sc and 'cache_fn' in tc):
        return 0.85
    if ('singledispatch' in sc and 'isinstance' in tc) or \
       ('isinstance' in sc and 'singledispatch' in tc):
        return 0.8
    if ('total_ordering' in sc and 'manual_ordering' in tc) or \
       ('manual_ordering' in sc and 'total_ordering' in tc):
        return 0.8
    if any(k in sc for k in ('partial', 'reduce', 'wraps', 'cache',
                             'singledispatch', 'total_ordering',
                             'lru_cache', 'memo')):
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

    # 1. partial_fn → lambda_partial
    t = OOp('partial_fn', (OVar('f'), OVar('a')))
    r = apply(t)
    _assert(any(l == 'P45_partial_to_lambda' for _, l in r),
            "partial → lambda")

    # 2. lambda_partial → partial_fn
    t2 = OOp('lambda_partial', (OVar('f'), OVar('a')))
    r2 = apply(t2)
    _assert(any(l == 'P45_lambda_to_partial' for _, l in r2),
            "lambda → partial")

    # 3. reduce_fn → loop_reduce
    t3 = OOp('reduce_fn', (OVar('op'), OVar('xs'), OVar('init')))
    r3 = apply(t3)
    _assert(any(l == 'P45_reduce_to_loop' for _, l in r3),
            "reduce → loop")

    # 4. loop_reduce → reduce_fn
    t4 = OOp('loop_reduce', (OVar('op'), OVar('xs'), OVar('init')))
    r4 = apply(t4)
    _assert(any(l == 'P45_loop_to_reduce' for _, l in r4),
            "loop → reduce")

    # 5. wraps_decorator → manual_wraps
    t5 = OOp('wraps_decorator', (OVar('f'),))
    r5 = apply(t5)
    _assert(any(l == 'P45_wraps_to_manual' for _, l in r5),
            "wraps → manual")

    # 6. manual_wraps → wraps_decorator
    t6 = OOp('manual_wraps', (OVar('f'),))
    r6 = apply(t6)
    _assert(any(l == 'P45_manual_to_wraps' for _, l in r6),
            "manual → wraps")

    # 7. total_ordering → manual_ordering
    t7 = OOp('total_ordering', (OVar('cls'),))
    r7 = apply(t7)
    _assert(any(l == 'P45_total_ordering_to_manual' for _, l in r7),
            "total_ordering → manual")

    # 8. manual_ordering → total_ordering
    t8 = OOp('manual_ordering', (OVar('cls'),))
    r8 = apply(t8)
    _assert(any(l == 'P45_manual_to_total_ordering' for _, l in r8),
            "manual → total_ordering")

    # 9. cache_fn → lru_cache_none
    t9 = OOp('cache_fn', (OVar('f'),))
    r9 = apply(t9)
    _assert(any(l == 'P45_cache_to_lru_cache' for _, l in r9),
            "cache → lru_cache")

    # 10. lru_cache_none → cache_fn
    t10 = OOp('lru_cache_none', (OVar('f'),))
    r10 = apply(t10)
    _assert(any(l == 'P45_lru_cache_to_cache' for _, l in r10),
            "lru_cache → cache")

    # 11. singledispatch → isinstance_chain
    t11 = OOp('singledispatch', (OVar('f'),))
    r11 = apply(t11)
    _assert(any(l == 'P45_singledispatch_to_isinstance' for _, l in r11),
            "singledispatch → isinstance")

    # 12. isinstance_chain → singledispatch
    t12 = OOp('isinstance_chain', (OVar('f'),))
    r12 = apply(t12)
    _assert(any(l == 'P45_isinstance_to_singledispatch' for _, l in r12),
            "isinstance → singledispatch")

    # 13. partial_method → lambda_method
    t13 = OOp('partial_method', (OVar('f'), OVar('a')))
    r13 = apply(t13)
    _assert(any(l == 'P45_partial_method_to_lambda' for _, l in r13),
            "partial_method → lambda")

    # 14. lambda_method → partial_method
    t14 = OOp('lambda_method', (OVar('f'), OVar('a')))
    r14 = apply(t14)
    _assert(any(l == 'P45_lambda_to_partial_method' for _, l in r14),
            "lambda → partial_method")

    # 15. reduce_init → loop_reduce_init
    t15 = OOp('reduce_init', (OVar('op'), OVar('xs')))
    r15 = apply(t15)
    _assert(any(l == 'P45_reduce_init_to_loop' for _, l in r15),
            "reduce_init → loop")

    # 16. loop_reduce_init → reduce_init
    t16 = OOp('loop_reduce_init', (OVar('op'), OVar('xs')))
    r16 = apply(t16)
    _assert(any(l == 'P45_loop_to_reduce_init' for _, l in r16),
            "loop → reduce_init")

    # 17. lru_cache_fn → manual_memo_dict
    t17 = OOp('lru_cache_fn', (OVar('f'), OLit(128)))
    r17 = apply(t17)
    _assert(any(l == 'P45_lru_cache_to_memo_dict' for _, l in r17),
            "lru_cache → memo_dict")

    # 18. manual_memo_dict → lru_cache_fn
    t18 = OOp('manual_memo_dict', (OVar('f'), OLit(128)))
    r18 = apply(t18)
    _assert(any(l == 'P45_memo_dict_to_lru_cache' for _, l in r18),
            "memo_dict → lru_cache")

    # 19. partial_fn → OLam structural
    _assert(any(l == 'P45_partial_to_olam' for _, l in r),
            "partial → OLam")
    lam_results = [(t, l) for t, l in r if l == 'P45_partial_to_olam']
    if lam_results:
        _assert(isinstance(lam_results[0][0], OLam),
                "partial produces OLam")
    else:
        _assert(False, "partial produces OLam")

    # 20. reduce_fn → OFold structural
    _assert(any(l == 'P45_reduce_to_ofold' for _, l in r3),
            "reduce → OFold")
    fold_results = [(t, l) for t, l in r3 if l == 'P45_reduce_to_ofold']
    if fold_results:
        _assert(isinstance(fold_results[0][0], OFold),
                "reduce produces OFold")
    else:
        _assert(False, "reduce produces OFold")

    # 21. reduce single element simplification
    t21 = OOp('reduce_fn', (OVar('op'), OSeq((OVar('x'),)), OVar('init')))
    r21 = apply(t21)
    _assert(any(l == 'P45_reduce_single_element' for _, l in r21),
            "reduce single → call")

    # 22. cache idempotent
    t22 = OOp('cache_fn', (OOp('cache_fn', (OVar('f'),)),))
    r22 = apply(t22)
    _assert(any(l == 'P45_cache_idempotent' for _, l in r22),
            "cache(cache(f)) → cache(f)")
    idemp_results = [(t, l) for t, l in r22 if l == 'P45_cache_idempotent']
    if idemp_results:
        rr = idemp_results[0][0]
        _assert(isinstance(rr, OOp) and rr.name == 'cache_fn',
                "cache idempotent produces cache_fn")
    else:
        _assert(False, "cache idempotent produces cache_fn")

    # 23. singledispatch → OCase chain
    _assert(any(l == 'P45_singledispatch_to_case_chain' for _, l in r11),
            "singledispatch → case chain")
    case_results = [(t, l) for t, l in r11
                    if l == 'P45_singledispatch_to_case_chain']
    if case_results:
        _assert(isinstance(case_results[0][0], OCase),
                "singledispatch produces OCase")
    else:
        _assert(False, "singledispatch produces OCase")

    # 24. reduce_init → OCase + OFold structural
    _assert(any(l == 'P45_reduce_init_to_case_fold' for _, l in r15),
            "reduce_init → case+fold")

    # 25. lru_cache → memo lambda structural
    _assert(any(l == 'P45_lru_cache_to_memo_lambda' for _, l in r17),
            "lru_cache → memo lambda")

    # 26. inverse: lambda → partial
    r26_inv = apply_inverse(OOp('lambda_partial', (OVar('f'), OVar('a'))))
    _assert(any(l == 'P45_lambda_to_partial' for _, l in r26_inv),
            "inv: lambda → partial")

    # 27. inverse: loop → reduce
    r27_inv = apply_inverse(
        OOp('loop_reduce', (OVar('op'), OVar('xs'), OVar('init'))))
    _assert(any(l == 'P45_loop_to_reduce' for _, l in r27_inv),
            "inv: loop → reduce")

    # 28. inverse: isinstance → singledispatch
    r28_inv = apply_inverse(OOp('isinstance_chain', (OVar('f'),)))
    _assert(any(l == 'P45_isinstance_to_singledispatch' for _, l in r28_inv),
            "inv: isinstance → singledispatch")

    # 29. recognizes functools ops
    _assert(recognizes(OOp('partial_fn', (OVar('f'), OVar('a')))),
            "recognizes partial_fn")
    _assert(recognizes(OOp('reduce_fn', (OVar('op'), OVar('xs'), OVar('i')))),
            "recognizes reduce_fn")
    _assert(recognizes(OOp('singledispatch', (OVar('f'),))),
            "recognizes singledispatch")
    _assert(not recognizes(OLit(42)), "!recognizes literal")
    _assert(not recognizes(OVar('x')), "!recognizes var")

    # 30. relevance: partial ↔ lambda high
    _assert(relevance_score(
        OOp('partial_fn', (OVar('f'), OVar('a'))),
        OOp('lambda_partial', (OVar('f'), OVar('a'))),
    ) > 0.7, "partial/lambda relevance high")

    # 31. relevance: reduce ↔ loop high
    _assert(relevance_score(
        OOp('reduce_fn', (OVar('op'), OVar('xs'), OVar('i'))),
        OOp('loop_reduce', (OVar('op'), OVar('xs'), OVar('i'))),
    ) > 0.7, "reduce/loop relevance high")

    # 32. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2,
            "unrelated relevance low")

    # 33. no rewrites for non-OOp
    _assert(apply(OVar('x')) == [], "no rewrites for OVar")
    _assert(apply(OLit(42)) == [], "no rewrites for OLit")

    print(f"P45 functools: {_pass} passed, {_fail} failed")
