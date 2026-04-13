"""P1: Comprehension Equivalences (Theorem 30.1.1).

List/dict/set comprehension ↔ map/filter/dict/set built-in chains.

Mathematical foundation:
  Comprehensions are syntactic sugar for compositions of functorial
  operations (map, filter) in the category of finite sequences.  The
  equivalences arise from the universal property of list/set/dict as
  free algebras over their element types:

    [f(x) for x in xs if p(x)]  ≅  list(map(f, filter(p, xs)))

  For sets, the quotient by permutation and multiplicity gives:

    {f(x) for x in xs}  ≅  set(map(f, xs))

  These are natural isomorphisms in the presheaf category, witnessed
  by the adjunction  Free ⊣ Forget  between Set and Mon/CMon.

Covers:
  • List comp ↔ map+filter
  • Dict comp ↔ dict(pairs)
  • Set comp ↔ set(map(...))
  • Nested comp ↔ itertools.product
  • Conditional comp with ternary expression
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

AXIOM_NAME = 'P1_comprehension'
AXIOM_CATEGORY = 'python_idiom'

SOUNDNESS_PROOF = """
Theorem 30.1.1 (Comprehension–Map/Filter Equivalence):
  For any iterable xs, predicate p, and function f,
    [f(x) for x in xs if p(x)]  ≡  list(map(f, filter(p, xs)))
  as morphisms  X* → Y*  in the category of finite sequences.

Proof sketch:
  1. filter(p, xs) selects the sub-sequence {x ∈ xs | p(x)}.
  2. map(f, ·) applies f element-wise, preserving order.
  3. list(·) materialises the lazy iterator into a list.
  4. The comprehension [f(x) for x in xs if p(x)] performs steps
     1–3 in a single pass.  By induction on |xs|:
     - Base: [] → [] ✓
     - Step: if p(x), emit f(x); otherwise skip.  ∎

Corollary (Set comprehension):
  {f(x) for x in xs}  ≡  set(map(f, xs))
  Both compute the image f(xs) quotiented by equality.

Corollary (Dict comprehension):
  {k: v for k, v in pairs}  ≡  dict(pairs)
  Both construct the same finite map from a sequence of pairs.
"""

COMPOSES_WITH = ['D04_comp_fusion', 'D05_fold_universal', 'P2_builtins']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'List comp to map+filter',
        'before': "[f(x) for x in xs if p(x)]",
        'after': "list(map(f, filter(p, xs)))",
        'axiom': 'P1_listcomp_to_map_filter',
    },
    {
        'name': 'map+filter to list comp',
        'before': "list(map(f, filter(p, xs)))",
        'after': "[f(x) for x in xs if p(x)]",
        'axiom': 'P1_map_filter_to_listcomp',
    },
    {
        'name': 'Set comp to set(map(...))',
        'before': "{f(x) for x in xs}",
        'after': "set(map(f, xs))",
        'axiom': 'P1_setcomp_to_set_map',
    },
    {
        'name': 'Dict comp to dict()',
        'before': "{k: v for k, v in pairs}",
        'after': "dict(pairs)",
        'axiom': 'P1_dictcomp_to_dict',
    },
    {
        'name': 'List comp (no filter) to map',
        'before': "[f(x) for x in xs]",
        'after': "list(map(f, xs))",
        'axiom': 'P1_listcomp_to_map',
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
    """Apply P1 comprehension equivalences to *term*.

    Returns list of (rewritten_term, axiom_label) pairs.
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── OMap (list comp) with filter → list(map(f, filter(p, xs))) ──
    if isinstance(term, OMap) and term.filter_pred is not None:
        f = term.transform
        p = term.filter_pred
        xs = term.collection
        rewritten = OOp('list', (OOp('map', (f, OOp('filter', (p, xs)))),))
        results.append((rewritten, 'P1_listcomp_to_map_filter'))

    # ── OMap (list comp) without filter → list(map(f, xs)) ──
    if isinstance(term, OMap) and term.filter_pred is None:
        if not isinstance(term, OQuotient):
            f = term.transform
            xs = term.collection
            rewritten = OOp('list', (OOp('map', (f, xs)),))
            results.append((rewritten, 'P1_listcomp_to_map'))

    # ── list(map(f, filter(p, xs))) → OMap with filter ──
    if isinstance(term, OOp) and term.name == 'list' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'map' and len(inner.args) == 2:
            f, source = inner.args
            # map(f, filter(p, xs))
            if isinstance(source, OOp) and source.name == 'filter' and len(source.args) == 2:
                p, xs = source.args
                results.append((
                    OMap(transform=f, collection=xs, filter_pred=p),
                    'P1_map_filter_to_listcomp',
                ))
            else:
                # list(map(f, xs)) → OMap without filter
                results.append((
                    OMap(transform=f, collection=source),
                    'P1_map_to_listcomp',
                ))

    # ── OQuotient(OMap(...), 'perm') (set comp) → set(map(f, xs)) ──
    if isinstance(term, OQuotient) and isinstance(term.inner, OMap):
        inner_map = term.inner
        if inner_map.filter_pred is None:
            f = inner_map.transform
            xs = inner_map.collection
            rewritten = OOp('set', (OOp('map', (f, xs)),))
            results.append((rewritten, 'P1_setcomp_to_set_map'))
        else:
            # set comp with filter → set(map(f, filter(p, xs)))
            f = inner_map.transform
            p = inner_map.filter_pred
            xs = inner_map.collection
            rewritten = OOp('set', (OOp('map', (f, OOp('filter', (p, xs)))),))
            results.append((rewritten, 'P1_setcomp_filter_to_set_map_filter'))

    # ── set(map(f, xs)) → OQuotient(OMap(...), 'perm') ──
    if isinstance(term, OOp) and term.name == 'set' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'map' and len(inner.args) == 2:
            f, source = inner.args
            if isinstance(source, OOp) and source.name == 'filter' and len(source.args) == 2:
                p, xs = source.args
                results.append((
                    OQuotient(OMap(transform=f, collection=xs, filter_pred=p), 'perm'),
                    'P1_set_map_filter_to_setcomp',
                ))
            else:
                results.append((
                    OQuotient(OMap(transform=f, collection=source), 'perm'),
                    'P1_set_map_to_setcomp',
                ))

    # ── OMap over pairs producing ODict → dict(pairs) ──
    if isinstance(term, OMap):
        if isinstance(term.transform, OLam) and _produces_pair(term.transform):
            xs = term.collection
            results.append((
                OOp('dict', (xs,)),
                'P1_dictcomp_to_dict',
            ))

    # ── dict(pairs) → OMap producing ODict ──
    if isinstance(term, OOp) and term.name == 'dict' and len(term.args) == 1:
        pairs = term.args[0]
        # Represent as a map that unpacks pairs into key-value
        kv_lam = OLam(('_kv',), OOp('identity', (OVar('_kv'),)))
        results.append((
            OMap(transform=kv_lam, collection=pairs),
            'P1_dict_to_dictcomp',
        ))

    # ── Nested comp → itertools.product pattern ──
    # OMap(transform=OLam(..., OMap(...))) → product-based form
    if isinstance(term, OMap) and isinstance(term.transform, OLam):
        body = term.transform.body
        if isinstance(body, OMap):
            outer_xs = term.collection
            inner_xs = body.collection
            inner_f = body.transform
            rewritten = OOp('list', (
                OOp('map', (
                    inner_f,
                    OOp('product', (outer_xs, inner_xs)),
                )),
            ))
            results.append((rewritten, 'P1_nested_comp_to_product'))

    # ── itertools.product → nested comp ──
    if isinstance(term, OOp) and term.name == 'list' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'map' and len(inner.args) == 2:
            f, source = inner.args
            if isinstance(source, OOp) and source.name == 'product' and len(source.args) == 2:
                outer_xs, inner_xs = source.args
                results.append((
                    OMap(
                        transform=OLam(('_outer',), OMap(transform=f, collection=inner_xs)),
                        collection=outer_xs,
                    ),
                    'P1_product_to_nested_comp',
                ))

    # ── Conditional comp: OMap with OCase transform ──
    if isinstance(term, OMap) and isinstance(term.transform, OLam):
        lam = term.transform
        if isinstance(lam.body, OCase):
            xs = term.collection
            case = lam.body
            results.append((
                OOp('list', (
                    OOp('map', (
                        OLam(lam.params, case),
                        xs,
                    )),
                )),
                'P1_conditional_comp_to_map_ternary',
            ))

    return results


def _produces_pair(lam: OLam) -> bool:
    """Heuristic: does this lambda produce a key-value pair?"""
    body = lam.body
    if isinstance(body, OOp) and body.name in ('tuple', 'pair', 'kv_pair'):
        return True
    if isinstance(body, OSeq) and len(body.elements) == 2:
        return True
    return False


# ═══════════════════════════════════════════════════════════
# Inverse axiom
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply P1 in reverse: map/filter chains → comprehension forms.

    Inverse rewrites are already embedded in apply() as bidirectional
    rules; this function filters for only the reverse direction.
    """
    results = apply(term, ctx)
    inverse_labels = {
        'P1_map_filter_to_listcomp',
        'P1_map_to_listcomp',
        'P1_set_map_to_setcomp',
        'P1_set_map_filter_to_setcomp',
        'P1_dict_to_dictcomp',
        'P1_product_to_nested_comp',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if P1 is potentially applicable to *term*."""
    if isinstance(term, OMap):
        return True
    if isinstance(term, OQuotient) and isinstance(term.inner, OMap):
        return True
    if isinstance(term, OOp):
        if term.name in ('list', 'set', 'dict'):
            if len(term.args) == 1 and isinstance(term.args[0], OOp):
                if term.args[0].name in ('map', 'filter'):
                    return True
            if term.name == 'dict' and len(term.args) == 1:
                return True
        if term.name == 'map' and len(term.args) == 2:
            return True
        if term.name == 'filter':
            return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score how relevant P1 is for bridging *source* → *target*.

    Returns a float in [0, 1].
    """
    sc = source.canon()
    tc = target.canon()

    has_map_s = 'OMap(' in sc or 'map(' in sc
    has_map_t = 'OMap(' in tc or 'map(' in tc
    has_filter_s = 'filter(' in sc
    has_filter_t = 'filter(' in tc
    has_set_s = 'set(' in sc or 'OQuotient(' in sc
    has_set_t = 'set(' in tc or 'OQuotient(' in tc
    has_dict_s = 'dict(' in sc
    has_dict_t = 'dict(' in tc

    # One side comp, other side map/filter → high relevance
    if has_map_s and has_filter_t:
        return 0.95
    if has_map_t and has_filter_s:
        return 0.95

    # Set comprehension ↔ set(map(...))
    if has_set_s != has_set_t:
        return 0.90

    # Dict comprehension ↔ dict()
    if has_dict_s != has_dict_t:
        return 0.85

    # Both have map but different forms
    if has_map_s and has_map_t:
        return 0.70

    # Generic comprehension signals
    if has_map_s or has_map_t:
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
    f = OLam(('x',), OOp('inc', (OVar('x'),)))
    p = OLam(('x',), OOp('pos', (OVar('x'),)))

    # ── List comp with filter → map+filter ──
    print("P1: list comp (with filter) → map+filter ...")
    comp_term = OMap(transform=f, collection=xs, filter_pred=p)
    r = apply(comp_term, ctx)
    _assert(any(lbl == 'P1_listcomp_to_map_filter' for _, lbl in r),
            "list comp with filter should rewrite")
    map_filter_result = [t for t, lbl in r if lbl == 'P1_listcomp_to_map_filter'][0]
    _assert(isinstance(map_filter_result, OOp) and map_filter_result.name == 'list',
            "result is list(...)")

    # ── map+filter → list comp ──
    print("P1: map+filter → list comp ...")
    mf_term = OOp('list', (OOp('map', (f, OOp('filter', (p, xs)))),))
    r2 = apply(mf_term, ctx)
    _assert(any(lbl == 'P1_map_filter_to_listcomp' for _, lbl in r2),
            "map+filter should rewrite to comp")
    comp_result = [t for t, lbl in r2 if lbl == 'P1_map_filter_to_listcomp'][0]
    _assert(isinstance(comp_result, OMap), "result is OMap")

    # ── Roundtrip: comp → map+filter → comp ──
    print("P1: roundtrip ...")
    rt = apply(map_filter_result, ctx)
    _assert(any(lbl == 'P1_map_filter_to_listcomp' for _, lbl in rt),
            "roundtrip works")

    # ── List comp without filter → list(map(f, xs)) ──
    print("P1: list comp (no filter) → map ...")
    comp_nofilt = OMap(transform=f, collection=xs)
    r3 = apply(comp_nofilt, ctx)
    _assert(any(lbl == 'P1_listcomp_to_map' for _, lbl in r3),
            "list comp without filter rewrites")

    # ── list(map(f, xs)) → comp ──
    print("P1: list(map(f, xs)) → comp ...")
    lm_term = OOp('list', (OOp('map', (f, xs)),))
    r4 = apply(lm_term, ctx)
    _assert(any(lbl == 'P1_map_to_listcomp' for _, lbl in r4),
            "list(map) → comp")

    # ── Set comp → set(map(f, xs)) ──
    print("P1: set comp → set(map(...)) ...")
    set_comp = OQuotient(OMap(transform=f, collection=xs), 'perm')
    r5 = apply(set_comp, ctx)
    _assert(any(lbl == 'P1_setcomp_to_set_map' for _, lbl in r5),
            "set comp rewrites")

    # ── set(map(f, xs)) → set comp ──
    print("P1: set(map(f, xs)) → set comp ...")
    set_map = OOp('set', (OOp('map', (f, xs)),))
    r6 = apply(set_map, ctx)
    _assert(any(lbl == 'P1_set_map_to_setcomp' for _, lbl in r6),
            "set(map) → set comp")

    # ── Dict comp → dict() ──
    print("P1: dict comp → dict() ...")
    kv_lam = OLam(('item',), OOp('pair', (OVar('k'), OVar('v'))))
    dict_comp = OMap(transform=kv_lam, collection=xs)
    r7 = apply(dict_comp, ctx)
    _assert(any(lbl == 'P1_dictcomp_to_dict' for _, lbl in r7),
            "dict comp rewrites")

    # ── dict(pairs) → dict comp ──
    print("P1: dict(pairs) → dict comp ...")
    dict_call = OOp('dict', (xs,))
    r8 = apply(dict_call, ctx)
    _assert(any(lbl == 'P1_dict_to_dictcomp' for _, lbl in r8),
            "dict() → dict comp")

    # ── Nested comp → product ──
    print("P1: nested comp → product ...")
    ys = OVar('ys')
    inner_f = OLam(('y',), OOp('add', (OVar('x'), OVar('y'))))
    inner_map = OMap(transform=inner_f, collection=ys)
    outer_lam = OLam(('x',), inner_map)
    nested = OMap(transform=outer_lam, collection=xs)
    r9 = apply(nested, ctx)
    _assert(any(lbl == 'P1_nested_comp_to_product' for _, lbl in r9),
            "nested comp rewrites to product")

    # ── Conditional comp ──
    print("P1: conditional comp ...")
    cond_body = OCase(
        OOp('pos', (OVar('x'),)),
        OVar('x'),
        OLit(0),
    )
    cond_lam = OLam(('x',), cond_body)
    cond_comp = OMap(transform=cond_lam, collection=xs)
    r10 = apply(cond_comp, ctx)
    _assert(any(lbl == 'P1_conditional_comp_to_map_ternary' for _, lbl in r10),
            "conditional comp rewrites")

    # ── recognizes() ──
    print("P1: recognizes ...")
    _assert(recognizes(comp_term), "recognizes OMap with filter")
    _assert(recognizes(comp_nofilt), "recognizes OMap without filter")
    _assert(recognizes(set_comp), "recognizes OQuotient(OMap)")
    _assert(recognizes(mf_term), "recognizes list(map(...))")
    _assert(recognizes(set_map), "recognizes set(map(...))")
    _assert(recognizes(dict_call), "recognizes dict()")
    _assert(not recognizes(OOp('sorted', (xs,))), "does not recognise sorted")
    _assert(not recognizes(OLit(42)), "does not recognise literal")

    # ── relevance_score ──
    print("P1: relevance_score ...")
    score = relevance_score(comp_term, mf_term)
    _assert(score > 0.3, f"comp↔map score={score:.2f} > 0.3")
    low = relevance_score(OOp('sorted', (xs,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("P1: apply_inverse ...")
    inv = apply_inverse(mf_term, ctx)
    _assert(len(inv) >= 1, "inverse of map+filter produces comp")
    inv_set = apply_inverse(set_map, ctx)
    _assert(len(inv_set) >= 1, "inverse of set(map) produces set comp")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  P1 comprehension: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
