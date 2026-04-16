"""P11: Functional Patterns (Theorem 30.1.1).

functools / operator idioms ↔ explicit lambda / loop equivalents.

Mathematical foundation:
  Each functional combinator (reduce, partial, itemgetter, …) denotes
  a morphism in the category of Python expressions.  The equivalences
  recorded here are witnessed by natural isomorphisms in the presheaf
  category of operational terms: the two sides compute the same
  extensional function, but differ in the carrier object used at
  runtime.

  The key insight is that `functools.reduce` is the universal property
  of a fold over the free monoid (lists), and `operator.*` functions
  are η-expansions of the corresponding binary operations.

Covers:
  • functools.reduce(op, xs, init) ↔ for-loop accumulation (OFold)
  • functools.lru_cache ↔ manual dict memoization
  • operator.itemgetter(k) ↔ lambda x: x[k]
  • operator.attrgetter('a') ↔ lambda x: x.a
  • operator.add ↔ lambda a, b: a + b
  • functools.partial(f, a) ↔ lambda *args: f(a, *args)
  • map(f, xs) ↔ [f(x) for x in xs] (lazy vs eager)
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

AXIOM_NAME = 'P11_functional'
AXIOM_CATEGORY = 'python_idiom'  # §30 — Python-specific functional idioms

SOUNDNESS_PROOF = """
Theorem 30.1.1 (Functional Combinator Equivalences):
  For any binary operator op, initial value init, and iterable xs,
    functools.reduce(op, xs, init) ≡ fold(op, init, xs)
  as morphisms in the presheaf category.

Proof sketch:
  1. reduce(op, xs, init) is defined inductively:
     - reduce(op, [], init) = init
     - reduce(op, [x]+rest, init) = reduce(op, rest, op(init, x))
     This is exactly the universal property of fold.
  2. operator.itemgetter(k) is η-equivalent to λx.x[k] by definition.
  3. operator.attrgetter('a') is η-equivalent to λx.x.a by definition.
  4. operator.add is η-equivalent to λ(a,b).a+b by operator semantics.
  5. functools.partial(f, a) is η-equivalent to λ*args.f(a, *args) by
     the definition of partial application in Python.
  6. map(f, xs) ≅ [f(x) for x in xs] as denotational values; they
     differ only in evaluation strategy (lazy vs eager).  ∎
"""

COMPOSES_WITH = ['D01_fold_unfold', 'D05_fold_universal', 'D06_lazy_eager']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'reduce to fold',
        'before': "functools.reduce(op, xs, init)",
        'after': "fold(op, init, xs)",
        'axiom': 'P11_reduce_to_fold',
    },
    {
        'name': 'fold to reduce',
        'before': "fold(op, init, xs)",
        'after': "functools.reduce(op, xs, init)",
        'axiom': 'P11_fold_to_reduce',
    },
    {
        'name': 'lru_cache to memoized',
        'before': "lru_cache(f)",
        'after': "memoized(f, {})",
        'axiom': 'P11_lru_cache_to_memoized',
    },
    {
        'name': 'itemgetter to lambda',
        'before': "operator.itemgetter(k)",
        'after': "lambda x: x[k]",
        'axiom': 'P11_itemgetter_to_lambda',
    },
    {
        'name': 'attrgetter to lambda',
        'before': "operator.attrgetter('a')",
        'after': "lambda x: x.a",
        'axiom': 'P11_attrgetter_to_lambda',
    },
    {
        'name': 'operator.add to lambda',
        'before': "operator.add",
        'after': "lambda a, b: a + b",
        'axiom': 'P11_operator_add_to_lambda',
    },
    {
        'name': 'partial to lambda',
        'before': "functools.partial(f, a)",
        'after': "lambda *args: f(a, *args)",
        'axiom': 'P11_partial_to_lambda',
    },
    {
        'name': 'map to OMap',
        'before': "map(f, xs)",
        'after': "OMap(f, xs)",
        'axiom': 'P11_map_to_omap',
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
    """Apply P11 functional-pattern equivalences to *term*.

    Returns list of (rewritten_term, axiom_label) pairs.
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── functools.reduce(op, xs, init) → OFold(op, init, xs) ──
    if isinstance(term, OOp) and term.name in ('reduce', 'functools.reduce'):
        if len(term.args) == 3:
            op, xs, init = term.args
            results.append((
                OFold(op.name if isinstance(op, OOp) else str(op), init, xs),
                'P11_reduce_to_fold',
            ))

    # ── OFold(op, init, xs) → functools.reduce(op, xs, init) ──
    if isinstance(term, OFold):
        results.append((
            OOp('functools.reduce', (OOp(term.op_name, ()), term.collection, term.init)),
            'P11_fold_to_reduce',
        ))

    # ── lru_cache(f) → memoized(f, ODict(())) ──
    if isinstance(term, OOp) and term.name in ('lru_cache', 'functools.lru_cache'):
        if len(term.args) == 1:
            f = term.args[0]
            results.append((
                OOp('memoized', (f, ODict(()))),
                'P11_lru_cache_to_memoized',
            ))

    # ── memoized(f, ODict(())) → lru_cache(f) ──
    if isinstance(term, OOp) and term.name == 'memoized':
        if len(term.args) == 2 and isinstance(term.args[1], ODict):
            f = term.args[0]
            results.append((
                OOp('lru_cache', (f,)),
                'P11_memoized_to_lru_cache',
            ))

    # ── operator.itemgetter(k) → λx. x[k] ──
    if isinstance(term, OOp) and term.name == 'operator.itemgetter':
        if len(term.args) == 1:
            k = term.args[0]
            results.append((
                OLam(('x',), OOp('getitem', (OVar('x'), k))),
                'P11_itemgetter_to_lambda',
            ))

    # ── λx. x[k] → operator.itemgetter(k) ──
    if isinstance(term, OLam) and len(term.params) == 1:
        body = term.body
        if (isinstance(body, OOp) and body.name == 'getitem'
                and len(body.args) == 2
                and isinstance(body.args[0], OVar)
                and body.args[0].name == term.params[0]):
            k = body.args[1]
            results.append((
                OOp('operator.itemgetter', (k,)),
                'P11_lambda_to_itemgetter',
            ))

    # ── operator.attrgetter('a') → λx. x.a ──
    if isinstance(term, OOp) and term.name == 'operator.attrgetter':
        if len(term.args) == 1 and isinstance(term.args[0], OLit):
            attr = term.args[0].value
            results.append((
                OLam(('x',), OOp(f'.{attr}', (OVar('x'),))),
                'P11_attrgetter_to_lambda',
            ))

    # ── λx. x.a → operator.attrgetter('a') ──
    if isinstance(term, OLam) and len(term.params) == 1:
        body = term.body
        if (isinstance(body, OOp) and body.name.startswith('.')
                and len(body.args) == 1
                and isinstance(body.args[0], OVar)
                and body.args[0].name == term.params[0]):
            attr = body.name[1:]  # strip leading '.'
            results.append((
                OOp('operator.attrgetter', (OLit(attr),)),
                'P11_lambda_to_attrgetter',
            ))

    # ── operator.add → λ(a, b). a + b ──
    if isinstance(term, OOp) and term.name == 'operator.add' and len(term.args) == 0:
        results.append((
            OLam(('a', 'b'), OOp('add', (OVar('a'), OVar('b')))),
            'P11_operator_add_to_lambda',
        ))

    # ── λ(a, b). a + b → operator.add ──
    if isinstance(term, OLam) and len(term.params) == 2:
        body = term.body
        if (isinstance(body, OOp) and body.name == 'add'
                and len(body.args) == 2
                and isinstance(body.args[0], OVar) and body.args[0].name == term.params[0]
                and isinstance(body.args[1], OVar) and body.args[1].name == term.params[1]):
            results.append((
                OOp('operator.add', ()),
                'P11_lambda_to_operator_add',
            ))

    # ── functools.partial(f, a) → λ(*args). f(a, *args) ──
    if isinstance(term, OOp) and term.name in ('partial', 'functools.partial'):
        if len(term.args) == 2:
            f, a = term.args
            results.append((
                OLam(('args',), OOp('apply_star', (f, OOp('concat', (OSeq((a,)), OVar('args')))))),
                'P11_partial_to_lambda',
            ))

    # ── λ(*args). f(a, *args) → functools.partial(f, a) ──
    if isinstance(term, OLam) and len(term.params) == 1:
        body = term.body
        if (isinstance(body, OOp) and body.name == 'apply_star'
                and len(body.args) == 2):
            f = body.args[0]
            concat_part = body.args[1]
            if (isinstance(concat_part, OOp) and concat_part.name == 'concat'
                    and len(concat_part.args) == 2
                    and isinstance(concat_part.args[0], OSeq)
                    and len(concat_part.args[0].elements) == 1
                    and isinstance(concat_part.args[1], OVar)
                    and concat_part.args[1].name == term.params[0]):
                a = concat_part.args[0].elements[0]
                results.append((
                    OOp('functools.partial', (f, a)),
                    'P11_lambda_to_partial',
                ))

    # ── map(f, xs) → OMap(f, xs) ──
    if isinstance(term, OOp) and term.name == 'map':
        if len(term.args) == 2:
            f, xs = term.args
            results.append((
                OMap(f, xs),
                'P11_map_to_omap',
            ))

    # ── OMap(f, xs) → map(f, xs) ──
    # Only when no filter — filter_map ≠ map
    if isinstance(term, OMap) and term.filter_pred is None:
        results.append((
            OOp('map', (term.transform, term.collection)),
            'P11_omap_to_map',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse axiom
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply P11 in reverse: canonical → combinator form.

    Inverse rewrites are already embedded in apply() as bidirectional
    rules; this function filters for only the reverse direction.
    """
    results = apply(term, ctx)
    inverse_labels = {
        'P11_fold_to_reduce',
        'P11_memoized_to_lru_cache',
        'P11_lambda_to_itemgetter',
        'P11_lambda_to_attrgetter',
        'P11_lambda_to_operator_add',
        'P11_lambda_to_partial',
        'P11_omap_to_map',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if P11 is potentially applicable to *term*."""
    if isinstance(term, OOp):
        if term.name in ('reduce', 'functools.reduce',
                         'lru_cache', 'functools.lru_cache',
                         'memoized',
                         'operator.itemgetter', 'operator.attrgetter',
                         'operator.add',
                         'partial', 'functools.partial',
                         'map'):
            return True
    if isinstance(term, OFold):
        return True
    if isinstance(term, OMap):
        return True
    if isinstance(term, OLam):
        # Check for recognisable lambda patterns
        body = term.body
        if isinstance(body, OOp):
            if body.name == 'getitem' and len(term.params) == 1:
                return True
            if body.name.startswith('.') and len(term.params) == 1:
                return True
            if body.name == 'add' and len(term.params) == 2:
                return True
            if body.name == 'apply_star' and len(term.params) == 1:
                return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score how relevant P11 is for bridging *source* → *target*.

    Returns a float in [0, 1].
    """
    sc = source.canon()
    tc = target.canon()

    has_reduce_s = 'reduce(' in sc or 'functools.reduce(' in sc
    has_reduce_t = 'reduce(' in tc or 'functools.reduce(' in tc
    has_fold_s = 'fold[' in sc
    has_fold_t = 'fold[' in tc
    has_lru_s = 'lru_cache(' in sc
    has_lru_t = 'lru_cache(' in tc
    has_memo_s = 'memoized(' in sc
    has_memo_t = 'memoized(' in tc
    has_op_s = 'operator.' in sc
    has_op_t = 'operator.' in tc
    has_map_s = 'map(' in sc
    has_map_t = 'map(' in tc

    # reduce ↔ fold — high relevance
    if (has_reduce_s and has_fold_t) or (has_reduce_t and has_fold_s):
        return 0.95

    # lru_cache ↔ memoized
    if (has_lru_s and has_memo_t) or (has_lru_t and has_memo_s):
        return 0.90

    # operator.* ↔ lambda
    if has_op_s != has_op_t:
        return 0.85

    # map ↔ comprehension
    if has_map_s != has_map_t:
        return 0.80

    # partial presence
    if 'partial(' in sc or 'partial(' in tc:
        return 0.75

    # Generic functional signals
    if has_reduce_s or has_reduce_t or has_fold_s or has_fold_t:
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
    k = OVar('k')
    a = OVar('a')
    b = OVar('b')

    # ── reduce → fold ──
    print("P11: reduce → fold ...")
    reduce_term = OOp('functools.reduce', (OOp('add', ()), xs, OLit(0)))
    r = apply(reduce_term, ctx)
    _assert(len(r) >= 1, "reduce(add, xs, 0) should rewrite")
    _assert(r[0][1] == 'P11_reduce_to_fold', "axiom label")
    _assert(isinstance(r[0][0], OFold), "result is OFold")

    # ── fold → reduce ──
    print("P11: fold → reduce ...")
    fold_term = OFold('add', OLit(0), xs)
    r2 = apply(fold_term, ctx)
    _assert(any(lbl == 'P11_fold_to_reduce' for _, lbl in r2), "fold→reduce")

    # ── reduce roundtrip ──
    print("P11: reduce roundtrip ...")
    rt = apply(r[0][0], ctx)
    _assert(any(lbl == 'P11_fold_to_reduce' for _, lbl in rt), "roundtrip works")

    # ── lru_cache → memoized ──
    print("P11: lru_cache → memoized ...")
    lru_term = OOp('lru_cache', (f,))
    r3 = apply(lru_term, ctx)
    _assert(len(r3) >= 1, "lru_cache(f) should rewrite")
    _assert(r3[0][1] == 'P11_lru_cache_to_memoized', "lru_cache label")

    # ── memoized → lru_cache ──
    print("P11: memoized → lru_cache ...")
    memo_term = OOp('memoized', (f, ODict(())))
    r4 = apply(memo_term, ctx)
    _assert(any(lbl == 'P11_memoized_to_lru_cache' for _, lbl in r4), "memo→lru_cache")

    # ── itemgetter → lambda ──
    print("P11: itemgetter → lambda ...")
    ig_term = OOp('operator.itemgetter', (k,))
    r5 = apply(ig_term, ctx)
    _assert(len(r5) >= 1, "itemgetter should rewrite")
    _assert(r5[0][1] == 'P11_itemgetter_to_lambda', "itemgetter label")
    _assert(isinstance(r5[0][0], OLam), "result is OLam")

    # ── lambda → itemgetter ──
    print("P11: lambda → itemgetter ...")
    lam_ig = OLam(('x',), OOp('getitem', (OVar('x'), k)))
    r6 = apply(lam_ig, ctx)
    _assert(any(lbl == 'P11_lambda_to_itemgetter' for _, lbl in r6), "lambda→itemgetter")

    # ── attrgetter → lambda ──
    print("P11: attrgetter → lambda ...")
    ag_term = OOp('operator.attrgetter', (OLit('name'),))
    r7 = apply(ag_term, ctx)
    _assert(len(r7) >= 1, "attrgetter should rewrite")
    _assert(r7[0][1] == 'P11_attrgetter_to_lambda', "attrgetter label")

    # ── lambda → attrgetter ──
    print("P11: lambda → attrgetter ...")
    lam_ag = OLam(('x',), OOp('.name', (OVar('x'),)))
    r8 = apply(lam_ag, ctx)
    _assert(any(lbl == 'P11_lambda_to_attrgetter' for _, lbl in r8), "lambda→attrgetter")

    # ── operator.add → lambda ──
    print("P11: operator.add → lambda ...")
    op_add_term = OOp('operator.add', ())
    r9 = apply(op_add_term, ctx)
    _assert(len(r9) >= 1, "operator.add should rewrite")
    _assert(r9[0][1] == 'P11_operator_add_to_lambda', "operator.add label")

    # ── lambda → operator.add ──
    print("P11: lambda → operator.add ...")
    lam_add = OLam(('a', 'b'), OOp('add', (OVar('a'), OVar('b'))))
    r10 = apply(lam_add, ctx)
    _assert(any(lbl == 'P11_lambda_to_operator_add' for _, lbl in r10), "lambda→operator.add")

    # ── partial → lambda ──
    print("P11: partial → lambda ...")
    partial_term = OOp('functools.partial', (f, a))
    r11 = apply(partial_term, ctx)
    _assert(len(r11) >= 1, "partial should rewrite")
    _assert(r11[0][1] == 'P11_partial_to_lambda', "partial label")

    # ── lambda → partial ──
    print("P11: lambda → partial ...")
    lam_partial = OLam(('args',), OOp('apply_star', (f, OOp('concat', (OSeq((a,)), OVar('args'))))))
    r12 = apply(lam_partial, ctx)
    _assert(any(lbl == 'P11_lambda_to_partial' for _, lbl in r12), "lambda→partial")

    # ── map → OMap ──
    print("P11: map → OMap ...")
    map_term = OOp('map', (f, xs))
    r13 = apply(map_term, ctx)
    _assert(len(r13) >= 1, "map should rewrite")
    _assert(r13[0][1] == 'P11_map_to_omap', "map label")
    _assert(isinstance(r13[0][0], OMap), "result is OMap")

    # ── OMap → map ──
    print("P11: OMap → map ...")
    omap_term = OMap(f, xs)
    r14 = apply(omap_term, ctx)
    _assert(any(lbl == 'P11_omap_to_map' for _, lbl in r14), "OMap→map")

    # ── recognizes() ──
    print("P11: recognizes ...")
    _assert(recognizes(reduce_term), "recognizes reduce")
    _assert(recognizes(fold_term), "recognizes fold")
    _assert(recognizes(lru_term), "recognizes lru_cache")
    _assert(recognizes(ig_term), "recognizes itemgetter")
    _assert(recognizes(ag_term), "recognizes attrgetter")
    _assert(recognizes(map_term), "recognizes map")
    _assert(recognizes(omap_term), "recognizes OMap")
    _assert(recognizes(lam_ig), "recognizes lambda getitem")
    _assert(not recognizes(OOp('sorted', (xs,))), "does not recognise sorted")

    # ── relevance_score ──
    print("P11: relevance_score ...")
    score = relevance_score(reduce_term, fold_term)
    _assert(score > 0.8, f"reduce↔fold score={score:.2f} > 0.8")
    low = relevance_score(OOp('sorted', (xs,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("P11: apply_inverse ...")
    inv = apply_inverse(fold_term, ctx)
    _assert(len(inv) >= 1, "inverse of fold produces reduce")
    inv2 = apply_inverse(lam_ig, ctx)
    _assert(any(lbl == 'P11_lambda_to_itemgetter' for _, lbl in inv2), "inverse lambda→itemgetter")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  P11 functional: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
