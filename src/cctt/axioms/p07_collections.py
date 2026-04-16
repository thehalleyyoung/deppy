"""P7: Collections Module Equivalences (Theorem 28.3.1).

collections.Counter ↔ dict comprehension counting,
collections.OrderedDict ↔ dict (Python 3.7+),
collections.deque(maxlen=n) ↔ list slicing,
collections.namedtuple ↔ class with __init__,
collections.ChainMap ↔ dict merge,
collections.defaultdict(int) ↔ dict.get with 0 default.

Mathematical foundation:
  Each collections type is an object in the category of Python container
  functors.  The equivalences are natural isomorphisms between these
  functors when restricted to the sub-category of finite sequences /
  finite mappings.

  Counter(xs) is the image of xs under the free commutative-monoid
  functor into ℕ^X, identical to the dict-comprehension counting map.

  OrderedDict and dict are the same object in the presheaf category
  for Python ≥ 3.7 (insertion-order preservation is a property of the
  representation, not the morphism).

  ChainMap(d₁, d₂) computes the coproduct with left-priority in the
  category of partial maps, equivalent to {**d₂, **d₁}.

Covers:
  • Counter(xs) ↔ {x: xs.count(x) for x in set(xs)}
  • OrderedDict(args) ↔ dict(args)
  • deque(xs, maxlen=n) ↔ list(xs)[-n:]
  • namedtuple('T', 'a b') ↔ named record abstract
  • ChainMap(d1, d2) ↔ {**d2, **d1}
  • defaultdict(int) ↔ dict with get-0 pattern
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

AXIOM_NAME = 'P7_collections'
AXIOM_CATEGORY = 'python_idiom'  # §28 — Python-specific idioms

SOUNDNESS_PROOF = """
Theorem 28.3.1 (Collections Module Equivalences):
  For any iterable xs: X*,

  (a) Counter(xs) ≡ {x: xs.count(x) for x in set(xs)}
      Both compute the frequency morphism Free(X) → ℕ^X.

  (b) OrderedDict(pairs) ≡ dict(pairs)  (Python ≥ 3.7)
      dict preserves insertion order by language spec (PEP 468 / CPython 3.6+,
      language guarantee 3.7+).

  (c) deque(xs, maxlen=n) ≡ list(xs)[-n:]
      deque with maxlen keeps the last n elements; list slicing [-n:] is
      identical for finite sequences.

  (d) namedtuple('T', 'a b') ≡ record type with named fields
      Isomorphism of product types in the category of Python objects.

  (e) ChainMap(d₁, d₂) ≡ {**d₂, **d₁}  (for read-only lookup)
      Left-priority coproduct of partial maps.

  (f) defaultdict(int) ≡ dict with .get(k, 0) pattern
      Both realise the same total map X → ℕ with default 0.  ∎
"""

COMPOSES_WITH = ['D13_histogram', 'D14_indexing', 'D12_map_construct']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'Counter to dict comprehension',
        'before': "Counter(xs)",
        'after': "{x: xs.count(x) for x in set(xs)}",
        'axiom': 'P7_counter_to_dictcomp',
    },
    {
        'name': 'OrderedDict to dict',
        'before': "OrderedDict(pairs)",
        'after': "dict(pairs)",
        'axiom': 'P7_ordereddict_to_dict',
    },
    {
        'name': 'deque maxlen to slice',
        'before': "deque(xs, maxlen=n)",
        'after': "list(xs)[-n:]",
        'axiom': 'P7_deque_to_slice',
    },
    {
        'name': 'namedtuple to record',
        'before': "namedtuple('Point', 'x y')",
        'after': "named_record('Point', ('x', 'y'))",
        'axiom': 'P7_namedtuple_to_record',
    },
    {
        'name': 'ChainMap to merge',
        'before': "ChainMap(d1, d2)",
        'after': "{**d2, **d1}",
        'axiom': 'P7_chainmap_to_merge',
    },
    {
        'name': 'defaultdict(int) to get-0',
        'before': "defaultdict(int)",
        'after': "dict with get(k, 0)",
        'axiom': 'P7_defaultdict_to_get0',
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
    """Apply P7 collections equivalences to *term*.

    Returns list of (rewritten_term, axiom_label) pairs.
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── Counter(xs) → dict comprehension counting ──
    if isinstance(term, OOp) and term.name in ('Counter', 'collections.Counter'):
        if len(term.args) == 1:
            xs = term.args[0]
            # {x: xs.count(x) for x in set(xs)}
            x_var = OVar('_x')
            count_expr = OOp('count', (xs, x_var))
            pair_lam = OLam(('_x',), OOp('pair', (x_var, count_expr)))
            results.append((
                OMap(pair_lam, OOp('set', (xs,))),
                'P7_counter_to_dictcomp',
            ))

    # ── dict-comprehension counting → Counter(xs) ──
    if isinstance(term, OMap) and isinstance(term.transform, OLam):
        body = term.transform.body
        if isinstance(body, OOp) and body.name == 'pair' and len(body.args) == 2:
            _, count_part = body.args
            if isinstance(count_part, OOp) and count_part.name == 'count':
                if isinstance(term.collection, OOp) and term.collection.name == 'set':
                    if len(term.collection.args) == 1:
                        results.append((
                            OOp('Counter', (term.collection.args[0],)),
                            'P7_dictcomp_to_counter',
                        ))

    # ── OrderedDict(args) → dict(args) ──
    if isinstance(term, OOp) and term.name in ('OrderedDict', 'collections.OrderedDict'):
        results.append((
            OOp('dict', term.args),
            'P7_ordereddict_to_dict',
        ))

    # ── dict(args) → OrderedDict(args) (reverse) ──
    if isinstance(term, OOp) and term.name == 'dict':
        results.append((
            OOp('OrderedDict', term.args),
            'P7_dict_to_ordereddict',
        ))

    # ── deque(xs, maxlen=n) → list(xs)[-n:] ──
    if isinstance(term, OOp) and term.name in ('deque', 'collections.deque'):
        if len(term.args) == 2:
            xs, maxlen = term.args
            neg_n = OOp('neg', (maxlen,))
            results.append((
                OOp('slice', (OOp('list', (xs,)), neg_n, OLit(None))),
                'P7_deque_to_slice',
            ))

    # ── list slice with negative start → deque(maxlen) ──
    if isinstance(term, OOp) and term.name == 'slice':
        if len(term.args) == 3:
            base, start, end = term.args
            if isinstance(base, OOp) and base.name == 'list' and len(base.args) == 1:
                if isinstance(start, OOp) and start.name == 'neg' and len(start.args) == 1:
                    if isinstance(end, OLit) and end.value is None:
                        results.append((
                            OOp('deque', (base.args[0], start.args[0])),
                            'P7_slice_to_deque',
                        ))

    # ── namedtuple('T', 'a b') → named record abstract ──
    if isinstance(term, OOp) and term.name in ('namedtuple', 'collections.namedtuple'):
        if len(term.args) >= 2:
            type_name = term.args[0]
            field_spec = term.args[1]
            results.append((
                OAbstract('named_record', (type_name, field_spec)),
                'P7_namedtuple_to_record',
            ))

    # ── named record abstract → namedtuple ──
    if isinstance(term, OAbstract) and term.spec == 'named_record':
        if len(term.inputs) == 2:
            results.append((
                OOp('namedtuple', tuple(term.inputs)),
                'P7_record_to_namedtuple',
            ))

    # ── ChainMap(d1, d2) → merge({**d2, **d1}) ──
    if isinstance(term, OOp) and term.name in ('ChainMap', 'collections.ChainMap'):
        if len(term.args) == 2:
            d1, d2 = term.args
            results.append((
                OOp('merge', (d2, d1)),
                'P7_chainmap_to_merge',
            ))

    # ── merge(d2, d1) → ChainMap(d1, d2) ──
    if isinstance(term, OOp) and term.name == 'merge':
        if len(term.args) == 2:
            d2, d1 = term.args
            results.append((
                OOp('ChainMap', (d1, d2)),
                'P7_merge_to_chainmap',
            ))

    # ── defaultdict(int) → dict with get-0 pattern ──
    if isinstance(term, OOp) and term.name in ('defaultdict', 'collections.defaultdict'):
        if len(term.args) == 1:
            factory = term.args[0]
            if isinstance(factory, OLit) and factory.value in (0, 'int'):
                results.append((
                    OAbstract('dict_get_default', (OLit(0),)),
                    'P7_defaultdict_to_get0',
                ))

    # ── dict with get-0 pattern → defaultdict(int) ──
    if isinstance(term, OAbstract) and term.spec == 'dict_get_default':
        if len(term.inputs) == 1 and isinstance(term.inputs[0], OLit):
            if term.inputs[0].value == 0:
                results.append((
                    OOp('defaultdict', (OLit(0),)),
                    'P7_get0_to_defaultdict',
                ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse axiom
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply P7 in reverse direction.

    Inverse rewrites are already embedded in apply() as bidirectional
    rules; this function filters for only the reverse direction.
    """
    results = apply(term, ctx)
    inverse_labels = {
        'P7_dictcomp_to_counter',
        'P7_dict_to_ordereddict',
        'P7_slice_to_deque',
        'P7_record_to_namedtuple',
        'P7_merge_to_chainmap',
        'P7_get0_to_defaultdict',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if P7 is potentially applicable to *term*."""
    if isinstance(term, OOp):
        if term.name in (
            'Counter', 'collections.Counter',
            'OrderedDict', 'collections.OrderedDict',
            'deque', 'collections.deque',
            'namedtuple', 'collections.namedtuple',
            'ChainMap', 'collections.ChainMap',
            'defaultdict', 'collections.defaultdict',
            'dict', 'merge',
        ):
            return True
        if term.name == 'slice' and len(term.args) == 3:
            return _is_list_neg_slice(term)
    if isinstance(term, OAbstract):
        if term.spec in ('named_record', 'dict_get_default'):
            return True
    if isinstance(term, OMap) and isinstance(term.transform, OLam):
        body = term.transform.body
        if isinstance(body, OOp) and body.name == 'pair':
            return True
    return False


def _is_list_neg_slice(term: OTerm) -> bool:
    """Check for list(xs)[-n:] pattern."""
    if not isinstance(term, OOp) or term.name != 'slice' or len(term.args) != 3:
        return False
    base, start, end = term.args
    if not (isinstance(base, OOp) and base.name == 'list'):
        return False
    if isinstance(start, OOp) and start.name == 'neg':
        if isinstance(end, OLit) and end.value is None:
            return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score how relevant P7 is for bridging *source* → *target*.

    Returns a float in [0, 1].
    """
    sc = source.canon()
    tc = target.canon()

    collections_kws = (
        'Counter(', 'OrderedDict(', 'deque(', 'namedtuple(',
        'ChainMap(', 'defaultdict(',
    )
    has_coll_s = any(kw in sc for kw in collections_kws)
    has_coll_t = any(kw in tc for kw in collections_kws)

    builtin_kws = ('dict(', 'list(', 'merge(', 'slice(', 'named_record(')
    has_builtin_s = any(kw in sc for kw in builtin_kws)
    has_builtin_t = any(kw in tc for kw in builtin_kws)

    # One side collections, other side builtins → high relevance
    if has_coll_s and has_builtin_t:
        return 0.95
    if has_coll_t and has_builtin_s:
        return 0.95

    # Both have collections references → moderate (normalisation)
    if has_coll_s and has_coll_t:
        return 0.70

    # Only one side mentions collections at all
    if has_coll_s or has_coll_t:
        return 0.45

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

    # ── Counter → dict comprehension ──
    print("P7: Counter → dict comprehension ...")
    counter_term = OOp('Counter', (xs,))
    r = apply(counter_term, ctx)
    _assert(len(r) >= 1, "Counter(xs) should rewrite")
    _assert(r[0][1] == 'P7_counter_to_dictcomp', "axiom label")
    _assert(isinstance(r[0][0], OMap), "result is OMap")

    # ── dict comprehension → Counter (roundtrip) ──
    print("P7: dict comprehension → Counter ...")
    r2 = apply(r[0][0], ctx)
    _assert(any(lbl == 'P7_dictcomp_to_counter' for _, lbl in r2), "dictcomp→Counter")

    # ── OrderedDict → dict ──
    print("P7: OrderedDict → dict ...")
    od_term = OOp('OrderedDict', (xs,))
    r3 = apply(od_term, ctx)
    _assert(any(lbl == 'P7_ordereddict_to_dict' for _, lbl in r3), "OrderedDict→dict")
    _assert(any(isinstance(t, OOp) and t.name == 'dict' for t, _ in r3), "result is dict")

    # ── dict → OrderedDict (reverse) ──
    print("P7: dict → OrderedDict ...")
    dict_term = OOp('dict', (xs,))
    r4 = apply(dict_term, ctx)
    _assert(any(lbl == 'P7_dict_to_ordereddict' for _, lbl in r4), "dict→OrderedDict")

    # ── deque(xs, maxlen=n) → slice ──
    print("P7: deque → slice ...")
    n = OVar('n')
    deque_term = OOp('deque', (xs, n))
    r5 = apply(deque_term, ctx)
    _assert(any(lbl == 'P7_deque_to_slice' for _, lbl in r5), "deque→slice")
    _assert(any(isinstance(t, OOp) and t.name == 'slice' for t, _ in r5), "result is slice")

    # ── slice → deque (reverse) ──
    print("P7: slice → deque ...")
    slice_term = OOp('slice', (OOp('list', (xs,)), OOp('neg', (n,)), OLit(None)))
    r6 = apply(slice_term, ctx)
    _assert(any(lbl == 'P7_slice_to_deque' for _, lbl in r6), "slice→deque")

    # ── namedtuple → record ──
    print("P7: namedtuple → record ...")
    nt_term = OOp('namedtuple', (OLit('Point'), OLit('x y')))
    r7 = apply(nt_term, ctx)
    _assert(any(lbl == 'P7_namedtuple_to_record' for _, lbl in r7), "namedtuple→record")
    _assert(any(isinstance(t, OAbstract) for t, _ in r7), "result is OAbstract")

    # ── record → namedtuple (reverse) ──
    print("P7: record → namedtuple ...")
    rec_term = OAbstract('named_record', (OLit('Point'), OLit('x y')))
    r8 = apply(rec_term, ctx)
    _assert(any(lbl == 'P7_record_to_namedtuple' for _, lbl in r8), "record→namedtuple")

    # ── ChainMap → merge ──
    print("P7: ChainMap → merge ...")
    d1, d2 = OVar('d1'), OVar('d2')
    cm_term = OOp('ChainMap', (d1, d2))
    r9 = apply(cm_term, ctx)
    _assert(any(lbl == 'P7_chainmap_to_merge' for _, lbl in r9), "ChainMap→merge")

    # ── merge → ChainMap (reverse) ──
    print("P7: merge → ChainMap ...")
    merge_term = OOp('merge', (d2, d1))
    r10 = apply(merge_term, ctx)
    _assert(any(lbl == 'P7_merge_to_chainmap' for _, lbl in r10), "merge→ChainMap")

    # ── defaultdict(int) → get-0 ──
    print("P7: defaultdict(int) → get-0 ...")
    dd_term = OOp('defaultdict', (OLit(0),))
    r11 = apply(dd_term, ctx)
    _assert(any(lbl == 'P7_defaultdict_to_get0' for _, lbl in r11), "defaultdict→get0")

    # ── get-0 → defaultdict(int) (reverse) ──
    print("P7: get-0 → defaultdict(int) ...")
    get0_term = OAbstract('dict_get_default', (OLit(0),))
    r12 = apply(get0_term, ctx)
    _assert(any(lbl == 'P7_get0_to_defaultdict' for _, lbl in r12), "get0→defaultdict")

    # ── recognizes() ──
    print("P7: recognizes ...")
    _assert(recognizes(counter_term), "recognizes Counter")
    _assert(recognizes(od_term), "recognizes OrderedDict")
    _assert(recognizes(deque_term), "recognizes deque")
    _assert(recognizes(nt_term), "recognizes namedtuple")
    _assert(recognizes(cm_term), "recognizes ChainMap")
    _assert(recognizes(dd_term), "recognizes defaultdict")
    _assert(recognizes(rec_term), "recognizes named_record")
    _assert(not recognizes(OOp('sorted', (xs,))), "does not recognise sorted")

    # ── relevance_score ──
    print("P7: relevance_score ...")
    score = relevance_score(counter_term, dict_term)
    _assert(score > 0.8, f"Counter↔dict score={score:.2f} > 0.8")
    low = relevance_score(OOp('sorted', (xs,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("P7: apply_inverse ...")
    inv = apply_inverse(dict_term, ctx)
    _assert(len(inv) >= 1, "inverse of dict produces OrderedDict")
    inv_labels = {lbl for _, lbl in inv}
    _assert('P7_dict_to_ordereddict' in inv_labels, "inverse label correct")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  P7 collections: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
