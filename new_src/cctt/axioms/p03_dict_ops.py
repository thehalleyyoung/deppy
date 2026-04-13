"""P3: Dictionary Operation Equivalences.

d.get(k, default) ↔ d[k] if k in d else default
d.setdefault(k, v) ↔ conditional setitem
d.update(other) ↔ {**d, **other} ↔ d | other
dict(zip(keys, values)) ↔ {k: v for k, v in zip(keys, values)}
d.keys() iteration ↔ for k in d ↔ list(d)
d.items() ↔ [(k, d[k]) for k in d]
collections.defaultdict(list) ↔ {} + setdefault pattern

Mathematical foundation:
  A Python dict is a finite partial map  d: K ⇀ V  in the category of
  sets and partial functions.  The method-based and operator-based
  interfaces compute the same morphisms — they differ only in syntactic
  form.

  The equivalence is witnessed by natural isomorphisms in the presheaf
  category over the site of Python scopes:
    .get(k, v)   ≅  case(k ∈ dom(d), d(k), v)
    .update(o)   ≅  d ∪ o   (right-biased merge of finite maps)
    .items()     ≅  map(λk.(k, d(k)), dom(d))
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

AXIOM_NAME = 'P3_dict_ops'
AXIOM_CATEGORY = 'python_idiom'

SOUNDNESS_PROOF = """
Theorem P3.1 (Dict Get Equivalence):
  For any dict d: K ⇀ V, key k: K, and default v: V,
    d.get(k, v)  ≡  d[k] if k in d else v
  as morphisms K × V → V in Set.

Proof sketch:
  1. d.get(k, v) is defined as:  return d[k] if k in d else v.
  2. The conditional expression evaluates identically by case analysis
     on k ∈ dom(d):
     - k ∈ dom(d):  d.get(k, v) = d[k] = (d[k] if True else v)  ✓
     - k ∉ dom(d):  d.get(k, v) = v = (⊥ if False else v) = v    ✓
  3. This is exactly the universal property of coproduct
     injection in Set.  ∎

Theorem P3.2 (Dict Merge Equivalence):
  For any dicts d, o: K ⇀ V,
    d.update(o)  ≡  {**d, **o}  ≡  d | o   (Python 3.9+)
  as right-biased merge morphisms (K ⇀ V)² → (K ⇀ V).

Proof sketch:
  All three forms compute the right-biased union of finite maps:
    (d ∪ o)(k) = o(k) if k ∈ dom(o) else d(k).
  This is associative and has identity {} — it is the monoid operation
  on finite partial maps with right-bias.  ∎

Theorem P3.3 (Dict Items Equivalence):
  d.items() ≡ [(k, d[k]) for k in d]
  Both produce the graph of d as a finite set of pairs.  ∎
"""

COMPOSES_WITH = ['D13_histogram', 'D14_indexing', 'FOLD_extended']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'get to conditional',
        'before': "d.get(k, default)",
        'after': "d[k] if k in d else default",
        'axiom': 'P3_get_to_conditional',
    },
    {
        'name': 'conditional to get',
        'before': "d[k] if k in d else default",
        'after': "d.get(k, default)",
        'axiom': 'P3_conditional_to_get',
    },
    {
        'name': 'update to merge op',
        'before': "d.update(other)",
        'after': "d | other",
        'axiom': 'P3_update_to_merge',
    },
    {
        'name': 'dict from zip',
        'before': "dict(zip(keys, values))",
        'after': "{k: v for k, v in zip(keys, values)}",
        'axiom': 'P3_dict_zip_to_map',
    },
    {
        'name': 'keys to list',
        'before': "d.keys()",
        'after': "list(d)",
        'axiom': 'P3_keys_to_list',
    },
    {
        'name': 'items to map',
        'before': "d.items()",
        'after': "[(k, d[k]) for k in d]",
        'axiom': 'P3_items_to_map',
    },
    {
        'name': 'defaultdict to setdefault pattern',
        'before': "collections.defaultdict(list)",
        'after': "{} with setdefault calls",
        'axiom': 'P3_defaultdict_to_setdefault',
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
    """Apply P3 dictionary operation equivalences to *term*.

    Returns list of (rewritten_term, axiom_label) pairs.
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── d.get(k, default) → d[k] if k in d else default ──
    if isinstance(term, OOp) and term.name == '.get':
        if len(term.args) == 3:
            d, k, default = term.args
            results.append((
                OCase(
                    OOp('in', (k, d)),
                    OOp('getitem', (d, k)),
                    default,
                ),
                'P3_get_to_conditional',
            ))

    # ── d[k] if k in d else default → d.get(k, default) (inverse) ──
    if isinstance(term, OCase):
        if isinstance(term.test, OOp) and term.test.name == 'in':
            if len(term.test.args) == 2:
                k, d = term.test.args
                if isinstance(term.true_branch, OOp) and term.true_branch.name == 'getitem':
                    if len(term.true_branch.args) == 2:
                        d2, k2 = term.true_branch.args
                        if _terms_equal(d, d2) and _terms_equal(k, k2):
                            results.append((
                                OOp('.get', (d, k, term.false_branch)),
                                'P3_conditional_to_get',
                            ))

    # ── d.setdefault(k, v) → conditional setitem ──
    if isinstance(term, OOp) and term.name == '.setdefault':
        if len(term.args) == 3:
            d, k, v = term.args
            results.append((
                OCase(
                    OOp('in', (k, d)),
                    OOp('getitem', (d, k)),
                    OSeq((OOp('setitem', (d, k, v)), OOp('getitem', (d, k)))),
                ),
                'P3_setdefault_to_conditional',
            ))

    # ── d.update(other) → d | other (merge operator) ──
    if isinstance(term, OOp) and term.name == '.update':
        if len(term.args) == 2:
            d, other = term.args
            results.append((
                OOp('merge', (d, other)),
                'P3_update_to_merge',
            ))
            results.append((
                OOp('bitor', (d, other)),
                'P3_update_to_bitor',
            ))

    # ── d | other → d.update(other) (inverse) ──
    if isinstance(term, OOp) and term.name == 'bitor' and len(term.args) == 2:
        d, other = term.args
        if not _is_counter(d) and not _is_counter(other):
            results.append((
                OOp('.update', (d, other)),
                'P3_bitor_to_update',
            ))

    # ── merge(d, other) → d.update(other) (inverse) ──
    if isinstance(term, OOp) and term.name == 'merge' and len(term.args) == 2:
        d, other = term.args
        results.append((
            OOp('.update', (d, other)),
            'P3_merge_to_update',
        ))

    # ── dict(zip(keys, values)) → OMap over zip ──
    if isinstance(term, OOp) and term.name == 'dict':
        if len(term.args) == 1 and isinstance(term.args[0], OOp):
            if term.args[0].name == 'zip' and len(term.args[0].args) == 2:
                keys, values = term.args[0].args
                results.append((
                    OMap(
                        OLam(('kv',), OSeq((
                            OOp('getitem', (OVar('kv'), OLit(0))),
                            OOp('getitem', (OVar('kv'), OLit(1))),
                        ))),
                        OOp('zip', (keys, values)),
                    ),
                    'P3_dict_zip_to_map',
                ))

    # ── OMap over zip → dict(zip(...)) (inverse) ──
    if isinstance(term, OMap):
        if isinstance(term.collection, OOp) and term.collection.name == 'zip':
            if len(term.collection.args) == 2:
                keys, values = term.collection.args
                results.append((
                    OOp('dict', (OOp('zip', (keys, values)),)),
                    'P3_map_to_dict_zip',
                ))

    # ── d.keys() → list(d) ──
    if isinstance(term, OOp) and term.name == '.keys':
        if len(term.args) == 1:
            d = term.args[0]
            results.append((
                OOp('list', (d,)),
                'P3_keys_to_list',
            ))

    # ── list(d) → d.keys() (inverse, when d is known dict) ──
    if isinstance(term, OOp) and term.name == 'list' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, ODict) or (isinstance(inner, OVar)
                and ctx.param_duck_types.get(inner.name) == 'dict'):
            results.append((
                OOp('.keys', (inner,)),
                'P3_list_to_keys',
            ))

    # ── d.items() → map(λk.(k, d[k]), d) ──
    if isinstance(term, OOp) and term.name == '.items':
        if len(term.args) == 1:
            d = term.args[0]
            results.append((
                OMap(
                    OLam(('k',), OSeq((OVar('k'), OOp('getitem', (d, OVar('k')))))),
                    d,
                ),
                'P3_items_to_map',
            ))

    # ── defaultdict(list) → empty dict (with setdefault semantics) ──
    if isinstance(term, OOp) and term.name == 'defaultdict':
        if len(term.args) == 1:
            if isinstance(term.args[0], OLit) and term.args[0].value in ('list', list):
                results.append((
                    ODict(()),
                    'P3_defaultdict_to_setdefault',
                ))

    return results


def _is_counter(term: OTerm) -> bool:
    """Check if term is a Counter(...) construction."""
    return isinstance(term, OOp) and term.name in ('Counter', 'collections.Counter')


def _terms_equal(a: OTerm, b: OTerm) -> bool:
    """Structural equality check for OTerms via canonical form."""
    return a.canon() == b.canon()


# ═══════════════════════════════════════════════════════════
# Inverse axiom
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply P3 in reverse: expanded forms → method calls.

    Inverse rewrites are already embedded in apply() as bidirectional
    rules; this function filters for only the reverse direction.
    """
    results = apply(term, ctx)
    inverse_labels = {
        'P3_conditional_to_get',
        'P3_bitor_to_update',
        'P3_merge_to_update',
        'P3_map_to_dict_zip',
        'P3_list_to_keys',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if P3 is potentially applicable to *term*."""
    if isinstance(term, OOp):
        if term.name in ('.get', '.setdefault', '.update', '.keys',
                         '.items', 'defaultdict', 'merge'):
            return True
        if term.name == 'dict' and len(term.args) == 1:
            if isinstance(term.args[0], OOp) and term.args[0].name == 'zip':
                return True
        if term.name == 'bitor' and len(term.args) == 2:
            return True
        if term.name == 'list' and len(term.args) == 1:
            return True
    if isinstance(term, OCase):
        if isinstance(term.test, OOp) and term.test.name == 'in':
            return True
    if isinstance(term, OMap):
        if isinstance(term.collection, OOp) and term.collection.name == 'zip':
            return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score how relevant P3 is for bridging *source* → *target*.

    Returns a float in [0, 1].
    """
    sc = source.canon()
    tc = target.canon()

    has_get_s = '.get(' in sc or '.setdefault(' in sc
    has_get_t = '.get(' in tc or '.setdefault(' in tc
    has_cond_s = 'case(' in sc.lower() or 'in(' in sc
    has_cond_t = 'case(' in tc.lower() or 'in(' in tc
    has_update_s = '.update(' in sc or 'merge(' in sc or 'bitor(' in sc
    has_update_t = '.update(' in tc or 'merge(' in tc or 'bitor(' in tc
    has_items_s = '.items(' in sc or '.keys(' in sc
    has_items_t = '.items(' in tc or '.keys(' in tc

    # One side method-based, other side expanded → high relevance
    if has_get_s and has_cond_t:
        return 0.95
    if has_get_t and has_cond_s:
        return 0.95
    if has_update_s != has_update_t:
        return 0.90
    if has_items_s != has_items_t:
        return 0.85

    # dict(zip(...)) patterns
    if 'dict(' in sc and 'zip(' in sc:
        return 0.80
    if 'dict(' in tc and 'zip(' in tc:
        return 0.80

    # Generic dict signals
    if has_get_s or has_get_t or has_update_s or has_update_t:
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
    d = OVar('d')
    k = OVar('k')
    v = OVar('v')
    other = OVar('other')

    # ── get → conditional ──
    print("P3: get → conditional ...")
    get_term = OOp('.get', (d, k, v))
    r = apply(get_term, ctx)
    _assert(len(r) >= 1, "d.get(k, v) should rewrite")
    _assert(r[0][1] == 'P3_get_to_conditional', "axiom label")
    _assert(isinstance(r[0][0], OCase), "result is OCase")

    # ── conditional → get (inverse) ──
    print("P3: conditional → get ...")
    cond_term = OCase(
        OOp('in', (k, d)),
        OOp('getitem', (d, k)),
        v,
    )
    r2 = apply(cond_term, ctx)
    _assert(any(lbl == 'P3_conditional_to_get' for _, lbl in r2), "conditional→get")

    # ── roundtrip get ──
    print("P3: get roundtrip ...")
    rt = apply(r[0][0], ctx)
    _assert(any(lbl == 'P3_conditional_to_get' for _, lbl in rt), "roundtrip works")

    # ── setdefault ──
    print("P3: setdefault ...")
    sd_term = OOp('.setdefault', (d, k, v))
    r3 = apply(sd_term, ctx)
    _assert(len(r3) >= 1, "setdefault rewrites")
    _assert(r3[0][1] == 'P3_setdefault_to_conditional', "setdefault label")

    # ── update → merge ──
    print("P3: update → merge ...")
    upd_term = OOp('.update', (d, other))
    r4 = apply(upd_term, ctx)
    _assert(any(lbl == 'P3_update_to_merge' for _, lbl in r4), "update→merge")
    _assert(any(lbl == 'P3_update_to_bitor' for _, lbl in r4), "update→bitor")

    # ── bitor → update (inverse) ──
    print("P3: bitor → update ...")
    bitor_term = OOp('bitor', (d, other))
    r5 = apply(bitor_term, ctx)
    _assert(any(lbl == 'P3_bitor_to_update' for _, lbl in r5), "bitor→update")

    # ── dict(zip(keys, values)) → map ──
    print("P3: dict(zip) → map ...")
    keys_var = OVar('keys')
    vals_var = OVar('values')
    dz_term = OOp('dict', (OOp('zip', (keys_var, vals_var)),))
    r6 = apply(dz_term, ctx)
    _assert(any(lbl == 'P3_dict_zip_to_map' for _, lbl in r6), "dict(zip)→map")
    _assert(any(isinstance(t, OMap) for t, _ in r6), "result is OMap")

    # ── d.keys() → list(d) ──
    print("P3: keys → list ...")
    keys_term = OOp('.keys', (d,))
    r7 = apply(keys_term, ctx)
    _assert(any(lbl == 'P3_keys_to_list' for _, lbl in r7), "keys→list")

    # ── d.items() → map ──
    print("P3: items → map ...")
    items_term = OOp('.items', (d,))
    r8 = apply(items_term, ctx)
    _assert(any(lbl == 'P3_items_to_map' for _, lbl in r8), "items→map")
    _assert(any(isinstance(t, OMap) for t, _ in r8), "items result is OMap")

    # ── defaultdict(list) → empty dict ──
    print("P3: defaultdict → setdefault ...")
    dd_term = OOp('defaultdict', (OLit('list'),))
    r9 = apply(dd_term, ctx)
    _assert(any(lbl == 'P3_defaultdict_to_setdefault' for _, lbl in r9), "defaultdict→setdefault")

    # ── recognizes() ──
    print("P3: recognizes ...")
    _assert(recognizes(get_term), "recognizes .get")
    _assert(recognizes(upd_term), "recognizes .update")
    _assert(recognizes(items_term), "recognizes .items")
    _assert(recognizes(dz_term), "recognizes dict(zip)")
    _assert(not recognizes(OOp('sorted', (d,))), "does not recognise sorted")

    # ── relevance_score ──
    print("P3: relevance_score ...")
    score = relevance_score(get_term, cond_term)
    _assert(score > 0.8, f"get↔cond score={score:.2f} > 0.8")
    low = relevance_score(OOp('sorted', (d,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("P3: apply_inverse ...")
    inv = apply_inverse(cond_term, ctx)
    _assert(len(inv) >= 1, "inverse of conditional produces .get")

    # ── merge → update (inverse via apply_inverse) ──
    print("P3: merge inverse ...")
    merge_term = OOp('merge', (d, other))
    inv2 = apply_inverse(merge_term, ctx)
    _assert(any(lbl == 'P3_merge_to_update' for _, lbl in inv2), "merge inverse")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  P3 dict_ops: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
