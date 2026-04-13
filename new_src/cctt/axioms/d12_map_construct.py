"""D12 Axiom: Map Construction Equivalences.

Establishes equivalence between different ways to construct
dictionaries/maps in Python: dict comprehension, explicit loop
with assignment, dict.fromkeys, defaultdict patterns, setdefault
loops, and Counter-like accumulations.

Mathematical basis: A dictionary is a finite partial function
    d : K → V
The construction of d from a sequence of key-value pairs
(k₁,v₁), ..., (kₙ,vₙ) is a fold:
    d = fold[dict_set](∅, [(k₁,v₁), ..., (kₙ,vₙ)])

Different Python idioms for constructing the same mapping:
  - {k: f(k) for k in keys}
  - d = {}; for k in keys: d[k] = f(k)
  - dict.fromkeys(keys, default)
  - defaultdict(factory, items)
  - d = {}; for k in items: d.setdefault(k, []).append(v)

All produce the same finite partial function, hence the same
ODict or OFold in the denotation.  The axiom canonicalizes
these to a single representation.

For maps that accumulate (group-by pattern, multi-dict), the
construction is:
    fold[dict_append](∅, [(k₁,v₁), ...])
which is equivalent to defaultdict(list) + append loop.

(§21.5, Definition 21.5.2)
"""
from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)
from cctt.path_search import FiberCtx

# ═══════════════════════════════════════════════════════════
# Constants
# ═══════════════════════════════════════════════════════════

AXIOM_NAME = "D12_map_construct"
AXIOM_CATEGORY = "data_structure"

COMPOSES_WITH = ["D4_comp_fusion", "D5_fold_universal", "D11_adt", "D13_histogram"]
REQUIRES: List[str] = []

# Dict construction operation names
_DICT_SET_OPS = frozenset({
    'dict_set', 'setitem', '__setitem__',
    'dict_update', 'update',
})

_DICT_ACCUM_OPS = frozenset({
    'dict_append', 'setdefault_append',
    'dict_incr', 'setdefault_add',
    'dict_extend',
})

_FROMKEYS_OPS = frozenset({
    'fromkeys', 'dict.fromkeys',
})

_DEFAULTDICT_OPS = frozenset({
    'defaultdict', 'collections.defaultdict',
})

SOUNDNESS_PROOF = r"""
Theorem (D12 Map Construction Equivalence).

Let pairs = [(k₁,v₁), ..., (kₙ,vₙ)] be a sequence of key-value pairs.

Construction 1 (comprehension):
    d₁ = {kᵢ : f(kᵢ) for kᵢ in keys}
    OTerm: ODict(map(λk. (k, f(k)), keys))

Construction 2 (loop):
    d₂ = {}; for k in keys: d₂[k] = f(k)
    OTerm: fold[dict_set](ODict(()), map(λk. (k, f(k)), keys))

Construction 3 (fromkeys):
    d₃ = dict.fromkeys(keys, default)
    OTerm: OOp('fromkeys', (keys, default))

Claim: d₁ ≡ d₂ ≡ d₃ (when f(k) = default for all k).

Proof:
  1. d₁ and d₂ both compute fold[dict_set](∅, [(k,f(k)) for k in keys]).
     The comprehension is syntactic sugar for the fold (by Python semantics).
  2. When f(k) = default for all k, d₁ = d₃ by definition of fromkeys.
  3. The fold is a left fold with dict_set as combiner and {} as init.
     Since dict_set(d, (k,v)) = d ∪ {k↦v} (with override on collision),
     the final result is the finite function {kᵢ ↦ f(kᵢ)} for last-write-wins
     on duplicate keys.
  □

For accumulator maps (defaultdict(list)):
  fold[dict_append](∅, pairs) ≡ fold[setdefault_append](∅, pairs)
  Both construct the same multi-valued map.
"""

EXAMPLES = [
    {
        "name": "comprehension_vs_loop",
        "before": "fold[dict_set]({}, map(λk.(k,f(k)), keys))",
        "after": "{k: f(k) for k in keys}  (OMap with dict output)",
        "benchmark": None,
    },
    {
        "name": "fromkeys_vs_comprehension",
        "before": "dict.fromkeys(keys, 0)",
        "after": "{k: 0 for k in keys}",
        "benchmark": None,
    },
    {
        "name": "defaultdict_vs_setdefault",
        "before": "fold[setdefault_append]({}, pairs)",
        "after": "fold[dict_append]({}, pairs)",
        "benchmark": None,
    },
    {
        "name": "dict_comprehension_to_dict_call",
        "before": "dict(map(λp.(p[0],p[1]), pairs))",
        "after": "dict(pairs)",
        "benchmark": None,
    },
    {
        "name": "merge_dicts",
        "before": "dict_update(dict_update({}, d1), d2)",
        "after": "{**d1, **d2}",
        "benchmark": None,
    },
]


# ═══════════════════════════════════════════════════════════
# Pattern recognition helpers
# ═══════════════════════════════════════════════════════════

def _is_dict_construction_fold(term: OFold) -> bool:
    """Check if a fold constructs a dictionary."""
    return (term.op_name in _DICT_SET_OPS | _DICT_ACCUM_OPS
            or term.op_name.startswith('dict_'))


def _is_empty_dict(term: OTerm) -> bool:
    """Check if term represents an empty dictionary."""
    if isinstance(term, ODict) and len(term.pairs) == 0:
        return True
    if isinstance(term, OOp) and term.name in ('dict', 'OrderedDict') and not term.args:
        return True
    return False


def _extract_key_value_transform(collection: OTerm) -> Optional[Tuple[OTerm, OTerm, OTerm]]:
    """Extract (key_fn, val_fn, source) from a map producing key-value pairs.

    Recognizes patterns like:
        map(λk. (k, f(k)), keys) → (λk.k, λk.f(k), keys)
    """
    if isinstance(collection, OMap) and isinstance(collection.transform, OLam):
        lam = collection.transform
        if (isinstance(lam.body, OOp) and lam.body.name == 'tuple'
                and len(lam.body.args) == 2):
            key_expr, val_expr = lam.body.args
            key_fn = OLam(lam.params, key_expr)
            val_fn = OLam(lam.params, val_expr)
            return (key_fn, val_fn, collection.collection)
        if isinstance(lam.body, OSeq) and len(lam.body.elements) == 2:
            key_expr, val_expr = lam.body.elements
            key_fn = OLam(lam.params, key_expr)
            val_fn = OLam(lam.params, val_expr)
            return (key_fn, val_fn, collection.collection)
    return None


def _is_identity_key(key_fn: OTerm) -> bool:
    """Check if key_fn is the identity: λk. k."""
    if isinstance(key_fn, OLam) and len(key_fn.params) == 1:
        if isinstance(key_fn.body, OVar) and key_fn.body.name == key_fn.params[0]:
            return True
    return False


def _is_constant_val(val_fn: OTerm) -> Optional[OTerm]:
    """Check if val_fn returns a constant: λk. C → C."""
    if isinstance(val_fn, OLam) and len(val_fn.params) == 1:
        # Check body doesn't reference the parameter
        if isinstance(val_fn.body, OLit):
            return val_fn.body
        if isinstance(val_fn.body, OVar) and val_fn.body.name != val_fn.params[0]:
            return val_fn.body
    return None


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D12: Map construction equivalences.

    Handles:
      1. fold[dict_set]({}, map(λk.(k,f(k)), keys)) → dict comprehension OMap
      2. dict.fromkeys(keys, v) → fold[dict_set]({}, map(λk.(k,v), keys))
      3. fold[dict_set]({}, map(λk.(k,v), keys)) → fromkeys(keys, v)
      4. setdefault_append ↔ dict_append (accumulator synonym)
      5. defaultdict(factory) → fold[dict_accum]({}, items)
      6. dict(pairs) ↔ fold[dict_set]({}, pairs)
      7. {**d1, **d2} ↔ dict_update chain
      8. dict(zip(keys, values)) ↔ dict comprehension
    """
    results: List[Tuple[OTerm, str]] = []

    # ── fold[dict_set] patterns ──
    if isinstance(term, OFold) and _is_dict_construction_fold(term):
        # dict_set fold → comprehension
        if term.op_name in _DICT_SET_OPS and _is_empty_dict(term.init):
            kv = _extract_key_value_transform(term.collection)
            if kv is not None:
                key_fn, val_fn, source = kv
                if _is_identity_key(key_fn):
                    # fold[dict_set]({}, map(λk.(k,f(k)), keys)) → OMap as dict comp
                    dict_comp = OMap(val_fn, source)
                    results.append((dict_comp, 'D12_fold_to_comprehension'))

                    # Check if constant value → fromkeys
                    const = _is_constant_val(val_fn)
                    if const is not None:
                        results.append((
                            OOp('fromkeys', (source, const)),
                            'D12_fold_to_fromkeys',
                        ))

        # Accumulator synonym normalization
        if term.op_name in ('setdefault_append',):
            results.append((
                OFold('dict_append', term.init, term.collection),
                'D12_setdefault_to_dict_append',
            ))
        if term.op_name in ('setdefault_add',):
            results.append((
                OFold('dict_incr', term.init, term.collection),
                'D12_setdefault_add_to_dict_incr',
            ))

        # dict construction fold → dict(pairs)
        if term.op_name in _DICT_SET_OPS and _is_empty_dict(term.init):
            results.append((
                OOp('dict', (term.collection,)),
                'D12_fold_to_dict_call',
            ))

    # ── fromkeys → fold ──
    if isinstance(term, OOp) and term.name in _FROMKEYS_OPS:
        if len(term.args) == 2:
            keys, val = term.args
            # fromkeys(keys, v) → fold[dict_set]({}, map(λk.(k,v), keys))
            kv_transform = OLam(('_k',), OSeq((OVar('_k'), val)))
            fold_form = OFold('dict_set', ODict(()), OMap(kv_transform, keys))
            results.append((fold_form, 'D12_fromkeys_to_fold'))

            # fromkeys(keys, v) → comprehension
            val_fn = OLam(('_k',), val)
            results.append((
                OMap(val_fn, keys),
                'D12_fromkeys_to_comprehension',
            ))

    # ── dict(pairs) ↔ fold ──
    if isinstance(term, OOp) and term.name == 'dict':
        if len(term.args) == 1:
            pairs = term.args[0]
            results.append((
                OFold('dict_set', ODict(()), pairs),
                'D12_dict_call_to_fold',
            ))

            # dict(zip(keys, values)) → comprehension
            if isinstance(pairs, OOp) and pairs.name == 'zip' and len(pairs.args) == 2:
                keys, values = pairs.args
                kv_lam = OLam(('_kv',), OOp('getitem', (OVar('_kv'), OLit(1))))
                results.append((
                    OMap(kv_lam, pairs),
                    'D12_dict_zip_to_comprehension',
                ))

    # ── defaultdict(factory) patterns ──
    if isinstance(term, OOp) and term.name in _DEFAULTDICT_OPS:
        if len(term.args) >= 1:
            factory = term.args[0]
            # defaultdict(list) → empty dict for fold[dict_append]
            if isinstance(factory, OVar) and factory.name == 'list':
                results.append((
                    ODict(()),
                    'D12_defaultdict_list_to_empty',
                ))
            if isinstance(factory, OLit) and factory.value == 0:
                results.append((
                    ODict(()),
                    'D12_defaultdict_int_to_empty',
                ))

    # ── dict update chain → merge ──
    if isinstance(term, OOp) and term.name in ('dict_update', 'update'):
        if len(term.args) == 2:
            base, new = term.args
            if isinstance(base, OOp) and base.name in ('dict_update', 'update'):
                if len(base.args) == 2:
                    # update(update(d0, d1), d2) → merge(d0, d1, d2)
                    results.append((
                        OOp('dict_merge', (base.args[0], base.args[1], new)),
                        'D12_update_chain_to_merge',
                    ))
            # update(d1, d2) → {**d1, **d2}
            results.append((
                OOp('dict_unpack', (base, new)),
                'D12_update_to_unpack',
            ))

    # ── ODict literal ↔ comprehension over literal keys ──
    if isinstance(term, ODict) and len(term.pairs) >= 2:
        keys_seq = OSeq(tuple(k for k, _ in term.pairs))
        # Check if values follow a pattern (same transform on keys)
        all_same_op = True
        first_op = None
        for k, v in term.pairs:
            if isinstance(v, OOp) and len(v.args) == 1:
                if first_op is None:
                    first_op = v.name
                elif v.name != first_op:
                    all_same_op = False
                    break
            else:
                all_same_op = False
                break
        if all_same_op and first_op is not None:
            val_fn = OLam(('_k',), OOp(first_op, (OVar('_k'),)))
            comp = OMap(val_fn, keys_seq)
            results.append((comp, 'D12_dict_literal_to_comprehension'))

    return results


# ═══════════════════════════════════════════════════════════
# Recognizer & scoring
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could D12 apply to this term?"""
    if isinstance(term, OFold):
        return _is_dict_construction_fold(term)
    if isinstance(term, OOp):
        if term.name in _FROMKEYS_OPS | _DEFAULTDICT_OPS:
            return True
        if term.name in ('dict', 'dict_update', 'update'):
            return True
    if isinstance(term, ODict) and len(term.pairs) >= 2:
        return True
    return False


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Heuristic 0.0–1.0 for how likely D12 helps bridge term→other."""
    score = 0.0

    # Both are dict constructions
    t_is_dict = (isinstance(term, OFold) and _is_dict_construction_fold(term)
                 or isinstance(term, OOp) and term.name in _FROMKEYS_OPS | _DEFAULTDICT_OPS | {'dict'}
                 or isinstance(term, ODict))
    o_is_dict = (isinstance(other, OFold) and _is_dict_construction_fold(other)
                 or isinstance(other, OOp) and other.name in _FROMKEYS_OPS | _DEFAULTDICT_OPS | {'dict'}
                 or isinstance(other, ODict))

    if t_is_dict and o_is_dict:
        score = max(score, 0.9)

    # One is fold, other is comprehension
    if isinstance(term, OFold) and isinstance(other, OMap):
        if _is_dict_construction_fold(term):
            score = max(score, 0.85)
    if isinstance(term, OMap) and isinstance(other, OFold):
        if _is_dict_construction_fold(other):
            score = max(score, 0.85)

    # fromkeys ↔ comprehension
    if isinstance(term, OOp) and term.name in _FROMKEYS_OPS:
        if isinstance(other, OMap) or isinstance(other, OFold):
            score = max(score, 0.9)
    if isinstance(other, OOp) and other.name in _FROMKEYS_OPS:
        if isinstance(term, OMap) or isinstance(term, OFold):
            score = max(score, 0.9)

    # defaultdict → empty dict
    if isinstance(term, OOp) and term.name in _DEFAULTDICT_OPS:
        score = max(score, 0.6)

    return min(score, 1.0)


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Reverse D12: expand canonical dict forms back to alternatives.

    OMap → fold[dict_set]
    fromkeys → fold
    dict(pairs) → fold
    """
    results: List[Tuple[OTerm, str]] = []

    # Comprehension → fold
    if isinstance(term, OMap) and term.filter_pred is None:
        # Map producing dict → fold[dict_set]
        if isinstance(term.transform, OLam):
            kv_transform = OLam(term.transform.params,
                                OSeq((OVar(term.transform.params[0]),
                                      term.transform.body)))
            fold = OFold('dict_set', ODict(()), OMap(kv_transform, term.collection))
            results.append((fold, 'D12_inv_comprehension_to_fold'))

    # dict(pairs) → fromkeys when values are constant
    if isinstance(term, OOp) and term.name == 'dict':
        if len(term.args) == 1:
            pairs = term.args[0]
            results.append((
                OFold('dict_set', ODict(()), pairs),
                'D12_inv_dict_to_fold',
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════

if __name__ == '__main__':
    ctx = FiberCtx(param_duck_types={})

    # Test 1: fold[dict_set]({}, map(λk.(k,f(k)), keys)) → comprehension
    kv_lam = OLam(('k',), OSeq((OVar('k'), OOp('f', (OVar('k'),)))))
    fold_dict = OFold('dict_set', ODict(()), OMap(kv_lam, OVar('keys')))
    rewrites = apply(fold_dict, ctx)
    assert any('D12_fold_to_comprehension' in ax for _, ax in rewrites), \
        f"Expected fold→comp, got {[ax for _, ax in rewrites]}"
    print("✓ fold[dict_set] → comprehension")

    # Test 2: fold with constant value → fromkeys
    const_lam = OLam(('k',), OSeq((OVar('k'), OLit(0))))
    fold_const = OFold('dict_set', ODict(()), OMap(const_lam, OVar('keys')))
    rewrites = apply(fold_const, ctx)
    assert any('D12_fold_to_fromkeys' in ax for _, ax in rewrites)
    print("✓ fold with constant → fromkeys")

    # Test 3: fromkeys → fold
    fromkeys = OOp('fromkeys', (OVar('keys'), OLit(0)))
    rewrites = apply(fromkeys, ctx)
    assert any('D12_fromkeys_to_fold' in ax for _, ax in rewrites)
    assert any('D12_fromkeys_to_comprehension' in ax for _, ax in rewrites)
    print("✓ fromkeys → fold + comprehension")

    # Test 4: dict(pairs) → fold
    dict_call = OOp('dict', (OVar('pairs'),))
    rewrites = apply(dict_call, ctx)
    assert any('D12_dict_call_to_fold' in ax for _, ax in rewrites)
    print("✓ dict(pairs) → fold")

    # Test 5: setdefault_append → dict_append
    setdef_fold = OFold('setdefault_append', ODict(()), OVar('items'))
    rewrites = apply(setdef_fold, ctx)
    assert any('D12_setdefault_to_dict_append' in ax for _, ax in rewrites)
    print("✓ setdefault_append → dict_append")

    # Test 6: defaultdict(list) → empty dict
    ddict = OOp('defaultdict', (OVar('list'),))
    rewrites = apply(ddict, ctx)
    assert any('D12_defaultdict_list_to_empty' in ax for _, ax in rewrites)
    print("✓ defaultdict(list) → empty dict")

    # Test 7: update chain → merge
    chain_update = OOp('dict_update', (
        OOp('dict_update', (OVar('d0'), OVar('d1'))),
        OVar('d2'),
    ))
    rewrites = apply(chain_update, ctx)
    assert any('D12_update_chain_to_merge' in ax for _, ax in rewrites)
    print("✓ update chain → merge")

    # Test 8: dict(zip(keys, vals)) → comprehension
    dict_zip = OOp('dict', (OOp('zip', (OVar('keys'), OVar('vals'))),))
    rewrites = apply(dict_zip, ctx)
    assert any('D12_dict_zip_to_comprehension' in ax for _, ax in rewrites)
    print("✓ dict(zip(keys, vals)) → comprehension")

    # Test 9: recognizes
    assert recognizes(fold_dict)
    assert recognizes(fromkeys)
    assert recognizes(dict_call)
    assert recognizes(ddict)
    assert not recognizes(OVar('x'))
    assert not recognizes(OFold('add', OLit(0), OVar('xs')))
    print("✓ recognizes()")

    # Test 10: relevance_score
    score = relevance_score(fromkeys, fold_dict)
    assert score >= 0.8, f"Expected high relevance, got {score}"
    print(f"✓ relevance_score(fromkeys, fold) = {score:.2f}")

    # Test 11: inverse
    comp = OMap(OLam(('k',), OOp('f', (OVar('k'),))), OVar('keys'))
    inv = apply_inverse(comp, ctx)
    assert any('D12_inv_comprehension_to_fold' in ax for _, ax in inv)
    print("✓ apply_inverse(comprehension) → fold")

    # Test 12: fold → dict call
    assert any('D12_fold_to_dict_call' in ax for _, ax in apply(fold_dict, ctx))
    print("✓ fold → dict() call")

    print("\nAll D12 self-tests passed ✓")
