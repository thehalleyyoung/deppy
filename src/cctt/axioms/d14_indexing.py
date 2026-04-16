"""D14: Indexing Equivalences (Theorem 21.6.1).

Direct index vs enumerate vs zip(range) — different ways to access
elements by position in a collection.

Mathematical foundation:
  Indexing into a sequence xs at position i is the evaluation morphism
    ev_i : X^n → X
  in the category of finite products.  enumerate(xs) packages
  (i, xs[i]) pairs, which is the graph of ev;  zip(range(n), xs)
  constructs the same graph differently.

  All three are sections of the projection  X × ℕ → X.

Covers:
  • xs[i] ↔ dict(enumerate(xs))[i]  (when indices are dense)
  • for i, x in enumerate(xs) ↔ for i in range(len(xs)): x = xs[i]
  • zip(range(len(xs)), xs) ↔ enumerate(xs)
  • list(xs)[i] ↔ xs[i]  (redundant list() around indexable)
  • dict lookup on dense keys ↔ array indexing
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

AXIOM_NAME = 'D14_indexing'
AXIOM_CATEGORY = 'data_structure'  # §21

SOUNDNESS_PROOF = """
Theorem 21.6.1 (Indexing Equivalence):
  For a sequence xs of length n:
    (a) xs[i]  ≡  dict(enumerate(xs))[i]  for 0 ≤ i < n
    (b) enumerate(xs)  ≡  zip(range(len(xs)), xs)
    (c) list(xs)[i]  ≡  xs[i]  when xs supports __getitem__

Proof sketch:
  (a) enumerate(xs) = [(0,xs[0]), ..., (n-1,xs[n-1])].
      dict(enumerate(xs)) = {0: xs[0], ..., n-1: xs[n-1]}.
      Lookup by key i gives xs[i].  ∎
  (b) zip(range(n), xs) = [(0,xs[0]), ..., (n-1,xs[n-1])] = enumerate(xs).  ∎
  (c) list(xs) copies xs; indexing into the copy equals indexing
      into the original (assuming no mutation between).  ∎
"""

COMPOSES_WITH = ['D15_traversal', 'D13_histogram']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'enumerate to zip-range',
        'before': "enumerate(xs)",
        'after': "zip(range(len(xs)), xs)",
        'axiom': 'D14_enumerate_to_zip_range',
    },
    {
        'name': 'zip-range to enumerate',
        'before': "zip(range(len(xs)), xs)",
        'after': "enumerate(xs)",
        'axiom': 'D14_zip_range_to_enumerate',
    },
    {
        'name': 'indexed loop to enumerate loop',
        'before': "for i in range(len(xs)): use(xs[i])",
        'after': "for i, x in enumerate(xs): use(x)",
        'axiom': 'D14_index_loop_to_enumerate',
    },
    {
        'name': 'redundant list removal',
        'before': "list(xs)[i]",
        'after': "xs[i]",
        'axiom': 'D14_strip_redundant_list',
    },
    {
        'name': 'dict dense-key to array',
        'before': "dict(enumerate(xs))[i]",
        'after': "xs[i]",
        'axiom': 'D14_dict_dense_to_array',
    },
]


# ═══════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════

@dataclass
class FiberCtx:
    """Lightweight fiber context for standalone axiom evaluation."""
    param_duck_types: Dict[str, str] = field(default_factory=dict)


def _is_len_of(term: OTerm, collection: OTerm) -> bool:
    """Check if term is len(collection)."""
    if isinstance(term, OOp) and term.name == 'len' and len(term.args) == 1:
        return term.args[0].canon() == collection.canon()
    return False


def _is_range_len(term: OTerm) -> Optional[OTerm]:
    """If term is range(len(xs)), return xs.  Otherwise None."""
    if isinstance(term, OOp) and term.name == 'range' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'len' and len(inner.args) == 1:
            return inner.args[0]
    return None


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D14 indexing equivalences to *term*."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── enumerate(xs) → zip(range(len(xs)), xs) ──
    if isinstance(term, OOp) and term.name == 'enumerate':
        if len(term.args) == 1:
            xs = term.args[0]
            results.append((
                OOp('zip', (OOp('range', (OOp('len', (xs,)),)), xs)),
                'D14_enumerate_to_zip_range',
            ))

    # ── zip(range(len(xs)), xs) → enumerate(xs) ──
    if isinstance(term, OOp) and term.name == 'zip' and len(term.args) == 2:
        range_part, coll = term.args
        inner = _is_range_len(range_part)
        if inner is not None and inner.canon() == coll.canon():
            results.append((
                OOp('enumerate', (coll,)),
                'D14_zip_range_to_enumerate',
            ))

    # ── list(xs)[i] → xs[i] (strip redundant list) ──
    if isinstance(term, OOp) and term.name == 'getitem' and len(term.args) == 2:
        base, idx = term.args
        if isinstance(base, OOp) and base.name == 'list' and len(base.args) == 1:
            results.append((
                OOp('getitem', (base.args[0], idx)),
                'D14_strip_redundant_list',
            ))

    # ── tuple(xs)[i] → xs[i] (strip redundant tuple) ──
    if isinstance(term, OOp) and term.name == 'getitem' and len(term.args) == 2:
        base, idx = term.args
        if isinstance(base, OOp) and base.name == 'tuple' and len(base.args) == 1:
            results.append((
                OOp('getitem', (base.args[0], idx)),
                'D14_strip_redundant_tuple',
            ))

    # ── dict(enumerate(xs))[i] → xs[i] ──
    if isinstance(term, OOp) and term.name == 'getitem' and len(term.args) == 2:
        base, idx = term.args
        if isinstance(base, OOp) and base.name == 'dict' and len(base.args) == 1:
            inner = base.args[0]
            if isinstance(inner, OOp) and inner.name == 'enumerate' and len(inner.args) == 1:
                results.append((
                    OOp('getitem', (inner.args[0], idx)),
                    'D14_dict_dense_to_array',
                ))

    # ── map with index-based body over range(len(xs)) → map over enumerate ──
    # fold over range(len(xs)) with body using xs[i] → fold over xs directly
    if isinstance(term, OFold):
        rng = _is_range_len(term.collection)
        if rng is not None:
            # fold[op](init, range(len(xs))) where body references xs[i]
            # can be rewritten to fold[op'](init, xs)
            results.append((
                OFold(term.op_name, term.init, rng),
                'D14_fold_over_range_len',
            ))

    # ── map(λi. xs[i], range(len(xs))) → xs (identity indexing) ──
    if isinstance(term, OMap):
        rng = _is_range_len(term.collection)
        if rng is not None and isinstance(term.transform, OLam):
            lam = term.transform
            if (len(lam.params) == 1
                    and isinstance(lam.body, OOp)
                    and lam.body.name == 'getitem'
                    and len(lam.body.args) == 2):
                base, idx = lam.body.args
                if (base.canon() == rng.canon()
                        and isinstance(idx, OVar)
                        and idx.name == lam.params[0]):
                    results.append((rng, 'D14_identity_index_map'))

    # ── map(λi. f(xs[i]), range(len(xs))) → map(f, xs) ──
    if isinstance(term, OMap):
        rng = _is_range_len(term.collection)
        if rng is not None and isinstance(term.transform, OLam):
            lam = term.transform
            if len(lam.params) == 1 and isinstance(lam.body, OOp):
                # Check if body is f(getitem(xs, i))
                for j, arg in enumerate(lam.body.args):
                    if (isinstance(arg, OOp) and arg.name == 'getitem'
                            and len(arg.args) == 2):
                        base, idx = arg.args
                        if (base.canon() == rng.canon()
                                and isinstance(idx, OVar)
                                and idx.name == lam.params[0]):
                            new_param = '_x'
                            new_args = list(lam.body.args)
                            new_args[j] = OVar(new_param)
                            new_lam = OLam(
                                (new_param,),
                                OOp(lam.body.name, tuple(new_args)),
                            )
                            results.append((
                                OMap(new_lam, rng, term.filter_pred),
                                'D14_index_map_to_direct_map',
                            ))
                            break

    # ── xs[i] → dict_lookup when i is a non-integer key ──
    # (reverse direction: dict d[k] → array when keys are 0..n-1)
    # This is context-dependent; we provide the structural rewrite
    if isinstance(term, OOp) and term.name == 'dictget' and len(term.args) == 2:
        d, k = term.args
        results.append((
            OOp('getitem', (d, k)),
            'D14_dictget_to_getitem',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D14 in reverse direction."""
    results = apply(term, ctx)
    inverse_labels = {
        'D14_zip_range_to_enumerate',
        'D14_strip_redundant_list',
        'D14_strip_redundant_tuple',
        'D14_dict_dense_to_array',
        'D14_identity_index_map',
        'D14_index_map_to_direct_map',
        'D14_dictget_to_getitem',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D14 is potentially applicable."""
    if isinstance(term, OOp):
        if term.name in ('enumerate', 'dictget'):
            return True
        if term.name == 'zip' and len(term.args) == 2:
            return _is_range_len(term.args[0]) is not None
        if term.name == 'getitem' and len(term.args) == 2:
            base = term.args[0]
            if isinstance(base, OOp) and base.name in ('list', 'tuple', 'dict'):
                return True
    if isinstance(term, OFold):
        return _is_range_len(term.collection) is not None
    if isinstance(term, OMap):
        return _is_range_len(term.collection) is not None
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D14 relevance for *source* → *target* bridge."""
    sc = source.canon()
    tc = target.canon()

    has_enum_s = 'enumerate(' in sc
    has_enum_t = 'enumerate(' in tc
    has_zip_range_s = 'zip(' in sc and 'range(' in sc
    has_zip_range_t = 'zip(' in tc and 'range(' in tc
    has_getitem = 'getitem(' in sc or 'getitem(' in tc

    if has_enum_s != has_enum_t:
        return 0.90
    if has_zip_range_s != has_zip_range_t:
        return 0.85
    if has_enum_s and has_zip_range_t:
        return 0.90
    if has_getitem and (has_enum_s or has_enum_t):
        return 0.70
    if has_getitem:
        return 0.30
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
    i = OVar('i')

    # ── enumerate → zip(range) ──
    print("D14: enumerate → zip(range) ...")
    enum_term = OOp('enumerate', (xs,))
    r = apply(enum_term, ctx)
    _assert(len(r) >= 1, "enumerate should rewrite")
    _assert(r[0][1] == 'D14_enumerate_to_zip_range', "axiom label")

    # ── zip(range(len(xs)), xs) → enumerate(xs) ──
    print("D14: zip(range) → enumerate ...")
    zip_term = OOp('zip', (OOp('range', (OOp('len', (xs,)),)), xs))
    r2 = apply(zip_term, ctx)
    _assert(any(lbl == 'D14_zip_range_to_enumerate' for _, lbl in r2),
            "zip(range)→enumerate")

    # ── Roundtrip ──
    print("D14: roundtrip ...")
    fwd = apply(enum_term, ctx)
    bwd = apply(fwd[0][0], ctx)
    _assert(any(lbl == 'D14_zip_range_to_enumerate' for _, lbl in bwd),
            "roundtrip enumerate↔zip")

    # ── list(xs)[i] → xs[i] ──
    print("D14: strip redundant list ...")
    list_idx = OOp('getitem', (OOp('list', (xs,)), i))
    r3 = apply(list_idx, ctx)
    _assert(any(lbl == 'D14_strip_redundant_list' for _, lbl in r3),
            "strip list")

    # ── dict(enumerate(xs))[i] → xs[i] ──
    print("D14: dict(enumerate) → direct ...")
    dict_enum = OOp('getitem', (OOp('dict', (OOp('enumerate', (xs,)),)), i))
    r4 = apply(dict_enum, ctx)
    _assert(any(lbl == 'D14_dict_dense_to_array' for _, lbl in r4),
            "dict(enumerate)→direct")

    # ── fold over range(len(xs)) ──
    print("D14: fold over range(len) ...")
    fold_rng = OFold('add', OLit(0), OOp('range', (OOp('len', (xs,)),)))
    r5 = apply(fold_rng, ctx)
    _assert(any(lbl == 'D14_fold_over_range_len' for _, lbl in r5),
            "fold over range(len)")

    # ── identity index map ──
    print("D14: identity index map ...")
    id_map = OMap(
        OLam(('i',), OOp('getitem', (xs, OVar('i')))),
        OOp('range', (OOp('len', (xs,)),)),
    )
    r6 = apply(id_map, ctx)
    _assert(any(lbl == 'D14_identity_index_map' for _, lbl in r6),
            "identity index map")

    # ── recognizes ──
    print("D14: recognizes ...")
    _assert(recognizes(enum_term), "recognizes enumerate")
    _assert(recognizes(zip_term), "recognizes zip(range)")
    _assert(recognizes(list_idx), "recognizes list(xs)[i]")
    _assert(not recognizes(OOp('sorted', (xs,))), "does not recognise sorted")

    # ── relevance_score ──
    print("D14: relevance_score ...")
    score = relevance_score(enum_term, zip_term)
    _assert(score > 0.8, f"enum↔zip score={score:.2f} > 0.8")

    # ── apply_inverse ──
    print("D14: apply_inverse ...")
    inv = apply_inverse(zip_term, ctx)
    _assert(len(inv) >= 1, "inverse should produce enumerate")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  D14 indexing: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
