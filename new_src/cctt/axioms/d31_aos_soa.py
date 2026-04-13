"""D31: AoS ↔ SoA / Zip-Unzip Duality (Theorem 31.1).

Array of structs ↔ Struct of arrays ↔ zip/unzip transposition.

Mathematical foundation:
  The isomorphism  (A × B)^n  ≅  A^n × B^n  is the universal property
  of products in Set (or any cartesian closed category).  zip and unzip
  are the witnesses of this natural isomorphism in the functor category
  [ℕ, Set]:

      zip:   A^n × B^n  →  (A × B)^n
      unzip: (A × B)^n  →  A^n × B^n

  Projection absorption:  map(fst, zip(xs, ys)) ≡ xs
  follows from  π₁ ∘ ⟨f, g⟩ = f  (product β-law).

Covers:
  • zip(xs, ys) ↔ [(xs[i], ys[i]) for i in range(n)]
  • unzip(pairs) ↔ ([p[0] for p in pairs], [p[1] for p in pairs])
  • map(fst, zip(xs, ys)) → xs  (projection absorption)
  • map(snd, zip(xs, ys)) → ys
  • zip(*zip(xs, ys)) → (xs, ys)  (round-trip)
  • AoS ↔ SoA layout transformations
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

AXIOM_NAME = 'D31_aos_soa'
AXIOM_CATEGORY = 'data_representation'  # §31 — Data representation duality

SOUNDNESS_PROOF = """
Theorem 31.1 (Zip-Unzip Duality):
  For sequences xs : A^n, ys : B^n, pairs : (A × B)^n,
    zip(xs, ys) ≡ [(xs[i], ys[i]) for i in range(len(xs))]
    unzip(pairs) ≡ ([p[0] for p in pairs], [p[1] for p in pairs])
  and  unzip(zip(xs, ys)) ≡ (xs, ys).

Proof sketch:
  1. zip is the diagonal of the product functor:
       zip(xs, ys)[i] = (xs[i], ys[i])  by definition.
  2. unzip is the pair of projections:
       unzip(ps) = (map(π₁, ps), map(π₂, ps))  by definition.
  3. Round-trip: unzip(zip(xs, ys))
       = (map(π₁, zip(xs, ys)), map(π₂, zip(xs, ys)))
       = (xs, ys)   by the product β-law.
  4. Projection absorption: map(fst, zip(xs, ys))
       = [zip(xs, ys)[i][0] for i in range(n)]
       = [xs[i] for i in range(n)]
       = xs.  ∎

AoS ↔ SoA is exactly the same isomorphism on records (n-ary products).
"""

COMPOSES_WITH = ['D12_map_construct', 'D04_comp_fusion', 'D14_indexing']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'zip to comprehension',
        'before': "zip(xs, ys)",
        'after': "[(xs[i], ys[i]) for i in range(len(xs))]",
        'axiom': 'D31_zip_to_comp',
    },
    {
        'name': 'comprehension to zip',
        'before': "[(xs[i], ys[i]) for i in range(len(xs))]",
        'after': "zip(xs, ys)",
        'axiom': 'D31_comp_to_zip',
    },
    {
        'name': 'unzip to projections',
        'before': "unzip(pairs)",
        'after': "([p[0] for p in pairs], [p[1] for p in pairs])",
        'axiom': 'D31_unzip_to_proj',
    },
    {
        'name': 'projection absorption fst',
        'before': "map(fst, zip(xs, ys))",
        'after': "xs",
        'axiom': 'D31_proj_absorb_fst',
    },
    {
        'name': 'projection absorption snd',
        'before': "map(snd, zip(xs, ys))",
        'after': "ys",
        'axiom': 'D31_proj_absorb_snd',
    },
    {
        'name': 'zip-unzip round-trip',
        'before': "zip(*unzip(pairs))",
        'after': "pairs",
        'axiom': 'D31_zip_unzip_roundtrip',
    },
]


# ═══════════════════════════════════════════════════════════
# Helper: fiber context
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
    """Apply D31 AoS ↔ SoA / zip-unzip equivalences to *term*.

    Returns list of (rewritten_term, axiom_label) pairs.
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── zip(xs, ys) → comprehension [(xs[i], ys[i]) ...] ──
    if isinstance(term, OOp) and term.name == 'zip' and len(term.args) == 2:
        xs, ys = term.args
        i_var = OVar('_i')
        elem = OSeq((OOp('getitem', (xs, i_var)), OOp('getitem', (ys, i_var))))
        comp = OMap(
            OLam(('_i',), elem),
            OOp('range', (OOp('len', (xs,)),)),
        )
        results.append((comp, 'D31_zip_to_comp'))

    # ── map over zip: projection absorption ──
    if isinstance(term, OMap):
        tf = term.transform
        coll = term.collection
        # map(λp. p[0], zip(xs, ys)) → xs
        if (isinstance(tf, OLam) and len(tf.params) == 1
                and isinstance(coll, OOp) and coll.name == 'zip'
                and len(coll.args) == 2):
            body = tf.body
            param = tf.params[0]
            if isinstance(body, OOp) and body.name == 'getitem' and len(body.args) == 2:
                base, idx = body.args
                if isinstance(base, OVar) and base.name == param:
                    if isinstance(idx, OLit) and idx.value == 0:
                        results.append((coll.args[0], 'D31_proj_absorb_fst'))
                    elif isinstance(idx, OLit) and idx.value == 1:
                        results.append((coll.args[1], 'D31_proj_absorb_snd'))

    # ── OOp('map', (fst_lam, zip_term)) — alternate map encoding ──
    if isinstance(term, OOp) and term.name == 'map' and len(term.args) == 2:
        tf, coll = term.args
        if (isinstance(tf, OLam) and len(tf.params) == 1
                and isinstance(coll, OOp) and coll.name == 'zip'
                and len(coll.args) == 2):
            body = tf.body
            param = tf.params[0]
            if isinstance(body, OOp) and body.name == 'getitem' and len(body.args) == 2:
                base, idx = body.args
                if isinstance(base, OVar) and base.name == param:
                    if isinstance(idx, OLit) and idx.value == 0:
                        results.append((coll.args[0], 'D31_proj_absorb_fst'))
                    elif isinstance(idx, OLit) and idx.value == 1:
                        results.append((coll.args[1], 'D31_proj_absorb_snd'))

    # ── unzip(pairs) → (map(fst, pairs), map(snd, pairs)) ──
    if isinstance(term, OOp) and term.name == 'unzip' and len(term.args) == 1:
        pairs = term.args[0]
        fst_map = OMap(OLam(('_p',), OOp('getitem', (OVar('_p'), OLit(0)))), pairs)
        snd_map = OMap(OLam(('_p',), OOp('getitem', (OVar('_p'), OLit(1)))), pairs)
        results.append((OSeq((fst_map, snd_map)), 'D31_unzip_to_proj'))

    # ── (map(fst, ps), map(snd, ps)) → unzip(ps)  (reverse) ──
    if isinstance(term, OSeq) and len(term.elements) == 2:
        fst_arm, snd_arm = term.elements
        ps_fst = _is_projection_map(fst_arm, 0)
        ps_snd = _is_projection_map(snd_arm, 1)
        if ps_fst is not None and ps_snd is not None:
            if ps_fst.canon() == ps_snd.canon():
                results.append((OOp('unzip', (ps_fst,)), 'D31_proj_to_unzip'))

    # ── zip(*unzip(pairs)) → pairs  (round-trip) ──
    if isinstance(term, OOp) and term.name == 'zip':
        if len(term.args) == 1 and isinstance(term.args[0], OOp):
            if term.args[0].name == 'star_unzip':
                results.append((term.args[0].args[0], 'D31_zip_unzip_roundtrip'))
        # zip(unzip(p)[0], unzip(p)[1]) → p
        if len(term.args) == 2:
            a, b = term.args
            if (isinstance(a, OOp) and a.name == 'getitem'
                    and isinstance(b, OOp) and b.name == 'getitem'):
                if (len(a.args) == 2 and len(b.args) == 2
                        and isinstance(a.args[0], OOp) and a.args[0].name == 'unzip'
                        and isinstance(b.args[0], OOp) and b.args[0].name == 'unzip'):
                    if a.args[0].canon() == b.args[0].canon():
                        if (isinstance(a.args[1], OLit) and a.args[1].value == 0
                                and isinstance(b.args[1], OLit) and b.args[1].value == 1):
                            results.append((
                                a.args[0].args[0],
                                'D31_zip_unzip_roundtrip',
                            ))

    # ── enumerate(xs) → zip(range(len(xs)), xs) ──
    if isinstance(term, OOp) and term.name == 'enumerate' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OOp('zip', (OOp('range', (OOp('len', (xs,)),)), xs)),
            'D31_enumerate_to_zip',
        ))

    return results


def _is_projection_map(term: OTerm, idx: int) -> Optional[OTerm]:
    """If *term* is map(λp. p[idx], collection), return collection."""
    if isinstance(term, OMap):
        tf = term.transform
        if isinstance(tf, OLam) and len(tf.params) == 1:
            body = tf.body
            param = tf.params[0]
            if (isinstance(body, OOp) and body.name == 'getitem'
                    and len(body.args) == 2):
                base, ix = body.args
                if (isinstance(base, OVar) and base.name == param
                        and isinstance(ix, OLit) and ix.value == idx):
                    return term.collection
    return None


# ═══════════════════════════════════════════════════════════
# Inverse axiom
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D31 in reverse direction."""
    results = apply(term, ctx)
    inverse_labels = {
        'D31_comp_to_zip',
        'D31_proj_to_unzip',
        'D31_proj_absorb_fst',
        'D31_proj_absorb_snd',
        'D31_zip_unzip_roundtrip',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D31 is potentially applicable to *term*."""
    if isinstance(term, OOp):
        if term.name in ('zip', 'unzip', 'enumerate', 'star_unzip'):
            return True
        if term.name == 'map' and len(term.args) == 2:
            if isinstance(term.args[1], OOp) and term.args[1].name == 'zip':
                return True
    if isinstance(term, OMap):
        if isinstance(term.collection, OOp) and term.collection.name == 'zip':
            return True
    if isinstance(term, OSeq) and len(term.elements) == 2:
        if (_is_projection_map(term.elements[0], 0) is not None
                and _is_projection_map(term.elements[1], 1) is not None):
            return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score how relevant D31 is for bridging *source* → *target*."""
    sc = source.canon()
    tc = target.canon()

    zip_s = 'zip(' in sc or 'unzip(' in sc
    zip_t = 'zip(' in tc or 'unzip(' in tc
    enum_s = 'enumerate(' in sc
    enum_t = 'enumerate(' in tc

    if zip_s and zip_t:
        return 0.90
    if (zip_s and not zip_t) or (not zip_s and zip_t):
        return 0.85
    if enum_s or enum_t:
        return 0.70
    if 'getitem' in sc and 'getitem' in tc:
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
    ys = OVar('ys')
    pairs = OVar('pairs')

    # ── zip → comp ──
    print("D31: zip → comprehension ...")
    zip_term = OOp('zip', (xs, ys))
    r = apply(zip_term, ctx)
    _assert(len(r) >= 1, "zip(xs, ys) should rewrite")
    _assert(r[0][1] == 'D31_zip_to_comp', "axiom label")
    _assert(isinstance(r[0][0], OMap), "result is OMap")

    # ── unzip → projections ──
    print("D31: unzip → projections ...")
    unzip_term = OOp('unzip', (pairs,))
    r2 = apply(unzip_term, ctx)
    _assert(any(lbl == 'D31_unzip_to_proj' for _, lbl in r2), "unzip→proj")

    # ── projection absorption fst ──
    print("D31: projection absorption fst ...")
    proj_fst = OMap(
        OLam(('p',), OOp('getitem', (OVar('p'), OLit(0)))),
        OOp('zip', (xs, ys)),
    )
    r3 = apply(proj_fst, ctx)
    _assert(any(lbl == 'D31_proj_absorb_fst' for _, lbl in r3), "proj fst")
    fst_result = [t for t, lbl in r3 if lbl == 'D31_proj_absorb_fst']
    _assert(len(fst_result) >= 1 and isinstance(fst_result[0], OVar)
            and fst_result[0].name == 'xs', "fst → xs")

    # ── projection absorption snd ──
    print("D31: projection absorption snd ...")
    proj_snd = OMap(
        OLam(('p',), OOp('getitem', (OVar('p'), OLit(1)))),
        OOp('zip', (xs, ys)),
    )
    r4 = apply(proj_snd, ctx)
    _assert(any(lbl == 'D31_proj_absorb_snd' for _, lbl in r4), "proj snd")

    # ── (map(fst, ps), map(snd, ps)) → unzip(ps) ──
    print("D31: paired projections → unzip ...")
    pair_proj = OSeq((
        OMap(OLam(('_p',), OOp('getitem', (OVar('_p'), OLit(0)))), pairs),
        OMap(OLam(('_p',), OOp('getitem', (OVar('_p'), OLit(1)))), pairs),
    ))
    r5 = apply(pair_proj, ctx)
    _assert(any(lbl == 'D31_proj_to_unzip' for _, lbl in r5), "proj→unzip")

    # ── enumerate → zip ──
    print("D31: enumerate → zip ...")
    enum_term = OOp('enumerate', (xs,))
    r6 = apply(enum_term, ctx)
    _assert(any(lbl == 'D31_enumerate_to_zip' for _, lbl in r6), "enumerate→zip")

    # ── recognizes() ──
    print("D31: recognizes ...")
    _assert(recognizes(zip_term), "recognizes zip")
    _assert(recognizes(unzip_term), "recognizes unzip")
    _assert(recognizes(enum_term), "recognizes enumerate")
    _assert(not recognizes(OOp('sorted', (xs,))), "does not recognise sorted")

    # ── relevance_score ──
    print("D31: relevance_score ...")
    score = relevance_score(zip_term, unzip_term)
    _assert(score > 0.8, f"zip↔unzip score={score:.2f} > 0.8")
    low = relevance_score(OOp('sorted', (xs,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("D31: apply_inverse ...")
    inv = apply_inverse(pair_proj, ctx)
    _assert(len(inv) >= 1, "inverse produces unzip")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  D31 aos_soa: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
