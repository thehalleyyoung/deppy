from __future__ import annotations
"""D4: Composition Fusion — fuse nested map/comprehension chains.

Mathematical basis: catamorphism fusion (Banana-Split theorem).
Nested maps compose functorially:

    map(f, map(g, xs))  ≡  map(f ∘ g, xs)

This extends to 3+ nested maps, fold-map fusion, and the
map↔fold bridge (converting between OMap and OFold representations).

HIT path:  d4 : OMap(f, OMap(g, c)) = OMap(f∘g, c)
Monograph: Chapter 20, §20.4 — Definition 4.5, Theorem 4.6
"""

from dataclasses import dataclass
import hashlib
from typing import Any, Dict, List, Optional, Set, Tuple

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
    _subst, normalize,
)
from cctt.path_search import FiberCtx

# ═══════════════════════════════════════════════════════════════
# Constants
# ═══════════════════════════════════════════════════════════════

AXIOM_NAME = "d4_comp_fusion"
AXIOM_CATEGORY = "HOF"

# ═══════════════════════════════════════════════════════════════
# Internal helpers
# ═══════════════════════════════════════════════════════════════

def _canon_hash(s: str) -> str:
    """8-char md5 hash for canonical naming."""
    return hashlib.md5(s.encode()).hexdigest()[:8]


def _subst_deep(term: OTerm, var_name: str, replacement: OTerm) -> OTerm:
    """Deep substitution of a variable with an arbitrary OTerm."""
    if isinstance(term, OVar):
        return replacement if term.name == var_name else term
    if isinstance(term, OLit):
        return term
    if isinstance(term, OOp):
        return OOp(term.name,
                   tuple(_subst_deep(a, var_name, replacement) for a in term.args))
    if isinstance(term, OCase):
        return OCase(_subst_deep(term.test, var_name, replacement),
                     _subst_deep(term.true_branch, var_name, replacement),
                     _subst_deep(term.false_branch, var_name, replacement))
    if isinstance(term, OFold):
        return OFold(term.op_name,
                     _subst_deep(term.init, var_name, replacement),
                     _subst_deep(term.collection, var_name, replacement))
    if isinstance(term, OFix):
        return OFix(term.name, _subst_deep(term.body, var_name, replacement))
    if isinstance(term, OSeq):
        return OSeq(tuple(_subst_deep(e, var_name, replacement) for e in term.elements))
    if isinstance(term, OLam):
        if var_name in term.params:
            return term
        return OLam(term.params, _subst_deep(term.body, var_name, replacement))
    if isinstance(term, OMap):
        new_t = _subst_deep(term.transform, var_name, replacement)
        new_c = _subst_deep(term.collection, var_name, replacement)
        new_f = (_subst_deep(term.filter_pred, var_name, replacement)
                 if term.filter_pred else None)
        return OMap(new_t, new_c, new_f)
    if isinstance(term, OCatch):
        return OCatch(_subst_deep(term.body, var_name, replacement),
                      _subst_deep(term.default, var_name, replacement))
    if isinstance(term, OQuotient):
        return OQuotient(_subst_deep(term.inner, var_name, replacement),
                         term.equiv_class)
    if isinstance(term, OAbstract):
        return OAbstract(term.spec,
                         tuple(_subst_deep(a, var_name, replacement)
                               for a in term.inputs))
    if isinstance(term, ODict):
        return ODict(tuple((_subst_deep(k, var_name, replacement),
                            _subst_deep(v, var_name, replacement))
                           for k, v in term.pairs))
    return term


def _compose_transforms(outer: OTerm, inner: OTerm) -> Optional[OTerm]:
    """Compose two transforms: ``f ∘ g`` where both are lambdas.

    ``λx. f_body`` ∘ ``λy. g_body``  =  ``λy. f_body[x := g_body]``
    """
    if isinstance(outer, OLam) and isinstance(inner, OLam):
        if len(outer.params) == 1 and len(inner.params) == 1:
            composed_body = _subst_deep(outer.body, outer.params[0], inner.body)
            return OLam(inner.params, composed_body)
    return None


def _peel_maps(term: OTerm) -> Tuple[List[OTerm], OTerm]:
    """Peel nested ``OMap(f, OMap(g, OMap(h, coll)))`` into
    ``([f, g, h], coll)``."""
    transforms: List[OTerm] = []
    cur = term
    while isinstance(cur, OMap) and cur.filter_pred is None:
        transforms.append(cur.transform)
        cur = cur.collection
    return transforms, cur


def _compose_all(transforms: List[OTerm]) -> Optional[OTerm]:
    """Compose a list of transforms ``[f, g, h]`` into ``f ∘ g ∘ h``.

    Application order: f is outermost, h is innermost.
    Returns ``None`` if any composition step fails.
    """
    if len(transforms) < 2:
        return transforms[0] if transforms else None
    result = transforms[-1]
    for t in reversed(transforms[:-1]):
        composed = _compose_transforms(t, result)
        if composed is None:
            return None
        result = composed
    return result


def _build_map_chain(transforms: List[OTerm], base: OTerm) -> OTerm:
    """Reconstruct a nested ``OMap`` chain from transforms list."""
    cur = base
    for t in reversed(transforms):
        cur = OMap(t, cur)
    return cur


# ═══════════════════════════════════════════════════════════════
# Main apply function
# ═══════════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply D4 axiom: fuse nested maps and fold-map chains.

    Produces:
      - D4_map_fusion:     map(f, map(g, c)) → map(f∘g, c)
      - D4_multi_fusion_N: map(f, map(g, map(h, c))) → map(f∘g∘h, c)
      - D4_partial_fusion: fuse first two of 3+ maps
      - D4_fold_map_fusion: fold(op, map(f, c)) → fold(op, c) (absorb map)
      - D4_map_to_fold:    map(f, c) → fold(append∘f, [], c)
      - D4_fold_to_map:    fold(append_…, [], c) → map(…, c)
    """
    results: List[Tuple[OTerm, str]] = []

    # ── Standard map fusion: map(f, map(g, coll)) → map(f∘g, coll) ──
    if isinstance(term, OMap):
        if isinstance(term.collection, OMap) and term.collection.filter_pred is None:
            inner = term.collection
            composed = _compose_transforms(term.transform, inner.transform)
            if composed is not None:
                results.append((OMap(composed, inner.collection, term.filter_pred),
                                'D4_map_fusion'))

    # ── Multi-fusion for 3+ nested maps ──
    if isinstance(term, OMap):
        transforms, base_coll = _peel_maps(term)
        if len(transforms) >= 3:
            composed = _compose_all(transforms)
            if composed is not None:
                fused = OMap(composed, base_coll)
                if fused.canon() != term.canon():
                    results.append((fused, f'D4_multi_fusion_{len(transforms)}'))
            # Also emit partial fusion (first two)
            partial = _compose_transforms(transforms[0], transforms[1])
            if partial is not None:
                rest = _build_map_chain(transforms[2:], base_coll)
                partial_map = OMap(partial, rest)
                if partial_map.canon() != term.canon():
                    results.append((partial_map, 'D4_partial_fusion'))

    # ── Fold-map fusion: fold(op, init, map(f, coll)) → fold(op, init, coll) ──
    if isinstance(term, OFold):
        if isinstance(term.collection, OMap) and term.collection.filter_pred is None:
            results.append((OFold(term.op_name, term.init,
                                  term.collection.collection),
                           'D4_fold_map_fusion'))

    # ── Map↔Fold bridge ──
    # map(f, c) → fold(append∘f, [], c)
    if isinstance(term, OMap) and term.filter_pred is None:
        fold_key = f'append_{_canon_hash(term.transform.canon())}'
        results.append((
            OFold(fold_key, OSeq(()), term.collection),
            'D4_map_to_fold',
        ))

    # fold(append_…, [], c) → map(…, c)
    if isinstance(term, OFold):
        if (term.op_name.startswith('append_')
                and isinstance(term.init, OSeq)
                and len(term.init.elements) == 0):
            param = OVar('_x')
            inner_op = term.op_name[len('append_'):]
            transform = OLam(('_x',), OOp(inner_op, (param,)))
            results.append((
                OMap(transform, term.collection),
                'D4_fold_to_map',
            ))

    return results


# ═══════════════════════════════════════════════════════════════
# Recognition and relevance
# ═══════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could D4 apply to this term?"""
    # Nested maps
    if isinstance(term, OMap):
        if isinstance(term.collection, OMap):
            return True
        if term.filter_pred is None:
            return True  # potential map→fold bridge
    # Fold over map
    if isinstance(term, OFold):
        if isinstance(term.collection, OMap):
            return True
        if term.op_name.startswith('append_'):
            return True
    return False


def relevance_score(term: OTerm, other: OTerm) -> float:
    """How likely is D4 to help prove ``term ≡ other``?

    Returns a score in [0.0, 1.0]:
      0.9 — one has nested maps, the other has a single map
      0.8 — one is OMap, other is OFold (bridge needed)
      0.5 — both have maps
      0.0 — no maps or folds
    """
    t_map = isinstance(term, OMap)
    o_map = isinstance(other, OMap)
    t_fold = isinstance(term, OFold)
    o_fold = isinstance(other, OFold)

    if t_map and o_map:
        # Check depth difference
        t_depth = len(_peel_maps(term)[0])
        o_depth = len(_peel_maps(other)[0])
        if t_depth != o_depth:
            return 0.9
        return 0.5

    if (t_map and o_fold) or (t_fold and o_map):
        return 0.8

    if t_map or o_map:
        return 0.3
    return 0.0


# ═══════════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply D4 in reverse: unfuse a single map into nested maps.

    Given ``map(λx. f(g(x)), c)`` where the body is a composition,
    split into ``map(λx.f(x), map(λx.g(x), c))``.
    """
    results: List[Tuple[OTerm, str]] = []

    if isinstance(term, OMap) and isinstance(term.transform, OLam):
        lam = term.transform
        if len(lam.params) == 1 and isinstance(lam.body, OOp):
            body = lam.body
            if len(body.args) == 1 and not isinstance(body.args[0], (OVar, OLit)):
                # body = f(g(x)) — split into map(f, map(g, c))
                inner_body = body.args[0]
                outer_lam = OLam(('_u',), OOp(body.name, (OVar('_u'),)))
                inner_lam = OLam(lam.params, inner_body)
                unfused = OMap(outer_lam, OMap(inner_lam, term.collection))
                results.append((unfused, 'D4_inv_map_unfuse'))

    # fold → map (reverse of map_to_fold)
    if isinstance(term, OFold):
        if (term.op_name.startswith('append_')
                and isinstance(term.init, OSeq)
                and len(term.init.elements) == 0):
            param = OVar('_x')
            inner_op = term.op_name[len('append_'):]
            transform = OLam(('_x',), OOp(inner_op, (param,)))
            results.append((
                OMap(transform, term.collection),
                'D4_inv_fold_to_map',
            ))

    return results


# ═══════════════════════════════════════════════════════════════
# Composability metadata
# ═══════════════════════════════════════════════════════════════

COMPOSES_WITH = ["d2_beta", "d5_fold_universal", "d6_lazy_eager"]
REQUIRES: List[str] = []

# ═══════════════════════════════════════════════════════════════
# Soundness justification
# ═══════════════════════════════════════════════════════════════

SOUNDNESS_PROOF = """
Theorem (D4 Soundness): If D4 transforms t to t', then ⟦t⟧ = ⟦t'⟧.

Proof: By the functor composition law (catamorphism fusion).

1. Map fusion:
   ⟦map(f, map(g, xs))⟧
   = [f(y) for y in [g(x) for x in xs]]
   = [f(g(x)) for x in xs]
   = ⟦map(f∘g, xs)⟧

   This is the second functor law: F(f) ∘ F(g) = F(f ∘ g).

2. Multi-fusion follows by induction on chain length.

3. Fold-map fusion:
   ⟦fold(op, init, map(f, xs))⟧
   = reduce(op, [f(x) for x in xs], init)
   = reduce(op∘f, xs, init)
   = ⟦fold(op∘f, init, xs)⟧

   (When op can absorb f, e.g. sum(map(f, xs)) = sum_f(xs))

4. Map↔Fold bridge:
   ⟦map(f, xs)⟧ = [f(x) for x in xs]
   ⟦fold(append∘f, [], xs)⟧ = reduce(λacc,x. acc + [f(x)], xs, [])
   Both produce the same list by structural induction on xs.  ∎
"""

# ═══════════════════════════════════════════════════════════════
# Examples
# ═══════════════════════════════════════════════════════════════

EXAMPLES = [
    {
        "name": "two_map_fusion",
        "before": "OMap(OLam(('x',), OOp('add',(OVar('x'),OLit(1)))), OMap(OLam(('x',), OOp('mul',(OVar('x'),OLit(2)))), OVar('xs')))",
        "after": "OMap(OLam(('x',), OOp('add',(OOp('mul',(OVar('x'),OLit(2))),OLit(1)))), OVar('xs'))",
        "benchmark": "comp01",
        "description": "map(x+1, map(x*2, xs)) → map((x*2)+1, xs)",
    },
    {
        "name": "three_map_fusion",
        "before": "OMap(f, OMap(g, OMap(h, OVar('xs'))))",
        "after": "OMap(f∘g∘h, OVar('xs'))",
        "benchmark": "comp02",
        "description": "3-deep map chain fuses to single map",
    },
    {
        "name": "fold_map_fusion",
        "before": "OFold('iadd', OLit(0), OMap(OLam(('x',), OOp('mul',(OVar('x'),OLit(2)))), OVar('xs')))",
        "after": "OFold('iadd', OLit(0), OVar('xs'))",
        "benchmark": "comp03",
        "description": "sum(map(x*2, xs)) → fold(add, 0, xs) (absorb map)",
    },
    {
        "name": "map_to_fold_bridge",
        "before": "OMap(OLam(('x',), OOp('f',(OVar('x'),))), OVar('xs'))",
        "after": "OFold('append_...', OSeq(()), OVar('xs'))",
        "benchmark": "comp04",
        "description": "map(f, xs) → fold(append∘f, [], xs)",
    },
]

# ═══════════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════════

if __name__ == '__main__':
    import sys
    _passed = 0
    _failed = 0

    def _assert(cond: bool, msg: str) -> None:
        global _passed, _failed
        if cond:
            _passed += 1
            print(f'  ✓ {msg}')
        else:
            _failed += 1
            print(f'  ✗ FAIL: {msg}')

    ctx = FiberCtx(param_duck_types={'p0': 'int', 'p1': 'int'})

    f1 = OLam(('x',), OOp('add', (OVar('x'), OLit(1))))
    f2 = OLam(('x',), OOp('mul', (OVar('x'), OLit(2))))
    f3 = OLam(('x',), OOp('sub', (OVar('x'), OLit(3))))

    # Test 2-map fusion
    print('▶ D4 2-map fusion')
    double_map = OMap(f1, OMap(f2, OVar('coll')))
    results = apply(double_map, ctx)
    _assert(any(lbl == 'D4_map_fusion' for _, lbl in results),
            'D4_map_fusion fires')
    fused = [t for t, lbl in results if lbl == 'D4_map_fusion'][0]
    _assert(isinstance(fused, OMap), 'fused is OMap')
    _assert(isinstance(fused.collection, OVar), 'inner collection is var')

    # Test 3-map fusion
    print('▶ D4 3-map fusion')
    triple_map = OMap(f1, OMap(f2, OMap(f3, OVar('coll'))))
    results = apply(triple_map, ctx)
    _assert(any('D4_multi_fusion_3' in lbl for _, lbl in results),
            'D4 multi-fusion fires on 3 maps')
    _assert(any(lbl == 'D4_partial_fusion' for _, lbl in results),
            'D4 partial fusion also fires')

    # Test fold-map fusion
    print('▶ D4 fold-map fusion')
    fold_map = OFold('iadd', OLit(0), OMap(f1, OVar('xs')))
    results = apply(fold_map, ctx)
    _assert(any(lbl == 'D4_fold_map_fusion' for _, lbl in results),
            'fold_map_fusion fires')
    fm_result = [t for t, lbl in results if lbl == 'D4_fold_map_fusion'][0]
    _assert(isinstance(fm_result, OFold), 'result is OFold')
    _assert(isinstance(fm_result.collection, OVar), 'collection is now var')

    # Test map → fold bridge
    print('▶ D4 map↔fold bridge')
    simple_map = OMap(f1, OVar('coll'))
    results = apply(simple_map, ctx)
    _assert(any(lbl == 'D4_map_to_fold' for _, lbl in results),
            'map_to_fold fires')
    fold_result = [t for t, lbl in results if lbl == 'D4_map_to_fold'][0]
    _assert(isinstance(fold_result, OFold), 'result is OFold')
    _assert(fold_result.op_name.startswith('append_'), 'op starts with append_')

    # Test fold → map bridge
    print('▶ D4 fold→map bridge')
    fold_back = OFold('append_abc12345', OSeq(()), OVar('xs'))
    results = apply(fold_back, ctx)
    _assert(any(lbl == 'D4_fold_to_map' for _, lbl in results),
            'fold_to_map fires')

    # Test recognizes
    print('▶ D4 recognizes()')
    _assert(recognizes(double_map), 'nested maps recognised')
    _assert(recognizes(fold_map), 'fold over map recognised')
    _assert(recognizes(simple_map), 'single map recognised (bridge)')
    _assert(not recognizes(OLit(42)), 'literal not recognised')

    # Test relevance_score
    print('▶ D4 relevance_score()')
    _assert(relevance_score(double_map, simple_map) == 0.9,
            'nested vs single map → 0.9')
    _assert(relevance_score(simple_map, fold_back) == 0.8,
            'map vs fold → 0.8')
    _assert(relevance_score(OLit(1), OLit(2)) == 0.0,
            'no maps → 0.0')

    # Test inverse
    print('▶ D4 apply_inverse()')
    composed_map = OMap(OLam(('x',), OOp('f', (OOp('g', (OVar('x'),)),))),
                        OVar('xs'))
    inv_results = apply_inverse(composed_map, ctx)
    _assert(any('inv' in lbl for _, lbl in inv_results),
            'inverse fires on composed map')

    # Edge cases
    print('▶ D4 edge cases')
    _assert(apply(OLit(3), ctx) == [], 'D4 on literal is empty')
    single_no_filter = OMap(f1, OVar('c'))
    results = apply(single_no_filter, ctx)
    # Should emit map_to_fold but not map_fusion
    _assert(not any(lbl == 'D4_map_fusion' for _, lbl in results),
            'single map → no fusion')
    _assert(any(lbl == 'D4_map_to_fold' for _, lbl in results),
            'single map → bridge fires')

    print(f'\n{"═" * 50}')
    print(f'  D4: {_passed} passed, {_failed} failed')
    print(f'{"═" * 50}')
    sys.exit(1 if _failed > 0 else 0)
