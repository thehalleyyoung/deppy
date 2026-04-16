"""D28: Loop Fusion — Multiple Passes ↔ Single Pass.

§25.4 of the CCTT monograph.  Theorem 25.4.1:
Two independent traversals of the same collection can be fused
into a single traversal producing a tuple of results.

Key rewrites:
  • Horizontal map fusion:
    map(f, xs), map(g, xs) ↔ unzip(map(λx.(f(x),g(x)), xs))
  • Fold fusion:
    fold(op1, b1, xs), fold(op2, b2, xs)
    ↔ fold(λ(a1,a2),x.(op1(a1,x), op2(a2,x)), (b1,b2), xs)
  • Map-fold fusion (vertical):
    fold(op, base, map(f, xs)) ↔ fold(λa,x.op(a, f(x)), base, xs)
  • Map-map fusion (vertical):
    map(f, map(g, xs)) ↔ map(f∘g, xs)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "D28_loop_fusion"
AXIOM_CATEGORY = "control_flow"

SOUNDNESS_PROOF = r"""
Theorem 25.4.1 (Loop Fusion).

1. Horizontal map fusion:
   Let f, g : A → B, xs : [A].
   map(f, xs), map(g, xs) = unzip(map(λx.(f(x),g(x)), xs))
   Proof: both sides produce the same pair of lists by element-wise
   computation. By the universal property of products in Set^[A],
   the unique map into the product is λx.(f(x), g(x)).

2. Fold fusion:
   fold(op₁, b₁, xs), fold(op₂, b₂, xs)
   = fold(λ(a₁,a₂),x.(op₁(a₁,x), op₂(a₂,x)), (b₁,b₂), xs)
   Proof by induction on |xs|:
     Base: (b₁, b₂) = (b₁, b₂) ✓
     Step: the fused op applies op₁ and op₂ independently,
     which by IH equals running them separately.

3. Vertical map-fold fusion:
   fold(op, base, map(f, xs)) = fold(λa,x.op(a, f(x)), base, xs)
   This is the "deforestation" principle: the intermediate list
   map(f, xs) is never materialized.

4. Vertical map-map fusion:
   map(f, map(g, xs)) = map(f∘g, xs)
   Proof: (f∘g)(x) = f(g(x)) for each x; eliminates intermediate list.  □
"""

COMPOSES_WITH = ["D4_comp_fusion", "D5_fold_universal", "D25_loop_unroll", "D29_loop_fission"]
REQUIRES: List[str] = []

EXAMPLES = [
    {
        "name": "map_map_vertical",
        "before": "map(f, map(g, xs))",
        "after": "map(compose(f, g), xs)",
        "benchmark": None,
    },
    {
        "name": "map_fold_vertical",
        "before": "fold(add, 0, map(f, xs))",
        "after": "fold(λa,x.add(a, f(x)), 0, xs)",
        "benchmark": None,
    },
    {
        "name": "horizontal_map_fusion",
        "before": "OSeq(map(f, xs), map(g, xs))",
        "after": "unzip(map(λx.(f(x),g(x)), xs))",
        "benchmark": None,
    },
]


@dataclass
class FiberCtx:
    param_duck_types: Dict[str, str] = field(default_factory=dict)

    def is_numeric(self, term: OTerm) -> bool:
        return True


def _collections_match(a: OTerm, b: OTerm) -> bool:
    """Check if two terms refer to the same collection."""
    return a.canon() == b.canon()


def _subst_var(term: OTerm, name: str, replacement: OTerm) -> OTerm:
    """Substitute variable *name* with *replacement* in *term*."""
    if isinstance(term, OVar):
        return replacement if term.name == name else term
    if isinstance(term, (OLit, OUnknown)):
        return term
    if isinstance(term, OOp):
        return OOp(term.name, tuple(_subst_var(a, name, replacement) for a in term.args))
    if isinstance(term, OLam):
        if name in term.params:
            return term
        return OLam(term.params, _subst_var(term.body, name, replacement))
    if isinstance(term, OCase):
        return OCase(
            _subst_var(term.test, name, replacement),
            _subst_var(term.true_branch, name, replacement),
            _subst_var(term.false_branch, name, replacement),
        )
    if isinstance(term, OFold):
        return OFold(term.op_name, _subst_var(term.init, name, replacement),
                     _subst_var(term.collection, name, replacement))
    if isinstance(term, OSeq):
        return OSeq(tuple(_subst_var(e, name, replacement) for e in term.elements))
    if isinstance(term, OMap):
        filt = term.filter_pred
        if filt is not None:
            filt = _subst_var(filt, name, replacement)
        return OMap(_subst_var(term.transform, name, replacement),
                    _subst_var(term.collection, name, replacement), filt)
    if isinstance(term, OCatch):
        return OCatch(_subst_var(term.body, name, replacement),
                      _subst_var(term.default, name, replacement))
    return term


def _extract_lambda_body(transform: OTerm, param: str, arg: OTerm) -> Optional[OTerm]:
    """If transform is OLam, substitute param with arg and return body."""
    if isinstance(transform, OLam) and len(transform.params) == 1:
        return _subst_var(transform.body, transform.params[0], arg)
    return None


# ═══════════════════════════════════════════════════════════
# Core axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D28 loop fusion rewrites to *term*.

    Handles:
      1. Vertical map-map fusion: map(f, map(g, xs)) → map(f∘g, xs)
      2. Vertical map-fold fusion (deforestation):
         fold(op, base, map(f, xs)) → fold(λa,x.op(a,f(x)), base, xs)
      3. Horizontal map fusion: OSeq(map(f,xs), map(g,xs))
         → unzip(map(λx.(f(x),g(x)), xs))
      4. Horizontal fold fusion: OSeq(fold(op1,b1,xs), fold(op2,b2,xs))
         → fused fold with tuple accumulator
      5. Filter-map fusion: map(f, filter(p, xs)) → filter_map(p, f, xs)
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── 1. Vertical map-map fusion: map(f, map(g, xs)) → map(f∘g, xs) ──
    if isinstance(term, OMap) and isinstance(term.collection, OMap):
        inner = term.collection
        if inner.filter_pred is None and term.filter_pred is None:
            f_xf = term.transform
            g_xf = inner.transform
            if isinstance(f_xf, OLam) and isinstance(g_xf, OLam):
                # f∘g = λx. f(g(x))
                x_param = g_xf.params[0]
                g_body = g_xf.body
                f_param = f_xf.params[0]
                composed_body = _subst_var(f_xf.body, f_param, g_body)
                composed = OLam((x_param,), composed_body)
                results.append((
                    OMap(composed, inner.collection),
                    'D28_map_map_fuse',
                ))
            else:
                results.append((
                    OMap(OOp('compose', (f_xf, g_xf)), inner.collection),
                    'D28_map_map_fuse_opaque',
                ))

    # ── 2. Vertical map-fold fusion (deforestation) ──
    #    fold(op, base, map(f, xs)) → fold(op', base, xs)
    #    where op' = λ(a, x). op(a, f(x))
    if isinstance(term, OFold) and isinstance(term.collection, OMap):
        inner_map = term.collection
        if inner_map.filter_pred is None:
            f_xf = inner_map.transform
            if isinstance(f_xf, OLam) and len(f_xf.params) == 1:
                # Build: λ(a, x). op_name(a, f(x))
                f_body = f_xf.body
                fused_body = OOp(term.op_name, (OVar('_a'), f_body))
                fused_lam = OLam(('_a', f_xf.params[0]), fused_body)
                results.append((
                    OFold('__fused__', term.init, inner_map.collection),
                    'D28_map_fold_fuse',
                ))
                # Also produce the more explicit form with the composed lambda
                results.append((
                    OOp('fold_with', (fused_lam, term.init, inner_map.collection)),
                    'D28_map_fold_fuse_explicit',
                ))

    # ── 3. Horizontal map fusion: OSeq(map(f,xs), map(g,xs)) ──
    if isinstance(term, OSeq) and len(term.elements) >= 2:
        maps: List[Tuple[int, OMap]] = []
        for i, e in enumerate(term.elements):
            if isinstance(e, OMap) and e.filter_pred is None:
                maps.append((i, e))

        if len(maps) >= 2:
            # Group maps by collection
            from collections import defaultdict
            by_coll: Dict[str, List[Tuple[int, OMap]]] = defaultdict(list)
            for idx, m in maps:
                by_coll[m.collection.canon()].append((idx, m))

            for coll_key, group in by_coll.items():
                if len(group) >= 2:
                    collection = group[0][1].collection
                    transforms = [m.transform for _, m in group]
                    # Build fused lambda: λx. (f(x), g(x), ...)
                    param = '_x'
                    bodies: List[OTerm] = []
                    for xf in transforms:
                        if isinstance(xf, OLam) and len(xf.params) == 1:
                            bodies.append(_subst_var(xf.body, xf.params[0], OVar(param)))
                        else:
                            bodies.append(OOp('__call__', (xf, OVar(param))))
                    fused_lam = OLam((param,), OSeq(tuple(bodies)))
                    results.append((
                        OOp('unzip', (OMap(fused_lam, collection),)),
                        'D28_horizontal_map_fuse',
                    ))

    # ── 4. Horizontal fold fusion: OSeq(fold(op1,b1,xs), fold(op2,b2,xs)) ──
    if isinstance(term, OSeq) and len(term.elements) >= 2:
        folds: List[Tuple[int, OFold]] = []
        for i, e in enumerate(term.elements):
            if isinstance(e, OFold):
                folds.append((i, e))

        if len(folds) >= 2:
            from collections import defaultdict
            by_coll_f: Dict[str, List[Tuple[int, OFold]]] = defaultdict(list)
            for idx, f in folds:
                by_coll_f[f.collection.canon()].append((idx, f))

            for coll_key, group in by_coll_f.items():
                if len(group) >= 2:
                    collection = group[0][1].collection
                    inits = OSeq(tuple(f.init for _, f in group))
                    op_names = [f.op_name for _, f in group]
                    fused_name = '+'.join(op_names)
                    results.append((
                        OFold(fused_name, inits, collection),
                        'D28_horizontal_fold_fuse',
                    ))

    # ── 5. Filter-map fusion: map(f, filter_map(p, id, xs)) → filter_map(p, f, xs) ──
    if isinstance(term, OMap) and term.filter_pred is None:
        inner = term.collection
        if isinstance(inner, OMap) and inner.filter_pred is not None:
            results.append((
                OMap(term.transform, inner.collection, inner.filter_pred),
                'D28_filter_map_fuse',
            ))

    # ── 6. map(f∘g, xs) → map(f, map(g, xs))  [vertical fission, inverse] ──
    if isinstance(term, OMap) and isinstance(term.transform, OOp):
        if term.transform.name == 'compose' and len(term.transform.args) == 2:
            f, g = term.transform.args
            results.append((
                OMap(f, OMap(g, term.collection)),
                'D28_map_defuse_compose',
            ))

    return results


def recognizes(term: OTerm) -> bool:
    """Quick check: could D28 apply to this term?"""
    # Vertical: map over map, fold over map
    if isinstance(term, OMap) and isinstance(term.collection, OMap):
        return True
    if isinstance(term, OFold) and isinstance(term.collection, OMap):
        return True
    # Horizontal: sequence containing multiple maps/folds
    if isinstance(term, OSeq) and len(term.elements) >= 2:
        n_maps = sum(1 for e in term.elements if isinstance(e, OMap))
        n_folds = sum(1 for e in term.elements if isinstance(e, OFold))
        if n_maps >= 2 or n_folds >= 2:
            return True
    # Composed map transform
    if isinstance(term, OMap) and isinstance(term.transform, OOp):
        if term.transform.name == 'compose':
            return True
    # filter-map
    if isinstance(term, OMap) and isinstance(term.collection, OMap):
        if term.collection.filter_pred is not None:
            return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D28's relevance for bridging source → target."""
    sc = source.canon()
    tc = target.canon()
    s_multi = sc.count('map(') + sc.count('fold[')
    t_multi = tc.count('map(') + tc.count('fold[')

    # One has more traversals than other → fusion/fission likely needed
    if s_multi >= 2 and t_multi < s_multi:
        return 0.85
    if t_multi >= 2 and s_multi < t_multi:
        return 0.85
    # Compose in one, nested map in other
    if 'compose(' in sc and 'map(' in tc:
        return 0.7
    if 'compose(' in tc and 'map(' in sc:
        return 0.7
    if s_multi >= 2 or t_multi >= 2:
        return 0.5
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse of D28: split fused loops (→ D29 fission)."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # map(f∘g, xs) → map(f, map(g, xs))  (vertical defusion)
    if isinstance(term, OMap) and isinstance(term.transform, OLam):
        lam = term.transform
        if len(lam.params) == 1:
            x = lam.params[0]
            body = lam.body
            # Check if body = f(g(x)) pattern
            if isinstance(body, OOp) and len(body.args) == 1:
                inner = body.args[0]
                if isinstance(inner, OOp):
                    outer_lam = OLam(('_y',), OOp(body.name, (OVar('_y'),)))
                    inner_map = OMap(OLam((x,), inner), term.collection)
                    results.append((
                        OMap(outer_lam, inner_map),
                        'D28_inv_vertical_defuse',
                    ))

    # unzip(map(fused, xs)) → (map(f, xs), map(g, xs))  (horizontal defusion)
    if isinstance(term, OOp) and term.name == 'unzip' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OMap) and isinstance(inner.transform, OLam):
            lam = inner.transform
            if isinstance(lam.body, OSeq) and len(lam.body.elements) >= 2:
                param = lam.params[0]
                maps = []
                for component in lam.body.elements:
                    maps.append(OMap(OLam((param,), component), inner.collection))
                results.append((
                    OSeq(tuple(maps)),
                    'D28_inv_horizontal_defuse',
                ))

    return results


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

    ctx = FiberCtx()
    xs = OVar('xs')
    x = OVar('x')

    # 1. Vertical map-map fusion: map(f, map(g, xs)) → map(f∘g, xs)
    inner_map = OMap(OLam(('x',), OOp('g', (OVar('x'),))), xs)
    outer_map = OMap(OLam(('y',), OOp('f', (OVar('y'),))), inner_map)
    r1 = apply(outer_map, ctx)
    _assert(any(lbl == 'D28_map_map_fuse' for _, lbl in r1), "map-map vertical fuse")
    fused = [t for t, lbl in r1 if lbl == 'D28_map_map_fuse'][0]
    _assert(isinstance(fused, OMap) and not isinstance(fused.collection, OMap),
            "fused eliminates inner map")

    # 2. Vertical map-fold fusion: fold(add, 0, map(f, xs))
    map_term = OMap(OLam(('x',), OOp('double', (OVar('x'),))), xs)
    fold_over_map = OFold('add', OLit(0), map_term)
    r2 = apply(fold_over_map, ctx)
    _assert(any(lbl == 'D28_map_fold_fuse' for _, lbl in r2), "map-fold vertical fuse")

    # 3. Horizontal map fusion: [map(f, xs), map(g, xs)]
    m1 = OMap(OLam(('x',), OOp('f', (OVar('x'),))), xs)
    m2 = OMap(OLam(('x',), OOp('g', (OVar('x'),))), xs)
    seq_maps = OSeq((m1, m2))
    r3 = apply(seq_maps, ctx)
    _assert(any(lbl == 'D28_horizontal_map_fuse' for _, lbl in r3),
            "horizontal map fuse")

    # 4. Horizontal fold fusion: [fold(add, 0, xs), fold(mul, 1, xs)]
    f1 = OFold('add', OLit(0), xs)
    f2 = OFold('mul', OLit(1), xs)
    seq_folds = OSeq((f1, f2))
    r4 = apply(seq_folds, ctx)
    _assert(any(lbl == 'D28_horizontal_fold_fuse' for _, lbl in r4),
            "horizontal fold fuse")

    # 5. Map defuse compose: map(compose(f, g), xs) → map(f, map(g, xs))
    compose_map = OMap(OOp('compose', (OOp('f', ()), OOp('g', ()))), xs)
    r5 = apply(compose_map, ctx)
    _assert(any(lbl == 'D28_map_defuse_compose' for _, lbl in r5),
            "map defuse compose")

    # 6. Filter-map fusion
    filtered = OMap(OLam(('x',), OVar('x')), xs,
                    filter_pred=OLam(('x',), OOp('gt', (OVar('x'), OLit(0)))))
    outer_filtered = OMap(OLam(('x',), OOp('double', (OVar('x'),))), filtered)
    r6 = apply(outer_filtered, ctx)
    _assert(any(lbl == 'D28_filter_map_fuse' for _, lbl in r6), "filter-map fuse")

    # 7. Recognizes
    _assert(recognizes(outer_map), "recognizes map-over-map")
    _assert(recognizes(fold_over_map), "recognizes fold-over-map")
    _assert(recognizes(seq_maps), "recognizes seq of maps")
    _assert(recognizes(compose_map), "recognizes compose map")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # 8. Relevance
    _assert(relevance_score(outer_map, m1) > 0.5,
            "high relevance nested→flat")

    # 9. Inverse: unzip(map(fused, xs)) → [map(f, xs), map(g, xs)]
    fused_lam = OLam(('x',), OSeq((OOp('f', (OVar('x'),)), OOp('g', (OVar('x'),)))))
    unzip_term = OOp('unzip', (OMap(fused_lam, xs),))
    r9 = apply_inverse(unzip_term, ctx)
    _assert(any(lbl == 'D28_inv_horizontal_defuse' for _, lbl in r9),
            "inverse horizontal defuse")

    # 10. Inverse: vertical defuse map(λy.f(g(y)), xs) → map(f, map(g, xs))
    fused_vert = OMap(OLam(('y',), OOp('f', (OOp('g', (OVar('y'),)),))), xs)
    r10 = apply_inverse(fused_vert, ctx)
    _assert(any(lbl == 'D28_inv_vertical_defuse' for _, lbl in r10),
            "inverse vertical defuse")

    # 11. Non-matching collections don't fuse
    other_xs = OVar('ys')
    m_diff = OMap(OLam(('x',), OOp('g', (OVar('x'),))), other_xs)
    seq_diff = OSeq((m1, m_diff))
    r11 = apply(seq_diff, ctx)
    _assert(not any(lbl == 'D28_horizontal_map_fuse' for _, lbl in r11),
            "different collections don't fuse")

    print(f"D28 loop-fusion: {_pass} passed, {_fail} failed")
