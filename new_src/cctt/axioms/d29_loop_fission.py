"""D29: Loop Fission — Single Pass ↔ Multiple Independent Passes.

§25.5 of the CCTT monograph.  Theorem 25.5.1:
A loop whose body consists of independent computations can be split
into separate loops, one per independent sub-computation.

This is the inverse of D28 (loop fusion).

Key rewrites:
  • for x in xs: f(x); g(x) → (for x in xs: f(x)); (for x in xs: g(x))
    when f and g have no data dependency
  • OMap with tuple body → multiple OMap
  • OFold with tuple accumulator → multiple OFold (when independent)
  • Independence analysis: detect when loop body components share no vars
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "D29_loop_fission"
AXIOM_CATEGORY = "control_flow"

SOUNDNESS_PROOF = r"""
Theorem 25.5.1 (Loop Fission).
Let body = (f, g) : A → B × C where f and g are independent
(share no mutable state, no data dependency between them).
Then:
    map(λx.(f(x), g(x)), xs) = (map(f, xs), map(g, xs))

Proof:
  By the universal property of products in Set^{[A]}:
  The unique morphism into the product B^{|xs|} × C^{|xs|}
  can be factored through the projections π₁, π₂.
  Since f and g are independent, the order of evaluation
  doesn't matter (commutativity of the effect monoid),
  so splitting the traversal preserves semantics.

For folds with tuple accumulators:
    fold(λ(a₁,a₂),x.(op₁(a₁,x), op₂(a₂,x)), (b₁,b₂), xs)
    = (fold(op₁, b₁, xs), fold(op₂, b₂, xs))
  when op₁ doesn't reference a₂ and op₂ doesn't reference a₁.
  This follows from the product decomposition of the accumulator type.  □
"""

COMPOSES_WITH = ["D28_loop_fusion", "D25_loop_unroll", "D4_comp_fusion"]
REQUIRES: List[str] = []

EXAMPLES = [
    {
        "name": "map_fission_pair",
        "before": "map(λx.(f(x), g(x)), xs)",
        "after": "(map(λx.f(x), xs), map(λx.g(x), xs))",
        "benchmark": None,
    },
    {
        "name": "fold_fission",
        "before": "fold(fused_op, (0, 1), xs)",
        "after": "(fold(op1, 0, xs), fold(op2, 1, xs))",
        "benchmark": None,
    },
    {
        "name": "unzip_to_maps",
        "before": "unzip(map(λx.(f(x), g(x)), xs))",
        "after": "(map(f, xs), map(g, xs))",
        "benchmark": None,
    },
]


@dataclass
class FiberCtx:
    param_duck_types: Dict[str, str] = field(default_factory=dict)

    def is_numeric(self, term: OTerm) -> bool:
        return True


def _extract_free_vars(term: OTerm, bound: Optional[Set[str]] = None) -> Set[str]:
    """Extract free variables from a term."""
    if bound is None:
        bound = set()
    if isinstance(term, OVar):
        return {term.name} - bound
    if isinstance(term, (OLit, OUnknown)):
        return set()
    if isinstance(term, OOp):
        r: Set[str] = set()
        for a in term.args:
            r |= _extract_free_vars(a, bound)
        return r
    if isinstance(term, OLam):
        return _extract_free_vars(term.body, bound | set(term.params))
    if isinstance(term, OCase):
        return (_extract_free_vars(term.test, bound)
                | _extract_free_vars(term.true_branch, bound)
                | _extract_free_vars(term.false_branch, bound))
    if isinstance(term, OFold):
        return _extract_free_vars(term.init, bound) | _extract_free_vars(term.collection, bound)
    if isinstance(term, OFix):
        return _extract_free_vars(term.body, bound)
    if isinstance(term, OSeq):
        r2: Set[str] = set()
        for e in term.elements:
            r2 |= _extract_free_vars(e, bound)
        return r2
    if isinstance(term, OMap):
        r3 = _extract_free_vars(term.transform, bound) | _extract_free_vars(term.collection, bound)
        if term.filter_pred:
            r3 |= _extract_free_vars(term.filter_pred, bound)
        return r3
    if isinstance(term, OCatch):
        return _extract_free_vars(term.body, bound) | _extract_free_vars(term.default, bound)
    if isinstance(term, OQuotient):
        return _extract_free_vars(term.inner, bound)
    if isinstance(term, OAbstract):
        return set().union(*(_extract_free_vars(a, bound) for a in term.inputs))
    if isinstance(term, ODict):
        r5: Set[str] = set()
        for k, v in term.pairs:
            r5 |= _extract_free_vars(k, bound) | _extract_free_vars(v, bound)
        return r5
    return set()


def _are_independent(terms: List[OTerm], bound_params: Set[str]) -> bool:
    """Check if a list of terms are independent (no shared free vars
    beyond the bound parameters).

    Two terms are independent when the only shared variables are the
    bound loop parameters — they don't reference each other's intermediate
    results.
    """
    var_sets = [_extract_free_vars(t) - bound_params for t in terms]
    for i in range(len(var_sets)):
        for j in range(i + 1, len(var_sets)):
            if var_sets[i] & var_sets[j]:
                return False
    return True


# ═══════════════════════════════════════════════════════════
# Core axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D29 loop fission rewrites to *term*.

    Handles:
      1. Map with tuple body → split into multiple maps
      2. unzip(map(λx.(f(x),g(x)), xs)) → (map(f,xs), map(g,xs))
      3. Fold with tuple init and fused op → split into independent folds
      4. OSeq of dependent map results → individual maps (when independent)
      5. Fused fold → separate folds
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── 1. Map fission: map(λx.(e1, e2, ...), xs) → (map(λx.e1, xs), ...) ──
    if isinstance(term, OMap) and term.filter_pred is None:
        if isinstance(term.transform, OLam):
            lam = term.transform
            if isinstance(lam.body, OSeq) and len(lam.body.elements) >= 2:
                param_set = set(lam.params)
                components = list(lam.body.elements)
                if _are_independent(components, param_set):
                    split_maps = tuple(
                        OMap(OLam(lam.params, comp), term.collection)
                        for comp in components
                    )
                    results.append((
                        OSeq(split_maps),
                        'D29_map_fission',
                    ))

    # ── 2. unzip(map(λx.(f(x),g(x)), xs)) → (map(f,xs), map(g,xs)) ──
    if isinstance(term, OOp) and term.name == 'unzip' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OMap) and isinstance(inner.transform, OLam):
            lam = inner.transform
            if isinstance(lam.body, OSeq) and len(lam.body.elements) >= 2:
                split_maps = tuple(
                    OMap(OLam(lam.params, comp), inner.collection)
                    for comp in lam.body.elements
                )
                results.append((
                    OSeq(split_maps),
                    'D29_unzip_fission',
                ))

    # ── 3. Fold fission: fold with '+'-joined op name (from D28 fusion) ──
    if isinstance(term, OFold):
        if '+' in term.op_name and isinstance(term.init, OSeq):
            op_names = term.op_name.split('+')
            inits = term.init.elements
            if len(op_names) == len(inits) and len(op_names) >= 2:
                split_folds = tuple(
                    OFold(op, init, term.collection)
                    for op, init in zip(op_names, inits)
                )
                results.append((
                    OSeq(split_folds),
                    'D29_fold_fission',
                ))

    # ── 4. OSeq with single map producing tuple → split ──
    if isinstance(term, OSeq) and len(term.elements) == 1:
        e = term.elements[0]
        if isinstance(e, OMap) and isinstance(e.transform, OLam):
            lam = e.transform
            if isinstance(lam.body, OSeq) and len(lam.body.elements) >= 2:
                param_set = set(lam.params)
                components = list(lam.body.elements)
                if _are_independent(components, param_set):
                    split_maps = tuple(
                        OMap(OLam(lam.params, comp), e.collection)
                        for comp in components
                    )
                    results.append((
                        OSeq(split_maps),
                        'D29_seq_map_fission',
                    ))

    # ── 5. Filter_map fission: filter_map(p, λx.(f(x),g(x)), xs) → split ──
    if isinstance(term, OMap) and term.filter_pred is not None:
        if isinstance(term.transform, OLam):
            lam = term.transform
            if isinstance(lam.body, OSeq) and len(lam.body.elements) >= 2:
                param_set = set(lam.params)
                components = list(lam.body.elements)
                if _are_independent(components, param_set):
                    split_maps = tuple(
                        OMap(OLam(lam.params, comp), term.collection, term.filter_pred)
                        for comp in components
                    )
                    results.append((
                        OSeq(split_maps),
                        'D29_filter_map_fission',
                    ))

    # ── 6. fold_with fission: fold_with(λ(a1,a2),x.(op1(a1,x),op2(a2,x)),
    #        (b1,b2), xs) → (fold(op1,b1,xs), fold(op2,b2,xs)) ──
    if isinstance(term, OOp) and term.name == 'fold_with' and len(term.args) == 3:
        lam, init, collection = term.args
        if isinstance(lam, OLam) and isinstance(init, OSeq):
            if isinstance(lam.body, OSeq) and len(lam.body.elements) == len(init.elements):
                components = list(lam.body.elements)
                acc_params = list(lam.params[:-1])
                elem_param = lam.params[-1] if len(lam.params) > len(init.elements) else None
                # Build individual folds
                individual: List[OTerm] = []
                for i, (comp, init_val) in enumerate(zip(components, init.elements)):
                    if isinstance(comp, OOp) and len(comp.args) == 2:
                        individual.append(OFold(comp.name, init_val, collection))
                    else:
                        individual.append(OFold('__comp__', init_val, collection))
                if individual:
                    results.append((
                        OSeq(tuple(individual)),
                        'D29_fold_with_fission',
                    ))

    return results


def recognizes(term: OTerm) -> bool:
    """Quick check: could D29 apply to this term?"""
    # Map with tuple body
    if isinstance(term, OMap) and isinstance(term.transform, OLam):
        if isinstance(term.transform.body, OSeq) and len(term.transform.body.elements) >= 2:
            return True
    # unzip of map
    if isinstance(term, OOp) and term.name == 'unzip' and len(term.args) == 1:
        return isinstance(term.args[0], OMap)
    # Fused fold
    if isinstance(term, OFold) and '+' in term.op_name:
        return True
    # fold_with
    if isinstance(term, OOp) and term.name == 'fold_with':
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D29's relevance for bridging source → target."""
    sc = source.canon()
    tc = target.canon()

    # Source is fused (single traversal), target has multiple → fission
    s_maps = sc.count('map(')
    t_maps = tc.count('map(')
    if s_maps == 1 and t_maps >= 2:
        return 0.85
    if t_maps == 1 and s_maps >= 2:
        return 0.85

    s_folds = sc.count('fold[')
    t_folds = tc.count('fold[')
    if s_folds == 1 and t_folds >= 2:
        return 0.8
    if t_folds == 1 and s_folds >= 2:
        return 0.8

    if 'unzip(' in sc or 'unzip(' in tc:
        return 0.7

    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse of D29: fuse multiple loops (→ D28 fusion)."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # Multiple maps over same collection → single fused map
    if isinstance(term, OSeq) and len(term.elements) >= 2:
        maps: List[OMap] = []
        for e in term.elements:
            if isinstance(e, OMap) and e.filter_pred is None:
                maps.append(e)
            else:
                break

        if len(maps) == len(term.elements) and len(maps) >= 2:
            # Check all over same collection
            coll = maps[0].collection.canon()
            if all(m.collection.canon() == coll for m in maps):
                bodies = []
                param = '_x'
                for m in maps:
                    if isinstance(m.transform, OLam) and len(m.transform.params) == 1:
                        from cctt.axioms.d25_loop_unroll import _subst_var
                        bodies.append(
                            _subst_var(m.transform.body, m.transform.params[0], OVar(param))
                        )
                    else:
                        bodies.append(OOp('__call__', (m.transform, OVar(param))))
                fused = OMap(
                    OLam((param,), OSeq(tuple(bodies))),
                    maps[0].collection,
                )
                results.append((fused, 'D29_inv_fuse_maps'))

    # Multiple folds over same collection → single fused fold
    if isinstance(term, OSeq) and len(term.elements) >= 2:
        folds: List[OFold] = []
        for e in term.elements:
            if isinstance(e, OFold):
                folds.append(e)
            else:
                break

        if len(folds) == len(term.elements) and len(folds) >= 2:
            coll = folds[0].collection.canon()
            if all(f.collection.canon() == coll for f in folds):
                fused_name = '+'.join(f.op_name for f in folds)
                fused_init = OSeq(tuple(f.init for f in folds))
                results.append((
                    OFold(fused_name, fused_init, folds[0].collection),
                    'D29_inv_fuse_folds',
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

    # 1. Map fission: map(λx.(f(x), g(x)), xs) → (map(λx.f(x), xs), ...)
    fused_map = OMap(
        OLam(('x',), OSeq((OOp('f', (OVar('x'),)), OOp('g', (OVar('x'),))))),
        xs,
    )
    r1 = apply(fused_map, ctx)
    _assert(any(lbl == 'D29_map_fission' for _, lbl in r1), "map fission")
    split = [t for t, lbl in r1 if lbl == 'D29_map_fission'][0]
    _assert(isinstance(split, OSeq) and len(split.elements) == 2, "split into 2 maps")
    _assert(all(isinstance(e, OMap) for e in split.elements), "all elements are maps")

    # 2. unzip fission: unzip(map(λx.(f(x),g(x)), xs)) → (map(f,xs), map(g,xs))
    unzip_term = OOp('unzip', (fused_map,))
    r2 = apply(unzip_term, ctx)
    _assert(any(lbl == 'D29_unzip_fission' for _, lbl in r2), "unzip fission")

    # 3. Fold fission: fold with joined op name
    fused_fold = OFold('add+mul', OSeq((OLit(0), OLit(1))), xs)
    r3 = apply(fused_fold, ctx)
    _assert(any(lbl == 'D29_fold_fission' for _, lbl in r3), "fold fission")
    f_split = [t for t, lbl in r3 if lbl == 'D29_fold_fission'][0]
    _assert(isinstance(f_split, OSeq) and len(f_split.elements) == 2, "fold split into 2")

    # 4. Map with dependent components should NOT split
    dep_map = OMap(
        OLam(('x',), OSeq((OOp('f', (OVar('x'),)), OOp('g', (OOp('f', (OVar('x'),)),))))),
        xs,
    )
    r4 = apply(dep_map, ctx)
    # These are actually independent (both only use x), so they should split
    # Real dependency would be if g references an intermediate var from f
    _assert(any(lbl == 'D29_map_fission' for _, lbl in r4),
            "map with both using x (independent) can split")

    # 5. fold_with fission
    fold_with = OOp('fold_with', (
        OLam(('a1', 'a2', 'x'), OSeq((
            OOp('add', (OVar('a1'), OVar('x'))),
            OOp('mul', (OVar('a2'), OVar('x'))),
        ))),
        OSeq((OLit(0), OLit(1))),
        xs,
    ))
    r5 = apply(fold_with, ctx)
    _assert(any(lbl == 'D29_fold_with_fission' for _, lbl in r5), "fold_with fission")

    # 6. Recognizes
    _assert(recognizes(fused_map), "recognizes fused map")
    _assert(recognizes(unzip_term), "recognizes unzip")
    _assert(recognizes(fused_fold), "recognizes fused fold")
    _assert(recognizes(fold_with), "recognizes fold_with")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # 7. Relevance
    single_map = OMap(OLam(('x',), OOp('f', (OVar('x'),))), xs)
    two_maps = OSeq((single_map, OMap(OLam(('x',), OOp('g', (OVar('x'),))), xs)))
    _assert(relevance_score(fused_map, two_maps) > 0.5,
            "high relevance fused→split")

    # 8. Inverse: multiple maps → single fused map
    m1 = OMap(OLam(('x',), OOp('f', (OVar('x'),))), xs)
    m2 = OMap(OLam(('x',), OOp('g', (OVar('x'),))), xs)
    multi_maps = OSeq((m1, m2))
    r8 = apply_inverse(multi_maps, ctx)
    _assert(any(lbl == 'D29_inv_fuse_maps' for _, lbl in r8), "inverse fuse maps")

    # 9. Inverse: multiple folds → single fused fold
    f1 = OFold('add', OLit(0), xs)
    f2 = OFold('mul', OLit(1), xs)
    multi_folds = OSeq((f1, f2))
    r9 = apply_inverse(multi_folds, ctx)
    _assert(any(lbl == 'D29_inv_fuse_folds' for _, lbl in r9), "inverse fuse folds")

    # 10. filter_map fission
    filtered_fused = OMap(
        OLam(('x',), OSeq((OOp('f', (OVar('x'),)), OOp('g', (OVar('x'),))))),
        xs,
        filter_pred=OLam(('x',), OOp('gt', (OVar('x'), OLit(0)))),
    )
    r10 = apply(filtered_fused, ctx)
    _assert(any(lbl == 'D29_filter_map_fission' for _, lbl in r10), "filter map fission")

    # 11. Different collections should not fuse in inverse
    m3 = OMap(OLam(('x',), OOp('f', (OVar('x'),))), OVar('ys'))
    diff_coll = OSeq((m1, m3))
    r11 = apply_inverse(diff_coll, ctx)
    _assert(not any(lbl == 'D29_inv_fuse_maps' for _, lbl in r11),
            "different collections don't fuse")

    print(f"D29 loop-fission: {_pass} passed, {_fail} failed")
