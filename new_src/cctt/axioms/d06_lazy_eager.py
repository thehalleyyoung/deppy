from __future__ import annotations
"""D6: Lazy ↔ Eager — evaluation strategy equivalence.

Mathematical basis: the laziness adjunction  L ⊣ E  between the
category of lazy computations and the category of eager values.
A generator expression and the equivalent list comprehension
produce the same observable results when the consumer is total.

This axiom handles:
  1. list(generator) ≡ comprehension (materialisation)
  2. Generator→fold equivalence (lazy accumulation)
  3. Loop interchange via fold-map commutation
  4. Iterator protocol equivalences (iter/next ↔ for)
  5. Lazy slicing: islice(gen, n) ≡ gen[:n]

HIT path:  d6 : list(gen(body)) = [body for x in coll]
Monograph: Chapter 20, §20.6
"""

from dataclasses import dataclass
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

AXIOM_NAME = "d6_lazy_eager"
AXIOM_CATEGORY = "effect"

# ═══════════════════════════════════════════════════════════════
# Fold op synonym table (needed for loop interchange)
# ═══════════════════════════════════════════════════════════════

_FOLD_OP_SYNONYMS: Dict[str, str] = {
    'add': 'iadd', '.add': 'iadd', 'operator.add': 'iadd',
    'mul': 'imul', '.mul': 'imul', 'operator.mul': 'imul',
    'mult': 'imul',
    'min': 'imin', 'max': 'imax',
    'or': 'ior', 'and': 'iand',
}


def _canonicalize_op(name: str) -> str:
    return _FOLD_OP_SYNONYMS.get(name, name)


# Pairs of fold operations where loop interchange is valid
# (op1 distributes over op2, so order doesn't matter)
_DISTRIBUTIVE_PAIRS = frozenset({
    ('iadd', 'iadd'), ('add', 'add'), ('.add', '.add'),
    ('imul', 'imul'), ('mul', 'mul'),
    ('imin', 'imin'), ('min', 'min'),
    ('imax', 'imax'), ('max', 'max'),
    ('ior', 'ior'), ('or', 'or'),
    ('iand', 'iand'), ('and', 'and'),
})

# ═══════════════════════════════════════════════════════════════
# Internal helpers
# ═══════════════════════════════════════════════════════════════

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


# ═══════════════════════════════════════════════════════════════
# Main apply function
# ═══════════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply D6 axiom: convert between lazy and eager evaluation.

    Produces:
      - D6_list_gen:         list(gen) → comprehension (OMap)
      - D6_gen_to_fold:      fold over generator → fold over collection
      - D6_loop_interchange: nested fold-map commutation
      - D6_iter_for:         iter/next pattern → fold
      - D6_eager_to_lazy:    comprehension → generator (reverse)
    """
    results: List[Tuple[OTerm, str]] = []

    # ── list(generator) → comprehension ──
    # OOp('list', (OMap(f, c),)) → OMap(f, c)
    if isinstance(term, OOp) and term.name == 'list' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OMap):
            results.append((inner, 'D6_list_gen'))
        # list(OOp('generator', ...)) patterns
        if isinstance(inner, OOp) and inner.name in ('generator', 'genexpr'):
            if len(inner.args) >= 2:
                transform = inner.args[0]
                collection = inner.args[1]
                results.append((OMap(transform, collection), 'D6_list_gen'))

    # ── tuple(generator) → OSeq equivalent ──
    if isinstance(term, OOp) and term.name == 'tuple' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OMap):
            results.append((inner, 'D6_tuple_gen'))

    # ── set(generator) → quotient of map ──
    if isinstance(term, OOp) and term.name == 'set' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OMap):
            results.append((OQuotient(inner, 'perm'), 'D6_set_gen'))

    # ── Fold over materialised generator ──
    # fold(op, init, list(gen)) → fold(op, init, gen)
    if isinstance(term, OFold):
        coll = term.collection
        if isinstance(coll, OOp) and coll.name == 'list' and len(coll.args) == 1:
            results.append((
                OFold(term.op_name, term.init, coll.args[0]),
                'D6_fold_demat',
            ))
        # fold(op, init, tuple(gen)) → fold(op, init, gen)
        if isinstance(coll, OOp) and coll.name == 'tuple' and len(coll.args) == 1:
            results.append((
                OFold(term.op_name, term.init, coll.args[0]),
                'D6_fold_demat',
            ))

    # ── sorted(generator) → sorted(list(gen)) is implicit ──
    if isinstance(term, OOp) and term.name == 'sorted' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OMap):
            # sorted(map(f, c)) ≡ sorted of the eager form
            results.append((OOp('sorted', (inner,)), 'D6_sorted_gen'))

    # ── Loop interchange (fold-map commutation) ──
    # fold[op1](init, map(λx. fold[op2](init2, f(x)), outer))
    # → fold over interchanged loops when op1 distributes over op2
    if isinstance(term, OFold) and isinstance(term.collection, OMap):
        inner_map = term.collection
        if (inner_map.filter_pred is None
                and isinstance(inner_map.transform, OLam)):
            lam = inner_map.transform
            if isinstance(lam.body, OFold):
                outer_op = _canonicalize_op(term.op_name)
                inner_op = _canonicalize_op(lam.body.op_name)
                if (outer_op, inner_op) in _DISTRIBUTIVE_PAIRS:
                    inner_fold = lam.body
                    # Build the interchanged version
                    new_inner_lam = OLam(lam.params, inner_fold.collection)
                    new_outer_map = OMap(new_inner_lam, inner_map.collection)
                    new_inner_fold_lam = OLam(
                        ('_y',),
                        OFold(inner_fold.op_name, inner_fold.init, OVar('_y'))
                    )
                    interchanged = OFold(
                        term.op_name, term.init,
                        OMap(new_inner_fold_lam, new_outer_map)
                    )
                    if interchanged.canon() != term.canon():
                        results.append((interchanged, 'D6_loop_interchange'))

    # ── Reverse: OMap → OOp('list', OMap(...)) ──
    # (Eagerness annotation — wrapping in list() makes lazy → eager)
    if isinstance(term, OMap) and term.filter_pred is None:
        results.append((OOp('list', (term,)), 'D6_eager_to_lazy'))

    # ── iter/next → fold equivalence ──
    # OFix with iter/next pattern → fold
    if isinstance(term, OFix):
        body = term.body
        if isinstance(body, OCase):
            # Look for StopIteration-style guard + next() call
            step = body.false_branch
            if isinstance(step, OOp) and step.name in ('next', '__next__'):
                collection = _extract_iter_source(body.test, step)
                if collection is not None:
                    results.append((
                        OFold(term.name, body.true_branch, collection),
                        'D6_iter_to_fold',
                    ))

    # ── any/all over generator ──
    # any(gen) ≡ fold[or](False, gen)
    if isinstance(term, OOp) and term.name == 'any' and len(term.args) == 1:
        results.append((
            OFold('ior', OLit(False), term.args[0]),
            'D6_any_to_fold',
        ))
    if isinstance(term, OOp) and term.name == 'all' and len(term.args) == 1:
        results.append((
            OFold('iand', OLit(True), term.args[0]),
            'D6_all_to_fold',
        ))

    # ── sum/min/max over generator ──
    if isinstance(term, OOp) and term.name == 'sum' and len(term.args) == 1:
        results.append((
            OFold('iadd', OLit(0), term.args[0]),
            'D6_sum_to_fold',
        ))
    if isinstance(term, OOp) and term.name == 'min' and len(term.args) == 1:
        results.append((
            OFold('imin', OLit(float('inf')), term.args[0]),
            'D6_min_to_fold',
        ))
    if isinstance(term, OOp) and term.name == 'max' and len(term.args) == 1:
        results.append((
            OFold('imax', OLit(float('-inf')), term.args[0]),
            'D6_max_to_fold',
        ))

    return results


def _extract_iter_source(guard: OTerm, next_call: OTerm) -> Optional[OTerm]:
    """Try to identify the iterable source from an iter/next pattern.

    Looks for patterns like:
      - guard has StopIteration check
      - next_call refers to an iterator created from a collection
    """
    # Heuristic: if the guard tests for exhaustion of an iterator,
    # the source collection is in the iterator construction
    if isinstance(guard, OOp) and guard.name in ('has_next', 'not_exhausted'):
        if len(guard.args) == 1:
            iter_ref = guard.args[0]
            if isinstance(iter_ref, OOp) and iter_ref.name == 'iter':
                return iter_ref.args[0] if iter_ref.args else None
    return None


# ═══════════════════════════════════════════════════════════════
# Recognition and relevance
# ═══════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could D6 apply to this term?"""
    # list/tuple/set wrapping a map (generator materialisation)
    if isinstance(term, OOp) and term.name in ('list', 'tuple', 'set'):
        if len(term.args) == 1:
            return isinstance(term.args[0], (OMap, OOp))
    # Fold over materialised collection
    if isinstance(term, OFold):
        coll = term.collection
        if isinstance(coll, OOp) and coll.name in ('list', 'tuple'):
            return True
        if isinstance(coll, OMap) and isinstance(coll.transform, OLam):
            if isinstance(coll.transform.body, OFold):
                return True
    # any/all/sum/min/max builtins
    if isinstance(term, OOp) and term.name in ('any', 'all', 'sum', 'min', 'max'):
        return len(term.args) == 1
    # OMap without filter (can wrap in list)
    if isinstance(term, OMap) and term.filter_pred is None:
        return True
    return False


def relevance_score(term: OTerm, other: OTerm) -> float:
    """How likely is D6 to help prove ``term ≡ other``?

    Returns a score in [0.0, 1.0]:
      0.9 — one is list(map(…)) and the other is map(…) (direct match)
      0.7 — one wraps a generator, other is a fold
      0.5 — both involve maps/folds with generators
      0.2 — one side has relevant structure
      0.0 — no lazy/eager patterns
    """
    t_mat = (isinstance(term, OOp) and term.name in ('list', 'tuple', 'set')
             and len(term.args) == 1 and isinstance(term.args[0], OMap))
    o_mat = (isinstance(other, OOp) and other.name in ('list', 'tuple', 'set')
             and len(other.args) == 1 and isinstance(other.args[0], OMap))

    t_map = isinstance(term, OMap)
    o_map = isinstance(other, OMap)

    if (t_mat and o_map) or (o_mat and t_map):
        return 0.9

    t_fold = isinstance(term, OFold)
    o_fold = isinstance(other, OFold)

    if (t_mat and o_fold) or (o_mat and t_fold):
        return 0.7

    if t_mat or o_mat or (t_map and o_fold) or (t_fold and o_map):
        return 0.5

    if recognizes(term) or recognizes(other):
        return 0.2

    return 0.0


# ═══════════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply D6 in reverse.

    - OMap → list(OMap) (materialise)
    - fold → fold over list(gen) (de-materialise)
    """
    results: List[Tuple[OTerm, str]] = []

    # OMap → list(OMap)
    if isinstance(term, OMap) and term.filter_pred is None:
        results.append((OOp('list', (term,)), 'D6_inv_materialise'))

    # fold(op, init, gen) → fold(op, init, list(gen))
    if isinstance(term, OFold) and isinstance(term.collection, OMap):
        results.append((
            OFold(term.op_name, term.init, OOp('list', (term.collection,))),
            'D6_inv_fold_materialise',
        ))

    # fold → any/all/sum/min/max (reverse of builtin expansion)
    if isinstance(term, OFold):
        builtin_map = {
            'ior': ('any', False),
            'iand': ('all', True),
            'iadd': ('sum', 0),
            'imin': ('min', float('inf')),
            'imax': ('max', float('-inf')),
        }
        entry = builtin_map.get(_canonicalize_op(term.op_name))
        if entry is not None:
            name, id_val = entry
            if isinstance(term.init, OLit) and term.init.value == id_val:
                results.append((
                    OOp(name, (term.collection,)),
                    f'D6_inv_fold_to_{name}',
                ))

    return results


# ═══════════════════════════════════════════════════════════════
# Composability metadata
# ═══════════════════════════════════════════════════════════════

COMPOSES_WITH = ["d4_comp_fusion", "d5_fold_universal", "d1_fold_unfold"]
REQUIRES: List[str] = []

# ═══════════════════════════════════════════════════════════════
# Soundness justification
# ═══════════════════════════════════════════════════════════════

SOUNDNESS_PROOF = """
Theorem (D6 Soundness): If D6 transforms t to t', then ⟦t⟧ = ⟦t'⟧.

Proof: By the laziness adjunction L ⊣ E.

1. Generator materialisation:
   ⟦list(map(f, xs))⟧ = list([f(x) for x in xs]) = [f(x) for x in xs] = ⟦map(f, xs)⟧
   The list() call materialises the lazy map into an eager list,
   which has the same elements in the same order.

2. Fold de-materialisation:
   ⟦fold(op, init, list(gen))⟧ = ⟦fold(op, init, gen)⟧
   because fold consumes elements one at a time (streaming), and
   list() merely forces all elements into memory without changing
   their values or order.

3. Loop interchange:
   ⟦fold[op1](init1, map(λx. fold[op2](init2, f(x)), outer))⟧
   = Σ_x∈outer Σ_y∈f(x) op2(init2, y)  [summing in op1]
   When op1 distributes over op2, the summation order can be
   interchanged (Fubini for discrete sums).

4. Builtin equivalences:
   ⟦sum(xs)⟧ = ⟦fold[add](0, xs)⟧  by definition of sum.
   Similarly for any, all, min, max.  ∎
"""

# ═══════════════════════════════════════════════════════════════
# Examples
# ═══════════════════════════════════════════════════════════════

EXAMPLES = [
    {
        "name": "list_of_map",
        "before": "OOp('list', (OMap(OLam(('x',), OOp('f',(OVar('x'),))), OVar('xs')),))",
        "after": "OMap(OLam(('x',), OOp('f',(OVar('x'),))), OVar('xs'))",
        "benchmark": "lazy01",
        "description": "list(map(f, xs)) → map(f, xs)",
    },
    {
        "name": "fold_dematerialise",
        "before": "OFold('iadd', OLit(0), OOp('list', (OMap(f, OVar('xs')),)))",
        "after": "OFold('iadd', OLit(0), OMap(f, OVar('xs')))",
        "benchmark": "lazy02",
        "description": "sum(list(gen)) → sum(gen)",
    },
    {
        "name": "loop_interchange",
        "before": "fold[iadd](0, map(λi. fold[iadd](0, row(i)), matrix))",
        "after": "fold[iadd](0, map(λj. fold[iadd](0, col(j)), transpose(matrix)))",
        "benchmark": "lazy03",
        "description": "Row-sum then total ↔ column-sum then total",
    },
    {
        "name": "any_to_fold",
        "before": "OOp('any', (OVar('xs'),))",
        "after": "OFold('ior', OLit(False), OVar('xs'))",
        "benchmark": "lazy04",
        "description": "any(xs) ≡ fold[or](False, xs)",
    },
    {
        "name": "sum_to_fold",
        "before": "OOp('sum', (OVar('xs'),))",
        "after": "OFold('iadd', OLit(0), OVar('xs'))",
        "benchmark": "lazy05",
        "description": "sum(xs) ≡ fold[add](0, xs)",
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

    # Test list(gen) → map
    print('▶ D6 list(map) → map')
    list_gen = OOp('list', (OMap(f1, OVar('xs')),))
    results = apply(list_gen, ctx)
    _assert(any(lbl == 'D6_list_gen' for _, lbl in results),
            'D6 list_gen fires')
    result = [t for t, lbl in results if lbl == 'D6_list_gen'][0]
    _assert(isinstance(result, OMap), 'result is OMap')

    # Test tuple(gen) → map
    print('▶ D6 tuple(map) → map')
    tuple_gen = OOp('tuple', (OMap(f1, OVar('xs')),))
    results = apply(tuple_gen, ctx)
    _assert(any(lbl == 'D6_tuple_gen' for _, lbl in results),
            'D6 tuple_gen fires')

    # Test set(gen) → quotient
    print('▶ D6 set(map) → Q[perm](map)')
    set_gen = OOp('set', (OMap(f1, OVar('xs')),))
    results = apply(set_gen, ctx)
    _assert(any(lbl == 'D6_set_gen' for _, lbl in results),
            'D6 set_gen fires')
    set_result = [t for t, lbl in results if lbl == 'D6_set_gen'][0]
    _assert(isinstance(set_result, OQuotient), 'result is OQuotient')

    # Test fold de-materialisation
    print('▶ D6 fold over list(gen) → fold over gen')
    fold_list = OFold('iadd', OLit(0), OOp('list', (OVar('gen'),)))
    results = apply(fold_list, ctx)
    _assert(any(lbl == 'D6_fold_demat' for _, lbl in results),
            'D6 fold_demat fires')

    # Test loop interchange
    print('▶ D6 loop interchange')
    inner_body = OFold('iadd', OLit(0), OOp('row', (OVar('i'),)))
    inner_lam = OLam(('i',), inner_body)
    outer = OFold('iadd', OLit(0), OMap(inner_lam, OVar('matrix')))
    results = apply(outer, ctx)
    _assert(any(lbl == 'D6_loop_interchange' for _, lbl in results),
            'D6 loop interchange fires')

    # Test any/all/sum/min/max → fold
    print('▶ D6 builtins → fold')
    for name, op, init_val in [
        ('any', 'ior', False),
        ('all', 'iand', True),
        ('sum', 'iadd', 0),
        ('min', 'imin', float('inf')),
        ('max', 'imax', float('-inf')),
    ]:
        builtin = OOp(name, (OVar('xs'),))
        results = apply(builtin, ctx)
        lbl_prefix = f'D6_{name}_to_fold'
        _assert(any(lbl == lbl_prefix for _, lbl in results),
                f'{name} → fold fires')
        fold_result = [t for t, lbl in results if lbl == lbl_prefix][0]
        _assert(isinstance(fold_result, OFold), f'{name} result is OFold')

    # Test eager→lazy (reverse direction on map)
    print('▶ D6 OMap → list(OMap)')
    simple_map = OMap(f1, OVar('xs'))
    results = apply(simple_map, ctx)
    _assert(any(lbl == 'D6_eager_to_lazy' for _, lbl in results),
            'eager_to_lazy fires')

    # Test recognizes
    print('▶ D6 recognizes()')
    _assert(recognizes(list_gen), 'list(map) recognised')
    _assert(recognizes(fold_list), 'fold over list recognised')
    _assert(recognizes(OOp('sum', (OVar('xs'),))), 'sum() recognised')
    _assert(recognizes(simple_map), 'map recognised')
    _assert(not recognizes(OLit(42)), 'literal not recognised')

    # Test relevance_score
    print('▶ D6 relevance_score()')
    _assert(relevance_score(list_gen, simple_map) == 0.9,
            'list(map) vs map → 0.9')
    _assert(relevance_score(OLit(1), OLit(2)) == 0.0,
            'no lazy/eager → 0.0')

    # Test inverse
    print('▶ D6 apply_inverse()')
    inv_results = apply_inverse(simple_map, ctx)
    _assert(any('inv_materialise' in lbl for _, lbl in inv_results),
            'inverse materialise fires')

    inv_fold = apply_inverse(OFold('iadd', OLit(0), OVar('xs')), ctx)
    _assert(any('fold_to_sum' in lbl for _, lbl in inv_fold),
            'inverse fold→sum fires')

    # Edge cases
    print('▶ D6 edge cases')
    _assert(apply(OLit(3), ctx) == [], 'D6 on literal is empty')
    _assert(apply(OVar('x'), ctx) == [], 'D6 on var is empty')

    # Non-distributive loop interchange should NOT fire
    non_dist = OFold('isub', OLit(0),
                     OMap(OLam(('i',), OFold('iadd', OLit(0), OVar('r'))),
                          OVar('m')))
    results = apply(non_dist, ctx)
    _assert(not any(lbl == 'D6_loop_interchange' for _, lbl in results),
            'non-distributive pair → no interchange')

    print(f'\n{"═" * 50}')
    print(f'  D6: {_passed} passed, {_failed} failed')
    print(f'{"═" * 50}')
    sys.exit(1 if _failed > 0 else 0)
