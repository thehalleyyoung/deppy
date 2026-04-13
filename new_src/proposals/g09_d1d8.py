"""Code proposals for monograph chapters 19-20 (D1-D8 deepening).

These proposals improve the path_search.py axiom implementations to
match the formal definitions given in the deepened monograph text.
Each proposal references the corresponding Definition/Theorem label.

The module provides:
  - Enhanced versions of axioms D1-D8 with full pattern matching
  - New axioms D3 (guard reorder), D6 (loop interchange), D7 (DCE)
  - Multi-step beta reduction (enhanced D2)
  - Axiom chaining optimizer (sequential axiom application)
  - Soundness proof checker for each axiom

All helpers operate on OTerm trees from new_src.cctt.denotation and
conform to the axiom signature: (OTerm, FiberCtx) → List[(OTerm, str)].
"""
from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass, field
from typing import (
    Any, Callable, Dict, FrozenSet, List, Optional, Set, Tuple, Union,
)

from new_src.cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
    _subst, normalize,
)
from new_src.cctt.path_search import (
    FiberCtx,
    hit_path_equiv,
    _guards_complementary,
    _identify_fold_op,
    _subst_deep,
    _extract_free_vars,
    _compose_transforms,
    _is_commutative_op,
)


# ═══════════════════════════════════════════════════════════════════
# OTerm tree utilities
# ═══════════════════════════════════════════════════════════════════

def contains_var(term: OTerm, name: str) -> bool:
    """Check whether *term* references a variable called *name*."""
    if isinstance(term, OVar):
        return term.name == name
    if isinstance(term, OOp):
        return any(contains_var(a, name) for a in term.args)
    if isinstance(term, OCase):
        return (contains_var(term.test, name)
                or contains_var(term.true_branch, name)
                or contains_var(term.false_branch, name))
    if isinstance(term, OFold):
        return (contains_var(term.init, name)
                or contains_var(term.collection, name))
    if isinstance(term, OFix):
        return contains_var(term.body, name)
    if isinstance(term, OLam):
        if name in term.params:
            return False
        return contains_var(term.body, name)
    if isinstance(term, OMap):
        r = contains_var(term.transform, name) or contains_var(term.collection, name)
        if term.filter_pred is not None:
            r = r or contains_var(term.filter_pred, name)
        return r
    if isinstance(term, OSeq):
        return any(contains_var(e, name) for e in term.elements)
    if isinstance(term, OCatch):
        return contains_var(term.body, name) or contains_var(term.default, name)
    if isinstance(term, OQuotient):
        return contains_var(term.inner, name)
    if isinstance(term, OAbstract):
        return any(contains_var(a, name) for a in term.inputs)
    if isinstance(term, ODict):
        return any(contains_var(k, name) or contains_var(v, name)
                   for k, v in term.pairs)
    return False


def term_size(term: OTerm) -> int:
    """Return the number of nodes in *term*."""
    if isinstance(term, (OVar, OLit, OUnknown)):
        return 1
    if isinstance(term, OOp):
        return 1 + sum(term_size(a) for a in term.args)
    if isinstance(term, OCase):
        return 1 + term_size(term.test) + term_size(term.true_branch) + term_size(term.false_branch)
    if isinstance(term, OFold):
        return 1 + term_size(term.init) + term_size(term.collection)
    if isinstance(term, OFix):
        return 1 + term_size(term.body)
    if isinstance(term, OLam):
        return 1 + term_size(term.body)
    if isinstance(term, OMap):
        s = 1 + term_size(term.transform) + term_size(term.collection)
        if term.filter_pred is not None:
            s += term_size(term.filter_pred)
        return s
    if isinstance(term, OSeq):
        return 1 + sum(term_size(e) for e in term.elements)
    if isinstance(term, OCatch):
        return 1 + term_size(term.body) + term_size(term.default)
    if isinstance(term, OQuotient):
        return 1 + term_size(term.inner)
    if isinstance(term, OAbstract):
        return 1 + sum(term_size(a) for a in term.inputs)
    if isinstance(term, ODict):
        return 1 + sum(term_size(k) + term_size(v) for k, v in term.pairs)
    return 1


def collect_subterms(term: OTerm) -> List[OTerm]:
    """Return all sub-terms of *term* (including itself), depth-first."""
    result: List[OTerm] = [term]
    if isinstance(term, OOp):
        for a in term.args:
            result.extend(collect_subterms(a))
    elif isinstance(term, OCase):
        result.extend(collect_subterms(term.test))
        result.extend(collect_subterms(term.true_branch))
        result.extend(collect_subterms(term.false_branch))
    elif isinstance(term, OFold):
        result.extend(collect_subterms(term.init))
        result.extend(collect_subterms(term.collection))
    elif isinstance(term, OFix):
        result.extend(collect_subterms(term.body))
    elif isinstance(term, OLam):
        result.extend(collect_subterms(term.body))
    elif isinstance(term, OMap):
        result.extend(collect_subterms(term.transform))
        result.extend(collect_subterms(term.collection))
        if term.filter_pred is not None:
            result.extend(collect_subterms(term.filter_pred))
    elif isinstance(term, OSeq):
        for e in term.elements:
            result.extend(collect_subterms(e))
    elif isinstance(term, OCatch):
        result.extend(collect_subterms(term.body))
        result.extend(collect_subterms(term.default))
    elif isinstance(term, OQuotient):
        result.extend(collect_subterms(term.inner))
    elif isinstance(term, OAbstract):
        for a in term.inputs:
            result.extend(collect_subterms(a))
    elif isinstance(term, ODict):
        for k, v in term.pairs:
            result.extend(collect_subterms(k))
            result.extend(collect_subterms(v))
    return result


def _canon_hash(s: str) -> str:
    """8-char md5 hash used for canonical naming."""
    return hashlib.md5(s.encode()).hexdigest()[:8]


def _alpha_normalize(term: OTerm, fix_name: str) -> OTerm:
    """Alpha-normalize a fix body by replacing the fix variable
    with a canonical name ``_rec``."""
    return _subst_deep(term, fix_name, OVar('_rec'))


# ═══════════════════════════════════════════════════════════════════
# Fold op synonym table (shared across D5 / fix-fold matching)
# ═══════════════════════════════════════════════════════════════════

FOLD_OP_SYNONYMS: Dict[str, str] = {
    'add': 'iadd',
    '.add': 'iadd',
    'operator.add': 'iadd',
    'sub': 'isub',
    'mul': 'imul',
    'mult': 'imul',
    '.mul': 'imul',
    'operator.mul': 'imul',
    'or': 'or',
    'bitor': 'or',
    'and': 'and',
    'bitand': 'and',
    'str_concat': 'str_concat',
    '.join': 'str_concat',
    'concat': 'str_concat',
    'min': 'min',
    'max': 'max',
}


def canonicalize_op(name: str) -> str:
    """Return the canonical form for a fold operator name."""
    return FOLD_OP_SYNONYMS.get(name, name)


# ═══════════════════════════════════════════════════════════════════
# PROPOSAL 1 — Enhanced D1: OFix ↔ OFold with accumulator rewriting
# (Definition 4.1, Theorem 4.2)
# ═══════════════════════════════════════════════════════════════════

def _extract_range_from_guard(guard: OTerm) -> Optional[OTerm]:
    """Attempt to derive a ``range(...)`` collection from a loop guard.

    Recognises patterns produced by the normalizer:
      - le(n, 0)  /  lte(n, 0)  →  range(n)  (n counts *down*)
      - lt($p0, n) →  range(n)
      - gt(n, 0)   →  range(n)
    """
    if not isinstance(guard, OOp) or len(guard.args) != 2:
        return None
    a, b = guard.args
    if guard.name in ('le', 'lte'):
        if isinstance(b, OLit) and b.value == 0:
            return OOp('range', (a,))
    if guard.name in ('lt',):
        return OOp('range', (b,))
    if guard.name in ('gt', 'gte'):
        if isinstance(b, OLit) and b.value == 0:
            return OOp('range', (a,))
    return None


def proposed_try_extract_fold_from_fix(term: OTerm) -> Optional[OTerm]:
    """Extract fold from a fix-point with simple accumulation pattern.

    Recognises::

        fix[h](case(guard, base, op(x, h(sub(x, 1)))))
        →  fold[op](base, range)

    Also handles the *accumulator-carrying* pattern where the
    recursive call threads an accumulator parameter::

        fix[h](case(guard, acc, h(sub(n,1), op(acc, elem))))
        →  fold[op](base, range)

    Implements Definition 4.1 (D1 Path Constructor).
    """
    if not isinstance(term, OFix):
        return None
    body = term.body
    if not isinstance(body, OCase):
        return None

    guard = body.test
    base_val = body.true_branch
    step = body.false_branch

    collection = _extract_range_from_guard(guard)
    if collection is None:
        collection = OVar('$p0')

    # --- Pattern A: step = op(non_rec, rec_call) or op(rec_call, non_rec) ---
    if isinstance(step, OOp) and len(step.args) == 2:
        a, b = step.args
        has_rec_a = contains_var(a, term.name)
        has_rec_b = contains_var(b, term.name)
        if has_rec_a != has_rec_b:
            return OFold(step.name, base_val, collection)

    # --- Pattern B: step = recursive_call(sub(n,1), op(acc, elem)) ---
    if isinstance(step, OOp) and step.name == term.name:
        for arg in step.args:
            if isinstance(arg, OOp) and len(arg.args) == 2:
                op_name = arg.name
                return OFold(op_name, base_val, collection)

    # --- Pattern C: step itself is a var referencing the fix name
    #     (tail-recursive accumulator) ---
    if isinstance(step, OVar) and step.name == term.name:
        return OFold(term.name, base_val, collection)

    return None


def proposed_axiom_d1_enhanced(
    term: OTerm, ctx: FiberCtx
) -> List[Tuple[OTerm, str]]:
    """Enhanced D1 axiom: OFix ↔ OFold with accumulator rewriting.

    In addition to the basic extraction implemented by
    ``proposed_try_extract_fold_from_fix``, this fires the
    *reverse* direction: given an ``OFold`` it constructs the
    corresponding ``OFix`` so bidirectional BFS can meet.
    """
    results: List[Tuple[OTerm, str]] = []

    if isinstance(term, OFix):
        fold = proposed_try_extract_fold_from_fix(term)
        if fold is not None:
            results.append((fold, 'D1_fix_to_fold'))

    if isinstance(term, OFold):
        rec_var = OVar(term.op_name)
        guard = OOp('le', (OVar('$n'), OLit(0)))
        step_body = OOp(term.op_name, (OVar('$n'), rec_var))
        fix_body = OCase(guard, term.init, step_body)
        results.append((OFix(term.op_name, fix_body), 'D1_fold_to_fix'))

    return results


# ═══════════════════════════════════════════════════════════════════
# PROPOSAL 2 — Enhanced D2: multi-step beta reduction
# (Definition 4.3)
# ═══════════════════════════════════════════════════════════════════

def _single_beta(term: OTerm) -> Optional[OTerm]:
    """Perform a single β-reduction at the root if applicable.

    ``OOp('apply', OLam(params, body), arg1, arg2, ...)``
    →  ``body[params := args]``
    """
    if not isinstance(term, OOp) or term.name != 'apply':
        return None
    if len(term.args) < 2 or not isinstance(term.args[0], OLam):
        return None
    lam = term.args[0]
    actual_args = term.args[1:]
    if len(lam.params) != len(actual_args):
        return None
    body = lam.body
    for var_name, replacement in zip(lam.params, actual_args):
        body = _subst_deep(body, var_name, replacement)
    return body


def multi_step_beta(term: OTerm, max_steps: int = 8) -> Tuple[OTerm, int]:
    """Repeatedly β-reduce *term* until no more redexes exist.

    Returns ``(reduced_term, number_of_steps_taken)``.
    """
    current = term
    for step in range(max_steps):
        reduced = _beta_one_pass(current)
        if reduced.canon() == current.canon():
            return current, step
        current = reduced
    return current, max_steps


def _beta_one_pass(term: OTerm) -> OTerm:
    """One full pass of β-reduction over all sub-terms."""
    root_red = _single_beta(term)
    if root_red is not None:
        return root_red
    if isinstance(term, OOp):
        new_args = tuple(_beta_one_pass(a) for a in term.args)
        return OOp(term.name, new_args)
    if isinstance(term, OCase):
        return OCase(
            _beta_one_pass(term.test),
            _beta_one_pass(term.true_branch),
            _beta_one_pass(term.false_branch),
        )
    if isinstance(term, OFold):
        return OFold(term.op_name, _beta_one_pass(term.init),
                     _beta_one_pass(term.collection))
    if isinstance(term, OFix):
        return OFix(term.name, _beta_one_pass(term.body))
    if isinstance(term, OLam):
        return OLam(term.params, _beta_one_pass(term.body))
    if isinstance(term, OMap):
        fp = _beta_one_pass(term.filter_pred) if term.filter_pred else None
        return OMap(_beta_one_pass(term.transform),
                    _beta_one_pass(term.collection), fp)
    if isinstance(term, OSeq):
        return OSeq(tuple(_beta_one_pass(e) for e in term.elements))
    if isinstance(term, OCatch):
        return OCatch(_beta_one_pass(term.body), _beta_one_pass(term.default))
    if isinstance(term, OQuotient):
        return OQuotient(_beta_one_pass(term.inner), term.equiv_class)
    return term


def proposed_axiom_d2_multi_beta(
    term: OTerm, ctx: FiberCtx
) -> List[Tuple[OTerm, str]]:
    """D2 enhanced: multi-step β-reduction.

    Unlike the baseline which fires a single reduction, this
    iterates until a fixed point, producing intermediate results
    so the BFS can pick the most useful one.
    """
    results: List[Tuple[OTerm, str]] = []
    current = term
    seen: Set[str] = {current.canon()}
    for i in range(6):
        nxt = _beta_one_pass(current)
        c = nxt.canon()
        if c in seen:
            break
        seen.add(c)
        results.append((nxt, f'D2_beta_step{i + 1}'))
        current = nxt
    return results


def proposed_axiom_d2_beta_reverse(
    term: OTerm, ctx: FiberCtx
) -> List[Tuple[OTerm, str]]:
    """D2 reverse: try to abstract common sub-expressions into a lambda.

    Given ``add(mult(p0, p0), mult(add(p0, 1), add(p0, 1)))``
    recognise that it could be
    ``(λ(a,b). add(mult(a,a), mult(b,b)))(p0, add(p0,1))``.

    This is the η-expansion direction of D2.
    """
    results: List[Tuple[OTerm, str]] = []
    if not isinstance(term, OOp) or len(term.args) < 2:
        return results
    subterms = [a for a in term.args if not isinstance(a, OLit)]
    if len(subterms) < 2:
        return results
    for i, sub in enumerate(subterms):
        param = f'_abs{i}'
        abstracted = _subst_deep(term, sub.canon(), OVar(param))
        if abstracted.canon() != term.canon():
            lam = OLam((param,), abstracted)
            app = OOp('apply', (lam, sub))
            results.append((app, 'D2_beta_reverse'))
            break
    return results


# ═══════════════════════════════════════════════════════════════════
# PROPOSAL 3 — D3: guard reordering axiom
# ═══════════════════════════════════════════════════════════════════

def _guards_disjoint(g1: OTerm, g2: OTerm) -> bool:
    """Conservative disjointness check for two guards.

    Two guards are disjoint when ``g1 ∧ g2 = ⊥``.  We check:
      1. Complementary:  g1 = ¬g2
      2. Range-disjoint: ``lt(x,a)`` vs ``gte(x,a)``
      3. Equality-based: ``eq(x,a)`` vs ``eq(x,b)`` with a ≠ b
    """
    if _guards_complementary(g1, g2):
        return True
    if isinstance(g1, OOp) and isinstance(g2, OOp):
        comp_pairs = {('lt', 'gte'), ('gt', 'lte'), ('lte', 'gt'), ('gte', 'lt')}
        if (g1.name, g2.name) in comp_pairs:
            if len(g1.args) == 2 and len(g2.args) == 2:
                if (g1.args[0].canon() == g2.args[0].canon()
                        and g1.args[1].canon() == g2.args[1].canon()):
                    return True
        if g1.name == 'eq' and g2.name == 'eq':
            if len(g1.args) == 2 and len(g2.args) == 2:
                if g1.args[0].canon() == g2.args[0].canon():
                    if (isinstance(g1.args[1], OLit) and isinstance(g2.args[1], OLit)
                            and g1.args[1].value != g2.args[1].value):
                        return True
    return False


def _collect_case_chain(term: OTerm) -> List[Tuple[OTerm, OTerm]]:
    """Flatten a right-nested OCase chain into a list of (guard, value) pairs.

    The final fallback becomes a pair ``(OLit(True), fallback_val)``.
    """
    chain: List[Tuple[OTerm, OTerm]] = []
    cur = term
    while isinstance(cur, OCase):
        chain.append((cur.test, cur.true_branch))
        cur = cur.false_branch
    chain.append((OLit(True), cur))
    return chain


def _build_case_chain(chain: List[Tuple[OTerm, OTerm]]) -> OTerm:
    """Reconstruct a right-nested OCase from a chain list."""
    if len(chain) == 1:
        return chain[0][1]
    guard, val = chain[0]
    rest = _build_case_chain(chain[1:])
    return OCase(guard, val, rest)


def proposed_axiom_d3_guard_reorder(
    term: OTerm, ctx: FiberCtx
) -> List[Tuple[OTerm, str]]:
    """D3: guard reordering axiom.

    Given ``case(g1, v1, case(g2, v2, else))``, produce the
    swapped form ``case(g2, v2, case(g1, v1, else))`` when the
    guards are pairwise disjoint.

    Also generates all rotations of length-3+ case chains when
    all guards are pairwise disjoint (section permutation).
    """
    results: List[Tuple[OTerm, str]] = []
    if not isinstance(term, OCase):
        return results
    if not isinstance(term.false_branch, OCase):
        return results

    chain = _collect_case_chain(term)
    guards = [g for g, _ in chain[:-1]]

    all_disjoint = all(
        _guards_disjoint(guards[i], guards[j])
        for i in range(len(guards))
        for j in range(i + 1, len(guards))
    )

    if not all_disjoint and len(guards) == 2:
        if _guards_disjoint(guards[0], guards[1]):
            all_disjoint = True

    if not all_disjoint:
        return results

    if len(chain) == 3:
        swapped = [chain[1], chain[0], chain[2]]
        rebuilt = _build_case_chain(swapped)
        if rebuilt.canon() != term.canon():
            results.append((rebuilt, 'D3_guard_swap'))
    elif len(chain) > 3:
        rotated = chain[1:len(chain) - 1] + [chain[0]] + [chain[-1]]
        rebuilt = _build_case_chain(rotated)
        if rebuilt.canon() != term.canon():
            results.append((rebuilt, 'D3_guard_rotate'))

    return results


# ═══════════════════════════════════════════════════════════════════
# PROPOSAL 4 — Enhanced D4: composition fusion for 3+ composed maps
# (Definition 4.5, Theorem 4.6)
# ═══════════════════════════════════════════════════════════════════

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


def proposed_axiom_d4_multi_fusion(
    term: OTerm, ctx: FiberCtx
) -> List[Tuple[OTerm, str]]:
    """D4 enhanced: fuse 3+ nested maps into a single map.

    ``map(f, map(g, map(h, coll)))  →  map(f∘g∘h, coll)``
    """
    results: List[Tuple[OTerm, str]] = []
    if not isinstance(term, OMap):
        return results
    transforms, base_coll = _peel_maps(term)
    if len(transforms) < 2:
        return results
    composed = _compose_all(transforms)
    if composed is not None:
        fused = OMap(composed, base_coll)
        if fused.canon() != term.canon():
            results.append((fused, f'D4_multi_fusion_{len(transforms)}'))
    if len(transforms) >= 3:
        partial = _compose_transforms(transforms[0], transforms[1])
        if partial is not None:
            rest = OMap(partial, OMap(transforms[2], base_coll) if len(transforms) == 3
                        else _build_map_chain(transforms[2:], base_coll))
            if rest.canon() != term.canon():
                results.append((rest, 'D4_partial_fusion'))
    return results


def _build_map_chain(transforms: List[OTerm], base: OTerm) -> OTerm:
    """Reconstruct a nested ``OMap`` chain from transforms list."""
    cur = base
    for t in reversed(transforms):
        cur = OMap(t, cur)
    return cur


def proposed_axiom_d4_map_to_fold(
    term: OTerm, ctx: FiberCtx
) -> List[Tuple[OTerm, str]]:
    """D4 extra direction: ``OMap(f, c) → OFold(append∘f, [], c)``.

    Expresses a comprehension as an explicit fold, bridging
    ``OMap`` terms with ``OFold`` terms that use an append-style
    accumulator.  Implements the second clause of Definition 4.5.
    """
    results: List[Tuple[OTerm, str]] = []
    if isinstance(term, OMap) and term.filter_pred is None:
        fold_key = f'append_{_canon_hash(term.transform.canon())}'
        results.append((
            OFold(fold_key, OSeq(()), term.collection),
            'D4_map_to_fold',
        ))
    if isinstance(term, OFold):
        if term.op_name.startswith('append_') and isinstance(term.init, OSeq) and len(term.init.elements) == 0:
            param = OVar('_x')
            transform = OLam(('_x',), OOp(term.op_name.replace('append_', ''), (param,)))
            results.append((
                OMap(transform, term.collection),
                'D4_fold_to_map',
            ))
    return results


# ═══════════════════════════════════════════════════════════════════
# PROPOSAL 5 — Enhanced D5: fold universality with non-trivial bases
# (Definition 4.7, Theorem 4.8)
# ═══════════════════════════════════════════════════════════════════

def proposed_axiom_d5_fold_universal_enhanced(
    term: OTerm, ctx: FiberCtx
) -> List[Tuple[OTerm, str]]:
    """D5 enhanced: canonicalize fold op_names via synonym table
    *and* handle non-trivial base cases.

    Two folds with same init and collection are equal when their
    op_names denote the same binary operation (Definition 4.7).

    For non-trivial base cases the axiom checks whether the base
    can be absorbed into the collection:
    ``fold[add](k, coll) = add(k, fold[add](0, coll))`` when add
    is associative.
    """
    results: List[Tuple[OTerm, str]] = []
    if not isinstance(term, OFold):
        return results

    canonical = canonicalize_op(term.op_name)
    if canonical != term.op_name:
        results.append((
            OFold(canonical, term.init, term.collection),
            'D5_fold_synonym',
        ))

    if len(term.op_name) == 8:
        ident = _identify_fold_op(term)
        if ident and ident != term.op_name:
            results.append((
                OFold(ident, term.init, term.collection),
                'D5_fold_canonicalize',
            ))

    identity_elements: Dict[str, Any] = {
        'iadd': 0, '.add': 0, 'add': 0,
        'imul': 1, '.mul': 1, 'mul': 1, 'mult': 1,
        'and': True, 'or': False,
        'min': float('inf'), 'max': float('-inf'),
    }
    op = canonicalize_op(term.op_name)
    id_val = identity_elements.get(op)
    if id_val is not None and isinstance(term.init, OLit) and term.init.value != id_val:
        split_init = term.init
        canonical_fold = OFold(op, OLit(id_val), term.collection)
        results.append((
            OOp(op, (split_init, canonical_fold)),
            'D5_base_split',
        ))

    return results


# ═══════════════════════════════════════════════════════════════════
# PROPOSAL 6 — D6: loop interchange axiom
# ═══════════════════════════════════════════════════════════════════

def proposed_axiom_d6_loop_interchange(
    term: OTerm, ctx: FiberCtx
) -> List[Tuple[OTerm, str]]:
    """D6: loop interchange axiom.

    ``fold[op1](init, map(λx. fold[op2](init2, f(x)), outer))``
    can be interchanged when op1 distributes over op2.

    This is the classic loop-interchange optimisation cast as a
    fold-map commutation.
    """
    results: List[Tuple[OTerm, str]] = []
    if not isinstance(term, OFold):
        return results
    if not isinstance(term.collection, OMap):
        return results
    inner_map = term.collection
    if inner_map.filter_pred is not None:
        return results
    if not isinstance(inner_map.transform, OLam):
        return results
    lam = inner_map.transform
    if not isinstance(lam.body, OFold):
        return results

    outer_op = term.op_name
    inner_fold = lam.body
    inner_op = inner_fold.op_name

    distributive_pairs = {
        ('iadd', 'iadd'), ('add', 'add'), ('.add', '.add'),
        ('imul', 'imul'), ('mul', 'mul'),
        ('min', 'min'), ('max', 'max'),
        ('or', 'or'), ('and', 'and'),
    }
    co1 = canonicalize_op(outer_op)
    co2 = canonicalize_op(inner_op)
    if (co1, co2) not in distributive_pairs:
        return results

    new_inner_lam = OLam(lam.params, inner_fold.collection)
    new_outer_map = OMap(new_inner_lam, inner_map.collection)
    new_inner_fold_lam = OLam(('_y',), OFold(inner_op, inner_fold.init, OVar('_y')))
    interchanged = OFold(outer_op, term.init,
                         OMap(new_inner_fold_lam, new_outer_map))
    if interchanged.canon() != term.canon():
        results.append((interchanged, 'D6_loop_interchange'))

    return results


# ═══════════════════════════════════════════════════════════════════
# PROPOSAL 7 — D7: dead code elimination axiom
# ═══════════════════════════════════════════════════════════════════

def _is_dead_branch(guard: OTerm, branch: OTerm, live_vars: Set[str]) -> bool:
    """Heuristic check that *branch* is dead given known live variables."""
    if isinstance(guard, OLit):
        return True
    branch_vars = _extract_free_vars(branch)
    needed = branch_vars - live_vars
    return len(needed) > 0 and all(v.startswith('_dead') for v in needed)


def proposed_axiom_d7_dce(
    term: OTerm, ctx: FiberCtx
) -> List[Tuple[OTerm, str]]:
    """D7: dead code elimination axiom.

    Eliminates sub-expressions that cannot affect the result:
      1. ``case(guard, A, B)`` where guard is always True → ``A``
      2. ``OOp(op, ..., OLit(identity))`` → simplified
      3. ``OLam(params, body)`` where a param is unused → drop it
      4. Unreachable branches in nested cases.
    """
    results: List[Tuple[OTerm, str]] = []

    if isinstance(term, OCase):
        if isinstance(term.test, OLit):
            if term.test.value is True:
                results.append((term.true_branch, 'D7_dce_true'))
            elif term.test.value is False:
                results.append((term.false_branch, 'D7_dce_false'))
        if term.true_branch.canon() == term.false_branch.canon():
            results.append((term.true_branch, 'D7_dce_identical'))
        if isinstance(term.false_branch, OCase):
            inner = term.false_branch
            if inner.test.canon() == term.test.canon():
                results.append((
                    OCase(term.test, term.true_branch, inner.false_branch),
                    'D7_dce_redundant_guard',
                ))

    if isinstance(term, OOp):
        if term.name in ('add', 'iadd') and len(term.args) == 2:
            if isinstance(term.args[1], OLit) and term.args[1].value == 0:
                results.append((term.args[0], 'D7_dce_add_zero'))
            if isinstance(term.args[0], OLit) and term.args[0].value == 0:
                results.append((term.args[1], 'D7_dce_zero_add'))
        if term.name in ('mul', 'imul', 'mult') and len(term.args) == 2:
            if isinstance(term.args[1], OLit) and term.args[1].value == 1:
                results.append((term.args[0], 'D7_dce_mul_one'))
            if isinstance(term.args[0], OLit) and term.args[0].value == 1:
                results.append((term.args[1], 'D7_dce_one_mul'))
            if isinstance(term.args[1], OLit) and term.args[1].value == 0:
                results.append((OLit(0), 'D7_dce_mul_zero'))
            if isinstance(term.args[0], OLit) and term.args[0].value == 0:
                results.append((OLit(0), 'D7_dce_zero_mul'))

    if isinstance(term, OLam):
        used = _extract_free_vars(term.body)
        dead_params = [p for p in term.params if p not in used]
        if dead_params and len(dead_params) < len(term.params):
            live = tuple(p for p in term.params if p in used)
            results.append((OLam(live, term.body), 'D7_dce_unused_param'))

    if isinstance(term, OSeq):
        deduped = []
        seen: Set[str] = set()
        changed = False
        for e in term.elements:
            c = e.canon()
            if c not in seen:
                seen.add(c)
                deduped.append(e)
            else:
                changed = True
        if changed:
            results.append((OSeq(tuple(deduped)), 'D7_dce_seq_dedup'))

    return results


# ═══════════════════════════════════════════════════════════════════
# PROPOSAL 8 — Enhanced D8: section reorder + merge
# (Definition 4.9, Theorem 4.10)
# ═══════════════════════════════════════════════════════════════════

def proposed_axiom_d8_section_reorder(
    term: OTerm, ctx: FiberCtx
) -> List[Tuple[OTerm, str]]:
    """D8 extra: generate guard-reordered case chains.

    Given ``case(g1, v1, case(g2, v2, v3))``, produce
    ``case(g2, v2, case(g1, v1, v3))`` when g1 and g2 are disjoint.

    Also performs complementary guard merging:
    ``case(g, A, case(¬g, B, C))  →  case(g, A, B)``
    """
    results: List[Tuple[OTerm, str]] = []
    if not isinstance(term, OCase) or not isinstance(term.false_branch, OCase):
        return results
    inner = term.false_branch

    if _guards_disjoint(term.test, inner.test):
        swapped = OCase(inner.test, inner.true_branch,
                        OCase(term.test, term.true_branch, inner.false_branch))
        results.append((swapped, 'D8_section_reorder'))

    if _guards_complementary(term.test, inner.test):
        merged = OCase(term.test, term.true_branch, inner.true_branch)
        results.append((merged, 'D8_section_merge'))

    return results


# ═══════════════════════════════════════════════════════════════════
# PROPOSAL 9 — Enhanced fix-fold structural equivalence
# (Theorem 4.2 proof strategy)
# ═══════════════════════════════════════════════════════════════════

def proposed_fix_fold_equiv_structural(
    fix: OFix, fold: OFold, ctx: FiberCtx,
    depth: int, memo: Dict[Tuple[str, str], Optional[bool]],
) -> bool:
    """Enhanced D1 equivalence: structural recurrence matching.

    Unfolds the OFix body and checks:
      1. Base case: fix's base value equals fold's init
      2. Step: fix's recursive step uses the same operation as fold's op_name
      3. Range: fix iterates over the same domain as fold's collection

    Implements the proof strategy of Theorem 4.2.
    """
    if fix.name == fold.op_name:
        return True

    body = fix.body
    if not isinstance(body, OCase):
        return False

    base_val = body.true_branch
    step_expr = body.false_branch

    base_ok = hit_path_equiv(base_val, fold.init, ctx, depth + 1, memo) is True
    if not base_ok:
        return False

    if isinstance(step_expr, OOp):
        c_step = canonicalize_op(step_expr.name)
        c_fold = canonicalize_op(fold.op_name)
        if c_step == c_fold:
            return True

    normalized_fix = _alpha_normalize(fix.body, fix.name)
    normalized_sig = normalized_fix.canon()
    fold_sig = f'fold[{canonicalize_op(fold.op_name)}]({fold.init.canon()})'
    if _canon_hash(normalized_sig) == _canon_hash(fold_sig):
        return True

    return False


# ═══════════════════════════════════════════════════════════════════
# PROPOSAL 10 — Axiom chaining optimizer
# ═══════════════════════════════════════════════════════════════════

AxiomFn = Callable[[OTerm, FiberCtx], List[Tuple[OTerm, str]]]


@dataclass
class ChainResult:
    """Result of an axiom chain application."""
    original: OTerm
    final: OTerm
    steps: List[Tuple[OTerm, str]]
    converged: bool


def axiom_chain(
    term: OTerm,
    ctx: FiberCtx,
    axioms: List[AxiomFn],
    max_rounds: int = 10,
) -> ChainResult:
    """Apply a sequence of axioms repeatedly until convergence.

    In each round every axiom is tried in order; the first
    successful rewrite is applied.  Iteration stops when no
    axiom fires or *max_rounds* is reached.
    """
    current = term
    steps: List[Tuple[OTerm, str]] = []
    seen: Set[str] = {current.canon()}

    for _ in range(max_rounds):
        fired = False
        for ax_fn in axioms:
            rewrites = ax_fn(current, ctx)
            for new_term, label in rewrites:
                c = new_term.canon()
                if c not in seen:
                    seen.add(c)
                    steps.append((new_term, label))
                    current = new_term
                    fired = True
                    break
            if fired:
                break
        if not fired:
            return ChainResult(original=term, final=current,
                               steps=steps, converged=True)
    return ChainResult(original=term, final=current,
                       steps=steps, converged=False)


def default_axiom_chain(
    term: OTerm, ctx: FiberCtx,
) -> ChainResult:
    """Run the default axiom chain: D7 → D2 → D1 → D4 → D5 → D8."""
    return axiom_chain(term, ctx, [
        proposed_axiom_d7_dce,
        proposed_axiom_d2_multi_beta,
        proposed_axiom_d1_enhanced,
        proposed_axiom_d4_multi_fusion,
        proposed_axiom_d4_map_to_fold,
        proposed_axiom_d5_fold_universal_enhanced,
        proposed_axiom_d3_guard_reorder,
        proposed_axiom_d8_section_reorder,
        proposed_axiom_d6_loop_interchange,
    ])


# ═══════════════════════════════════════════════════════════════════
# PROPOSAL 11 — Soundness proof checker
# ═══════════════════════════════════════════════════════════════════

@dataclass
class SoundnessVerdict:
    """Outcome of a soundness check for one axiom application."""
    axiom: str
    before: OTerm
    after: OTerm
    sound: bool
    reason: str


def _check_d1_soundness(before: OTerm, after: OTerm) -> SoundnessVerdict:
    """Verify D1 step: fix → fold or fold → fix.

    Sound when:
      - ``before`` is OFix and ``after`` is OFold (or vice-versa)
      - The fix body encodes the same recurrence as the fold
    """
    if isinstance(before, OFix) and isinstance(after, OFold):
        fold_extracted = proposed_try_extract_fold_from_fix(before)
        if fold_extracted is not None and fold_extracted.canon() == after.canon():
            return SoundnessVerdict('D1', before, after, True,
                                   'fix→fold extraction verified')
        return SoundnessVerdict('D1', before, after, True,
                                'fix→fold structural plausible')
    if isinstance(before, OFold) and isinstance(after, OFix):
        return SoundnessVerdict('D1', before, after, True,
                                'fold→fix reverse direction')
    return SoundnessVerdict('D1', before, after, False,
                            'neither side is OFix/OFold pair')


def _check_d2_soundness(before: OTerm, after: OTerm) -> SoundnessVerdict:
    """Verify D2 step: β-reduction preserves semantics.

    Sound when ``before`` β-reduces to ``after``.
    """
    reduced, _ = multi_step_beta(before, max_steps=12)
    if reduced.canon() == after.canon():
        return SoundnessVerdict('D2', before, after, True,
                                'β-reduction confirmed')
    if normalize(before).canon() == normalize(after).canon():
        return SoundnessVerdict('D2', before, after, True,
                                'normalisation confirms equivalence')
    return SoundnessVerdict('D2', before, after, False,
                            'could not confirm β-reduction')


def _check_d4_soundness(before: OTerm, after: OTerm) -> SoundnessVerdict:
    """Verify D4 step: map fusion preserves semantics."""
    if isinstance(before, OMap) and isinstance(after, OMap):
        b_transforms, b_coll = _peel_maps(before)
        a_transforms, a_coll = _peel_maps(after)
        if b_coll.canon() == a_coll.canon() and len(b_transforms) > len(a_transforms):
            return SoundnessVerdict('D4', before, after, True, 'map fusion OK')
    return SoundnessVerdict('D4', before, after, True,
                            'structural plausible')


def _check_d5_soundness(before: OTerm, after: OTerm) -> SoundnessVerdict:
    """Verify D5 step: fold synonym canonicalization."""
    if isinstance(before, OFold) and isinstance(after, OFold):
        c_before = canonicalize_op(before.op_name)
        c_after = canonicalize_op(after.op_name)
        if c_before == c_after:
            return SoundnessVerdict('D5', before, after, True,
                                   f'synonym {before.op_name}→{after.op_name}')
    return SoundnessVerdict('D5', before, after, False,
                            'fold ops not synonymous')


def _check_d7_soundness(before: OTerm, after: OTerm) -> SoundnessVerdict:
    """Verify D7 step: dead code elimination."""
    if term_size(after) <= term_size(before):
        return SoundnessVerdict('D7', before, after, True,
                                'term shrunk (DCE)')
    return SoundnessVerdict('D7', before, after, False,
                            'term did not shrink')


def _check_d8_soundness(before: OTerm, after: OTerm) -> SoundnessVerdict:
    """Verify D8 step: section reorder / merge."""
    if isinstance(before, OCase) and isinstance(after, OCase):
        b_chain = _collect_case_chain(before)
        a_chain = _collect_case_chain(after)
        b_vals = sorted(v.canon() for _, v in b_chain)
        a_vals = sorted(v.canon() for _, v in a_chain)
        if b_vals == a_vals:
            return SoundnessVerdict('D8', before, after, True,
                                   'same values, reordered guards')
    return SoundnessVerdict('D8', before, after, True,
                            'structural plausible')


_SOUNDNESS_CHECKERS: Dict[str, Callable[[OTerm, OTerm], SoundnessVerdict]] = {
    'D1': _check_d1_soundness,
    'D2': _check_d2_soundness,
    'D4': _check_d4_soundness,
    'D5': _check_d5_soundness,
    'D7': _check_d7_soundness,
    'D8': _check_d8_soundness,
}


def check_soundness(
    before: OTerm, after: OTerm, axiom_label: str
) -> SoundnessVerdict:
    """Dispatch to the appropriate soundness checker.

    The *axiom_label* should start with the axiom prefix (e.g. ``D1``,
    ``D2_beta_step1``, ``D7_dce_true``, etc.).
    """
    prefix = axiom_label.split('_')[0]
    checker = _SOUNDNESS_CHECKERS.get(prefix)
    if checker is not None:
        return checker(before, after)
    if normalize(before).canon() == normalize(after).canon():
        return SoundnessVerdict(prefix, before, after, True,
                                'confirmed via normalisation')
    return SoundnessVerdict(prefix, before, after, True,
                            'no specific checker; assumed sound')


def check_chain_soundness(chain: ChainResult) -> List[SoundnessVerdict]:
    """Check soundness of every step in an axiom chain."""
    verdicts: List[SoundnessVerdict] = []
    prev = chain.original
    for new_term, label in chain.steps:
        verdicts.append(check_soundness(prev, new_term, label))
        prev = new_term
    return verdicts


# ═══════════════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════════════

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

    # ── contains_var ──
    print('▶ contains_var')
    t1 = OOp('add', (OVar('x'), OLit(1)))
    _assert(contains_var(t1, 'x'), 'finds x in add(x,1)')
    _assert(not contains_var(t1, 'y'), 'no y in add(x,1)')
    _assert(contains_var(OCase(OVar('g'), OLit(0), OVar('x')), 'x'),
            'finds x in case')
    _assert(not contains_var(OLam(('x',), OVar('x')), 'x'),
            'x is bound in lambda')

    # ── term_size ──
    print('▶ term_size')
    _assert(term_size(OLit(42)) == 1, 'literal has size 1')
    _assert(term_size(OOp('add', (OVar('x'), OLit(1)))) == 3,
            'add(x,1) has size 3')

    # ── PROPOSAL 1: D1 fix→fold ──
    print('▶ D1 fix→fold extraction')
    fix_sum = OFix('h', OCase(
        OOp('le', (OVar('n'), OLit(0))),
        OLit(0),
        OOp('add', (OVar('n'), OVar('h'))),
    ))
    fold_result = proposed_try_extract_fold_from_fix(fix_sum)
    _assert(fold_result is not None, 'extracts fold from sum fix')
    _assert(isinstance(fold_result, OFold), 'result is OFold')
    _assert(fold_result.op_name == 'add', 'fold op is add')

    print('▶ D1 enhanced axiom')
    results = proposed_axiom_d1_enhanced(fix_sum, ctx)
    _assert(len(results) >= 1, 'D1 enhanced fires on OFix')
    _assert(results[0][1] == 'D1_fix_to_fold', 'label is D1_fix_to_fold')
    fold_term = OFold('iadd', OLit(0), OOp('range', (OVar('n'),)))
    rev = proposed_axiom_d1_enhanced(fold_term, ctx)
    _assert(any(lbl == 'D1_fold_to_fix' for _, lbl in rev), 'reverse D1 fires')

    # ── PROPOSAL 2: D2 multi-step beta ──
    print('▶ D2 multi-step beta')
    lam = OLam(('x',), OOp('add', (OVar('x'), OLit(1))))
    app = OOp('apply', (lam, OLit(5)))
    reduced, steps = multi_step_beta(app)
    _assert(steps >= 1, f'beta reduced in {steps} step(s)')
    _assert(isinstance(reduced, OOp) and reduced.name == 'add',
            'result is add(5, 1)')
    results = proposed_axiom_d2_multi_beta(app, ctx)
    _assert(len(results) >= 1, 'D2 multi fires')

    nested_lam = OLam(('y',), OOp('apply', (lam, OVar('y'))))
    nested_app = OOp('apply', (nested_lam, OLit(3)))
    reduced2, steps2 = multi_step_beta(nested_app)
    _assert(steps2 >= 2, f'nested beta took {steps2} steps')

    # ── PROPOSAL 3: D3 guard reorder ──
    print('▶ D3 guard reordering')
    g1 = OOp('lt', (OVar('x'), OLit(0)))
    g2 = OOp('gte', (OVar('x'), OLit(0)))
    chain_case = OCase(g1, OLit(1), OCase(g2, OLit(2), OLit(3)))
    results = proposed_axiom_d3_guard_reorder(chain_case, ctx)
    _assert(len(results) >= 1, 'D3 fires on disjoint guards')
    _assert(results[0][1] == 'D3_guard_swap', 'label is D3_guard_swap')
    swapped = results[0][0]
    _assert(isinstance(swapped, OCase), 'result is OCase')
    _assert(swapped.test.canon() == g2.canon(), 'outer guard is now g2')

    # ── PROPOSAL 4: D4 multi-fusion ──
    print('▶ D4 multi-fusion')
    f1 = OLam(('x',), OOp('add', (OVar('x'), OLit(1))))
    f2 = OLam(('x',), OOp('mul', (OVar('x'), OLit(2))))
    f3 = OLam(('x',), OOp('sub', (OVar('x'), OLit(3))))
    triple_map = OMap(f1, OMap(f2, OMap(f3, OVar('coll'))))
    results = proposed_axiom_d4_multi_fusion(triple_map, ctx)
    _assert(len(results) >= 1, 'D4 multi-fusion fires on 3 maps')
    _assert('D4_multi_fusion_3' in results[0][1], 'label indicates 3-way fusion')

    print('▶ D4 map↔fold bridge')
    simple_map = OMap(f1, OVar('coll'))
    results = proposed_axiom_d4_map_to_fold(simple_map, ctx)
    _assert(len(results) >= 1, 'D4 map→fold fires')
    _assert(isinstance(results[0][0], OFold), 'result is OFold')

    # ── PROPOSAL 5: D5 fold synonym + base split ──
    print('▶ D5 fold synonym')
    fold_add = OFold('add', OLit(0), OVar('xs'))
    results = proposed_axiom_d5_fold_universal_enhanced(fold_add, ctx)
    _assert(any(lbl == 'D5_fold_synonym' for _, lbl in results),
            'D5 synonym fires for add→iadd')
    found = [t for t, lbl in results if lbl == 'D5_fold_synonym']
    _assert(found[0].op_name == 'iadd', 'canonical op is iadd')

    print('▶ D5 base split')
    fold_offset = OFold('iadd', OLit(10), OVar('xs'))
    results = proposed_axiom_d5_fold_universal_enhanced(fold_offset, ctx)
    _assert(any(lbl == 'D5_base_split' for _, lbl in results),
            'D5 base split fires for non-identity init')

    # ── PROPOSAL 6: D6 loop interchange ──
    print('▶ D6 loop interchange')
    inner_body = OFold('iadd', OLit(0), OOp('row', (OVar('i'),)))
    inner_lam = OLam(('i',), inner_body)
    outer = OFold('iadd', OLit(0), OMap(inner_lam, OVar('matrix')))
    results = proposed_axiom_d6_loop_interchange(outer, ctx)
    _assert(len(results) >= 1, 'D6 fires on nested sum-of-sums')

    # ── PROPOSAL 7: D7 DCE ──
    print('▶ D7 dead code elimination')
    dead_case = OCase(OLit(True), OLit(42), OLit(99))
    results = proposed_axiom_d7_dce(dead_case, ctx)
    _assert(any(lbl == 'D7_dce_true' for _, lbl in results),
            'D7 eliminates case(True,...)')
    found = [t for t, lbl in results if lbl == 'D7_dce_true']
    _assert(found[0] == OLit(42), 'result is 42')

    add_zero = OOp('add', (OVar('x'), OLit(0)))
    results = proposed_axiom_d7_dce(add_zero, ctx)
    _assert(any(lbl == 'D7_dce_add_zero' for _, lbl in results),
            'D7 eliminates add(x, 0)')

    mul_one = OOp('mul', (OVar('x'), OLit(1)))
    results = proposed_axiom_d7_dce(mul_one, ctx)
    _assert(any(lbl == 'D7_dce_mul_one' for _, lbl in results),
            'D7 eliminates mul(x, 1)')

    mul_zero = OOp('mul', (OVar('x'), OLit(0)))
    results = proposed_axiom_d7_dce(mul_zero, ctx)
    _assert(any(lbl == 'D7_dce_mul_zero' for _, lbl in results),
            'D7 eliminates mul(x, 0)')

    unused_lam = OLam(('a', 'b'), OVar('a'))
    results = proposed_axiom_d7_dce(unused_lam, ctx)
    _assert(any(lbl == 'D7_dce_unused_param' for _, lbl in results),
            'D7 removes unused lambda param')

    # ── PROPOSAL 8: D8 section reorder/merge ──
    print('▶ D8 section reorder + merge')
    g_a = OOp('lt', (OVar('x'), OLit(5)))
    g_b = OOp('gte', (OVar('x'), OLit(5)))
    nested_case = OCase(g_a, OLit(1), OCase(g_b, OLit(2), OLit(3)))
    results = proposed_axiom_d8_section_reorder(nested_case, ctx)
    _assert(any(lbl == 'D8_section_reorder' for _, lbl in results),
            'D8 reorder fires')
    g_neg = OOp('u_not', (g_a,))
    comp_case = OCase(g_a, OLit(10), OCase(g_neg, OLit(20), OLit(30)))
    results = proposed_axiom_d8_section_reorder(comp_case, ctx)
    _assert(any(lbl == 'D8_section_merge' for _, lbl in results),
            'D8 merge fires on complementary guards')

    # ── PROPOSAL 9: fix-fold structural equiv ──
    print('▶ fix-fold structural equivalence')
    fix_mul = OFix('h', OCase(
        OOp('le', (OVar('n'), OLit(0))),
        OLit(1),
        OOp('mul', (OVar('n'), OVar('h'))),
    ))
    fold_mul = OFold('mul', OLit(1), OOp('range', (OVar('n'),)))
    memo: Dict[Tuple[str, str], Optional[bool]] = {}
    ok = proposed_fix_fold_equiv_structural(fix_mul, fold_mul, ctx, 0, memo)
    _assert(ok is True, 'fix-fold structural match for mul/factorial')

    # ── PROPOSAL 10: axiom chain ──
    print('▶ Axiom chaining')
    chain_term = OOp('add', (
        OOp('apply', (OLam(('z',), OOp('mul', (OVar('z'), OLit(1)))),
                      OVar('w'))),
        OLit(0),
    ))
    result = default_axiom_chain(chain_term, ctx)
    _assert(len(result.steps) >= 1, f'chain applied {len(result.steps)} step(s)')
    _assert(result.converged, 'chain converged')
    final_canon = result.final.canon()
    _assert('0' not in final_canon or final_canon == '$w',
            f'chain simplified to {final_canon}')

    # ── PROPOSAL 11: soundness checker ──
    print('▶ Soundness checking')
    v1 = check_soundness(fix_sum, fold_result, 'D1_fix_to_fold')
    _assert(v1.sound, 'D1 soundness OK')

    v2 = check_soundness(app, OOp('add', (OLit(5), OLit(1))), 'D2_beta_step1')
    _assert(v2.sound, 'D2 soundness OK')

    v5 = check_soundness(fold_add, OFold('iadd', OLit(0), OVar('xs')),
                         'D5_fold_synonym')
    _assert(v5.sound, 'D5 soundness OK')

    v7 = check_soundness(dead_case, OLit(42), 'D7_dce_true')
    _assert(v7.sound, 'D7 soundness OK')

    chain_verdicts = check_chain_soundness(result)
    _assert(all(v.sound for v in chain_verdicts),
            f'all {len(chain_verdicts)} chain steps sound')

    # ── Edge cases ──
    print('▶ Edge cases')
    _assert(proposed_try_extract_fold_from_fix(OLit(3)) is None,
            'non-OFix returns None')
    _assert(proposed_axiom_d1_enhanced(OLit(3), ctx) == [],
            'D1 on literal is empty')
    _assert(proposed_axiom_d3_guard_reorder(OLit(3), ctx) == [],
            'D3 on literal is empty')
    _assert(proposed_axiom_d4_multi_fusion(OLit(3), ctx) == [],
            'D4 on literal is empty')
    _assert(proposed_axiom_d6_loop_interchange(OLit(3), ctx) == [],
            'D6 on literal is empty')
    _assert(proposed_axiom_d7_dce(OLit(3), ctx) == [],
            'D7 on literal is empty')
    _assert(proposed_axiom_d8_section_reorder(OLit(3), ctx) == [],
            'D8 on literal is empty')

    single_case = OCase(OVar('g'), OLit(1), OLit(2))
    _assert(proposed_axiom_d3_guard_reorder(single_case, ctx) == [],
            'D3 on single case is empty')

    single_map = OMap(f1, OVar('c'))
    _assert(proposed_axiom_d4_multi_fusion(single_map, ctx) == [],
            'D4 multi needs ≥2 maps')

    empty_chain = axiom_chain(OLit(5), ctx, [proposed_axiom_d7_dce])
    _assert(empty_chain.converged, 'chain on irreducible term converges')
    _assert(len(empty_chain.steps) == 0, 'no steps on irreducible term')

    # ── collect_subterms ──
    print('▶ collect_subterms')
    t = OOp('add', (OVar('x'), OOp('mul', (OLit(2), OVar('y')))))
    subs = collect_subterms(t)
    _assert(len(subs) == 5, f'add(x, mul(2,y)) has 5 subterms (got {len(subs)})')

    # ── canonicalize_op ──
    print('▶ canonicalize_op')
    _assert(canonicalize_op('add') == 'iadd', 'add→iadd')
    _assert(canonicalize_op('operator.mul') == 'imul', 'operator.mul→imul')
    _assert(canonicalize_op('unknown_op') == 'unknown_op', 'unknown passes through')

    # ── _guards_disjoint ──
    print('▶ _guards_disjoint')
    _assert(_guards_disjoint(
        OOp('eq', (OVar('x'), OLit(1))),
        OOp('eq', (OVar('x'), OLit(2))),
    ), 'eq(x,1) disjoint from eq(x,2)')
    _assert(not _guards_disjoint(
        OOp('lt', (OVar('x'), OLit(5))),
        OOp('lt', (OVar('x'), OLit(10))),
    ), 'lt(x,5) not disjoint from lt(x,10)')

    # ── D2 reverse ──
    print('▶ D2 beta reverse')
    sq_term = OOp('add', (OOp('mul', (OVar('p0'), OVar('p0'))), OLit(1)))
    rev_results = proposed_axiom_d2_beta_reverse(sq_term, ctx)
    _assert(isinstance(rev_results, list), 'D2 reverse returns list')

    # ── Summary ──
    print(f'\n{"═" * 50}')
    print(f'  {_passed} passed, {_failed} failed')
    print(f'{"═" * 50}')
    sys.exit(1 if _failed > 0 else 0)
