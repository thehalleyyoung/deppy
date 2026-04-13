"""P31 Axiom: Counter / DefaultDict Equivalences.

Establishes equivalences between collections.Counter, defaultdict,
and their manual-loop / dict-comprehension counterparts.

Mathematical basis: Counter(xs) is the image of xs under the free
commutative-monoid functor  F: List(X) → ℕ^X.  A manual counting
loop computes the same homomorphism by iterating over xs and
incrementing a dict.  Both inhabit the same object in the
presheaf category of finite multisets, so the rewrite is a
natural isomorphism:  Counter(xs) ≅ count_loop(xs).

Counter arithmetic (+, -, &, |) corresponds to the lattice operations
on ℕ^X:  pointwise addition, monus, meet, and join respectively.

defaultdict(list) and the setdefault idiom are isomorphic in the
category of mappings X → List(Y) with append-morphisms.

Key rewrites:
  • Counter(lst) ↔ manual counting loop
  • Counter.most_common(n) ↔ sorted(… key=lambda …)[:n]
  • defaultdict(list) ↔ dict.setdefault pattern
  • defaultdict(int) ↔ Counter
  • Counter + Counter ↔ element-wise addition
  • Counter - Counter ↔ element-wise subtraction (monus)
  • Counter & Counter ↔ element-wise minimum (meet)
  • Counter | Counter ↔ element-wise maximum (join)
  • Counter ↔ dict comprehension counting
  • Counter.update ↔ loop increment
  • Counter.elements ↔ chain.from_iterable repeat
  • Counter.total ↔ sum(c.values())

(§P31, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P31_counter"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P7_collections", "P3_dict_ops", "P1_comprehension"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P31 Counter / DefaultDict Equivalences).

1. Counter(lst) ≡ count_loop(lst)
   Both compute the free-commutative-monoid image F(lst) ∈ ℕ^X.
   The loop explicitly folds over lst with a dict accumulator;
   Counter.__init__ does the same internally.

2. most_common(c, n) ≡ sorted_by_count(c, n)
   most_common returns elements in decreasing count order, identical
   to sorted(c.items(), key=lambda kv: -kv[1])[:n].

3. defaultdict_list(d, k, v) ≡ setdefault_append(d, k, v)
   defaultdict(list)[k].append(v) is extensionally identical to
   d.setdefault(k, []).append(v): both ensure the key maps to a list
   and append v.

4. defaultdict_int(d) ≡ counter(d)
   defaultdict(int) and Counter are the same ℕ-valued mapping
   for counting purposes.

5. counter_add(c1, c2) ≡ pointwise addition in ℕ^X.
6. counter_sub(c1, c2) ≡ pointwise monus  (max(0, c1[x]-c2[x])).
7. counter_intersect(c1, c2) ≡ pointwise min (meet in the lattice).
8. counter_union(c1, c2) ≡ pointwise max (join in the lattice).
9. counter_dict_comp(lst) ≡ Counter(lst)
   {x: lst.count(x) for x in set(lst)} computes the same mapping.
10. counter_update(c, lst) ≡ loop increment over lst into c.
11. counter_elements(c) ≡ chain.from_iterable(repeat(k, n) …)
12. counter_total(c) ≡ sum(c.values())
"""

EXAMPLES = [
    ("counter($lst)", "count_loop($lst)", "P31_counter_to_loop"),
    ("most_common($c, $n)", "sorted_by_count($c, $n)", "P31_most_common"),
    ("defaultdict_list($d, $k, $v)", "setdefault_append($d, $k, $v)", "P31_dd_list"),
    ("defaultdict_int($d)", "counter($d)", "P31_dd_int_to_counter"),
    ("counter_add($a, $b)", "counter_merge_add($a, $b)", "P31_counter_add"),
]

_COUNTER_OPS = frozenset({
    'counter', 'count_loop', 'most_common', 'sorted_by_count',
    'defaultdict_list', 'setdefault_append', 'defaultdict_int',
    'counter_add', 'counter_sub', 'counter_intersect', 'counter_union',
    'counter_dict_comp', 'counter_update', 'counter_elements',
    'counter_total', 'counter_merge_add', 'counter_merge_sub',
    'counter_merge_min', 'counter_merge_max', 'loop_increment',
    'sum_values', 'chain_repeat',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P31: Counter / defaultdict equivalence rewrites (forward)."""
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp):
        return results

    # ── 1. Counter(lst) ↔ count_loop(lst) ──
    if term.name == 'counter' and len(term.args) == 1:
        results.append((
            OOp('count_loop', term.args),
            'P31_counter_to_loop',
        ))
        results.append((
            OOp('counter_dict_comp', term.args),
            'P31_counter_to_dict_comp',
        ))

    if term.name == 'count_loop' and len(term.args) == 1:
        results.append((
            OOp('counter', term.args),
            'P31_loop_to_counter',
        ))

    # ── 2. counter_dict_comp(lst) → counter(lst) ──
    if term.name == 'counter_dict_comp' and len(term.args) == 1:
        results.append((
            OOp('counter', term.args),
            'P31_dict_comp_to_counter',
        ))

    # ── 3. most_common(c, n) ↔ sorted_by_count(c, n) ──
    if term.name == 'most_common' and len(term.args) == 2:
        results.append((
            OOp('sorted_by_count', term.args),
            'P31_most_common_to_sorted',
        ))

    if term.name == 'sorted_by_count' and len(term.args) == 2:
        results.append((
            OOp('most_common', term.args),
            'P31_sorted_to_most_common',
        ))

    # ── 4. defaultdict_list(d, k, v) ↔ setdefault_append(d, k, v) ──
    if term.name == 'defaultdict_list' and len(term.args) == 3:
        results.append((
            OOp('setdefault_append', term.args),
            'P31_dd_list_to_setdefault',
        ))

    if term.name == 'setdefault_append' and len(term.args) == 3:
        results.append((
            OOp('defaultdict_list', term.args),
            'P31_setdefault_to_dd_list',
        ))

    # ── 5. defaultdict_int(d) ↔ counter(d) ──
    if term.name == 'defaultdict_int' and len(term.args) == 1:
        results.append((
            OOp('counter', term.args),
            'P31_dd_int_to_counter',
        ))

    if term.name == 'counter' and len(term.args) == 1:
        results.append((
            OOp('defaultdict_int', term.args),
            'P31_counter_to_dd_int',
        ))

    # ── 6. counter_add(c1, c2) ↔ counter_merge_add(c1, c2) ──
    if term.name == 'counter_add' and len(term.args) == 2:
        results.append((
            OOp('counter_merge_add', term.args),
            'P31_counter_add_to_merge',
        ))

    if term.name == 'counter_merge_add' and len(term.args) == 2:
        results.append((
            OOp('counter_add', term.args),
            'P31_merge_to_counter_add',
        ))

    # ── 7. counter_sub(c1, c2) ↔ counter_merge_sub(c1, c2) ──
    if term.name == 'counter_sub' and len(term.args) == 2:
        results.append((
            OOp('counter_merge_sub', term.args),
            'P31_counter_sub_to_merge',
        ))

    if term.name == 'counter_merge_sub' and len(term.args) == 2:
        results.append((
            OOp('counter_sub', term.args),
            'P31_merge_to_counter_sub',
        ))

    # ── 8. counter_intersect(c1, c2) ↔ counter_merge_min(c1, c2) ──
    if term.name == 'counter_intersect' and len(term.args) == 2:
        results.append((
            OOp('counter_merge_min', term.args),
            'P31_counter_intersect_to_merge',
        ))

    if term.name == 'counter_merge_min' and len(term.args) == 2:
        results.append((
            OOp('counter_intersect', term.args),
            'P31_merge_to_counter_intersect',
        ))

    # ── 9. counter_union(c1, c2) ↔ counter_merge_max(c1, c2) ──
    if term.name == 'counter_union' and len(term.args) == 2:
        results.append((
            OOp('counter_merge_max', term.args),
            'P31_counter_union_to_merge',
        ))

    if term.name == 'counter_merge_max' and len(term.args) == 2:
        results.append((
            OOp('counter_union', term.args),
            'P31_merge_to_counter_union',
        ))

    # ── 10. counter_update(c, lst) ↔ loop_increment(c, lst) ──
    if term.name == 'counter_update' and len(term.args) == 2:
        results.append((
            OOp('loop_increment', term.args),
            'P31_update_to_loop',
        ))

    if term.name == 'loop_increment' and len(term.args) == 2:
        results.append((
            OOp('counter_update', term.args),
            'P31_loop_to_update',
        ))

    # ── 11. counter_elements(c) ↔ chain_repeat(c) ──
    if term.name == 'counter_elements' and len(term.args) == 1:
        results.append((
            OOp('chain_repeat', term.args),
            'P31_elements_to_chain',
        ))

    if term.name == 'chain_repeat' and len(term.args) == 1:
        results.append((
            OOp('counter_elements', term.args),
            'P31_chain_to_elements',
        ))

    # ── 12. counter_total(c) ↔ sum_values(c) ──
    if term.name == 'counter_total' and len(term.args) == 1:
        results.append((
            OOp('sum_values', term.args),
            'P31_total_to_sum',
        ))

    if term.name == 'sum_values' and len(term.args) == 1:
        results.append((
            OOp('counter_total', term.args),
            'P31_sum_to_total',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Return reverse rewrites (manual form → Counter/defaultdict form)."""
    inverse_labels = {
        'P31_loop_to_counter', 'P31_dict_comp_to_counter',
        'P31_sorted_to_most_common', 'P31_setdefault_to_dd_list',
        'P31_dd_int_to_counter', 'P31_merge_to_counter_add',
        'P31_merge_to_counter_sub', 'P31_merge_to_counter_intersect',
        'P31_merge_to_counter_union', 'P31_loop_to_update',
        'P31_chain_to_elements', 'P31_sum_to_total',
    }
    return [(t, l) for t, l in apply(term, ctx) if l in inverse_labels]


def recognizes(term: OTerm) -> bool:
    """Return True if the term's root operator is a Counter/defaultdict op."""
    if isinstance(term, OOp) and term.name in _COUNTER_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Heuristic relevance for search-guided rewriting."""
    sc, tc = source.canon(), target.canon()
    for kw in ('counter', 'count', 'defaultdict', 'most_common',
               'setdefault', 'elements', 'total'):
        if kw in sc and kw in tc:
            return 0.9
    if ('counter' in sc and 'loop' in tc) or ('loop' in sc and 'counter' in tc):
        return 0.85
    if ('defaultdict' in sc and 'setdefault' in tc) or \
       ('setdefault' in sc and 'defaultdict' in tc):
        return 0.85
    if any(k in sc for k in ('counter', 'defaultdict', 'count')):
        return 0.3
    return 0.05


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

    # 1. Counter → count_loop
    t = OOp('counter', (OVar('lst'),))
    r = apply(t)
    _assert(any(l == 'P31_counter_to_loop' for _, l in r), "counter → loop")

    # 2. count_loop → Counter
    t2 = OOp('count_loop', (OVar('lst'),))
    r2 = apply(t2)
    _assert(any(l == 'P31_loop_to_counter' for _, l in r2), "loop → counter")

    # 3. Counter → dict comprehension
    _assert(any(l == 'P31_counter_to_dict_comp' for _, l in r), "counter → dict_comp")

    # 4. dict_comp → Counter
    t4 = OOp('counter_dict_comp', (OVar('lst'),))
    r4 = apply(t4)
    _assert(any(l == 'P31_dict_comp_to_counter' for _, l in r4), "dict_comp → counter")

    # 5. most_common → sorted_by_count
    t5 = OOp('most_common', (OVar('c'), OLit(3)))
    r5 = apply(t5)
    _assert(any(l == 'P31_most_common_to_sorted' for _, l in r5), "most_common → sorted")

    # 6. sorted_by_count → most_common
    t6 = OOp('sorted_by_count', (OVar('c'), OLit(3)))
    r6 = apply(t6)
    _assert(any(l == 'P31_sorted_to_most_common' for _, l in r6), "sorted → most_common")

    # 7. defaultdict_list → setdefault_append
    t7 = OOp('defaultdict_list', (OVar('d'), OVar('k'), OVar('v')))
    r7 = apply(t7)
    _assert(any(l == 'P31_dd_list_to_setdefault' for _, l in r7), "dd_list → setdefault")

    # 8. setdefault_append → defaultdict_list
    t8 = OOp('setdefault_append', (OVar('d'), OVar('k'), OVar('v')))
    r8 = apply(t8)
    _assert(any(l == 'P31_setdefault_to_dd_list' for _, l in r8), "setdefault → dd_list")

    # 9. defaultdict_int → counter
    t9 = OOp('defaultdict_int', (OVar('d'),))
    r9 = apply(t9)
    _assert(any(l == 'P31_dd_int_to_counter' for _, l in r9), "dd_int → counter")

    # 10. counter_add → counter_merge_add
    t10 = OOp('counter_add', (OVar('c1'), OVar('c2')))
    r10 = apply(t10)
    _assert(any(l == 'P31_counter_add_to_merge' for _, l in r10), "add → merge_add")

    # 11. counter_sub → counter_merge_sub
    t11 = OOp('counter_sub', (OVar('c1'), OVar('c2')))
    r11 = apply(t11)
    _assert(any(l == 'P31_counter_sub_to_merge' for _, l in r11), "sub → merge_sub")

    # 12. counter_intersect → counter_merge_min
    t12 = OOp('counter_intersect', (OVar('c1'), OVar('c2')))
    r12 = apply(t12)
    _assert(any(l == 'P31_counter_intersect_to_merge' for _, l in r12), "intersect → min")

    # 13. counter_union → counter_merge_max
    t13 = OOp('counter_union', (OVar('c1'), OVar('c2')))
    r13 = apply(t13)
    _assert(any(l == 'P31_counter_union_to_merge' for _, l in r13), "union → max")

    # 14. counter_update → loop_increment
    t14 = OOp('counter_update', (OVar('c'), OVar('lst')))
    r14 = apply(t14)
    _assert(any(l == 'P31_update_to_loop' for _, l in r14), "update → loop")

    # 15. counter_elements → chain_repeat
    t15 = OOp('counter_elements', (OVar('c'),))
    r15 = apply(t15)
    _assert(any(l == 'P31_elements_to_chain' for _, l in r15), "elements → chain")

    # 16. counter_total → sum_values
    t16 = OOp('counter_total', (OVar('c'),))
    r16 = apply(t16)
    _assert(any(l == 'P31_total_to_sum' for _, l in r16), "total → sum")

    # 17. inverse: loop_increment → counter_update
    r17_inv = apply_inverse(OOp('loop_increment', (OVar('c'), OVar('lst'))))
    _assert(any(l == 'P31_loop_to_update' for _, l in r17_inv), "inv loop → update")

    # 18. recognizes counter ops
    _assert(recognizes(OOp('counter', (OVar('x'),))), "recognizes counter")
    _assert(recognizes(OOp('defaultdict_list', (OVar('d'), OVar('k'), OVar('v')))),
            "recognizes dd_list")
    _assert(not recognizes(OLit(42)), "!recognizes literal")

    # 19. relevance: counter ↔ count high
    _assert(relevance_score(
        OOp('counter', (OVar('x'),)),
        OOp('count_loop', (OVar('x'),)),
    ) > 0.7, "counter/loop relevance high")

    # 20. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2, "unrelated relevance low")

    print(f"P31 counter: {_pass} passed, {_fail} failed")
