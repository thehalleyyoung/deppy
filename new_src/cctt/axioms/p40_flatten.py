"""P40 Axiom: List Flattening Equivalences.

Establishes equivalences between different Python list-flattening
patterns: nested comprehension, itertools.chain.from_iterable,
sum(nested, []) (quadratic!), functools.reduce(operator.iadd, …),
recursive flatten, and extend-loop patterns.

Mathematical basis: flattening is the join (μ) of the list monad:

  μ : List(List(A)) → List(A)
  μ(xss) = concat(xss) = [x | xs ∈ xss, x ∈ xs]

The list monad (List, η, μ) satisfies:
  η(x) = [x]     (unit / singleton)
  μ(xss) = ⊕_{xs ∈ xss} xs   (join / concatenation)

sum(nested, []) computes μ via repeated __add__, which copies
the growing accumulator at each step → O(n²) total.

chain.from_iterable lazily yields elements → O(n) total.

The nested comprehension [x for sub in nested for x in sub]
is syntactic sugar for μ applied via iteration.

functools.reduce(operator.iadd, nested, []) uses in-place
addition, but still copies on non-list types → O(n) for lists
but semantically fragile.

Key rewrites:
  • [x for sub in nested for x in sub] ↔ chain.from_iterable(nested)
  • sum(nested, []) → chain.from_iterable(nested)   (perf upgrade)
  • reduce(iadd, nested, []) ↔ chain.from_iterable(nested)
  • extend loop ↔ chain.from_iterable
  • recursive flatten ↔ iterative flatten
  • concat_lists ↔ chain concat
  • nested map + flatten ↔ flatmap
  • flatten_depth(xs, 1) ↔ flatten_one_level(xs)

(§P40, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P40_flatten"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P01_comprehension", "P06_itertools", "P35_map_filter_reduce"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P40 List Flattening Equivalences).

1. nested_comp_flatten(xss) ≡ chain_from_iterable(xss)
   [x for sub in xss for x in sub] and
   list(itertools.chain.from_iterable(xss)) both compute
   the monadic join μ(xss).

2. sum_flatten(xss) ≡ chain_flatten(xss)
   sum(xss, []) and chain.from_iterable(xss) produce the same
   result, but sum is O(n²) due to repeated list.__add__.

3. reduce_iadd(xss) ≡ chain_reduce(xss)
   functools.reduce(operator.iadd, xss, []) and
   chain.from_iterable(xss) produce the same result.
   reduce with iadd mutates in-place for lists but is fragile.

4. extend_loop(xss) ≡ chain_extend(xss)
   result = []; for sub in xss: result.extend(sub)
   is equivalent to list(chain.from_iterable(xss)).

5. recursive_flatten(xs) ≡ iterative_flatten(xs)
   A recursive flatten that checks isinstance(x, list) and
   the iterative version using an explicit stack both produce
   the same deeply-flattened sequence.

6. concat_lists(a, b) ≡ chain_concat(a, b)
   a + b and list(chain(a, b)) both concatenate two lists.

7. flatten_depth(xs, 1) ≡ flatten_one_level(xs)
   Flattening to depth 1 is exactly the monadic join — no
   deeper recursion.

8. nested_map_flatten(f, xss) ≡ flatmap(f, xss)
   [y for x in xss for y in f(x)] ≡ flatmap(f, xss)
   This is the monadic bind (>>=) of the list monad:
   xss >>= f = μ(map(f, xss)).

9. sum_flatten → chain_from_iterable (performance upgrade).
   This is a directed rewrite: sum(xss, []) should always be
   rewritten to chain.from_iterable for O(n²) → O(n).

10. nested_comp_flatten → OFold using concat.
"""

EXAMPLES = [
    ("nested_comp_flatten($xss)", "chain_from_iterable($xss)",
     "P40_comp_to_chain"),
    ("sum_flatten($xss)", "chain_flatten($xss)",
     "P40_sum_to_chain"),
    ("reduce_iadd($xss)", "chain_reduce($xss)",
     "P40_reduce_to_chain"),
    ("extend_loop($xss)", "chain_extend($xss)",
     "P40_extend_to_chain"),
    ("nested_map_flatten($f, $xss)", "flatmap($f, $xss)",
     "P40_nested_map_to_flatmap"),
]

_FLATTEN_OPS = frozenset({
    'nested_comp_flatten', 'chain_from_iterable', 'sum_flatten',
    'chain_flatten', 'recursive_flatten', 'iterative_flatten',
    'reduce_iadd', 'chain_reduce', 'extend_loop', 'chain_extend',
    'concat_lists', 'chain_concat', 'flatten_depth',
    'flatten_one_level', 'nested_map_flatten', 'flatmap',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P40: List flattening equivalence rewrites (forward)."""
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp):
        return results

    # ── 1. nested_comp_flatten ↔ chain_from_iterable ──
    if term.name == 'nested_comp_flatten' and len(term.args) >= 1:
        results.append((
            OOp('chain_from_iterable', term.args),
            'P40_comp_to_chain',
        ))

    if term.name == 'chain_from_iterable' and len(term.args) >= 1:
        results.append((
            OOp('nested_comp_flatten', term.args),
            'P40_chain_to_comp',
        ))

    # ── 2. sum_flatten → chain_flatten (performance upgrade) ──
    if term.name == 'sum_flatten' and len(term.args) >= 1:
        results.append((
            OOp('chain_flatten', term.args),
            'P40_sum_to_chain',
        ))
        # Also emit chain_from_iterable directly
        results.append((
            OOp('chain_from_iterable', term.args),
            'P40_sum_to_chain_perf',
        ))

    if term.name == 'chain_flatten' and len(term.args) >= 1:
        results.append((
            OOp('sum_flatten', term.args),
            'P40_chain_to_sum',
        ))

    # ── 3. reduce_iadd ↔ chain_reduce ──
    if term.name == 'reduce_iadd' and len(term.args) >= 1:
        results.append((
            OOp('chain_reduce', term.args),
            'P40_reduce_to_chain',
        ))
        results.append((
            OOp('chain_from_iterable', term.args),
            'P40_reduce_to_chain_direct',
        ))

    if term.name == 'chain_reduce' and len(term.args) >= 1:
        results.append((
            OOp('reduce_iadd', term.args),
            'P40_chain_to_reduce',
        ))

    # ── 4. extend_loop ↔ chain_extend ──
    if term.name == 'extend_loop' and len(term.args) >= 1:
        results.append((
            OOp('chain_extend', term.args),
            'P40_extend_to_chain',
        ))

    if term.name == 'chain_extend' and len(term.args) >= 1:
        results.append((
            OOp('extend_loop', term.args),
            'P40_chain_to_extend',
        ))

    # ── 5. recursive_flatten ↔ iterative_flatten ──
    if term.name == 'recursive_flatten' and len(term.args) >= 1:
        results.append((
            OOp('iterative_flatten', term.args),
            'P40_recursive_to_iterative',
        ))

    if term.name == 'iterative_flatten' and len(term.args) >= 1:
        results.append((
            OOp('recursive_flatten', term.args),
            'P40_iterative_to_recursive',
        ))

    # ── 6. concat_lists ↔ chain_concat ──
    if term.name == 'concat_lists' and len(term.args) == 2:
        results.append((
            OOp('chain_concat', term.args),
            'P40_concat_to_chain',
        ))

    if term.name == 'chain_concat' and len(term.args) == 2:
        results.append((
            OOp('concat_lists', term.args),
            'P40_chain_to_concat',
        ))

    # ── 7. flatten_depth(xs, 1) ↔ flatten_one_level ──
    if term.name == 'flatten_depth' and len(term.args) == 2:
        xs, depth = term.args
        if isinstance(depth, OLit) and depth.value == 1:
            results.append((
                OOp('flatten_one_level', (xs,)),
                'P40_depth1_to_one_level',
            ))
        results.append((
            OOp('flatten_one_level', (xs,)),
            'P40_depth_to_one_level',
        ))

    if term.name == 'flatten_one_level' and len(term.args) == 1:
        results.append((
            OOp('flatten_depth', (term.args[0], OLit(1))),
            'P40_one_level_to_depth1',
        ))
        results.append((
            OOp('chain_from_iterable', term.args),
            'P40_one_level_to_chain',
        ))

    # ── 8. nested_map_flatten ↔ flatmap ──
    if term.name == 'nested_map_flatten' and len(term.args) == 2:
        results.append((
            OOp('flatmap', term.args),
            'P40_nested_map_to_flatmap',
        ))

    if term.name == 'flatmap' and len(term.args) == 2:
        results.append((
            OOp('nested_map_flatten', term.args),
            'P40_flatmap_to_nested_map',
        ))

    # ── 9. nested_comp_flatten → extend_loop (alternative) ──
    if term.name == 'nested_comp_flatten' and len(term.args) >= 1:
        results.append((
            OOp('extend_loop', term.args),
            'P40_comp_to_extend',
        ))

    # ── 10. nested_comp_flatten → OFold form ──
    if term.name == 'nested_comp_flatten' and len(term.args) == 1:
        xss = term.args[0]
        results.append((
            OFold('concat', OSeq(()), xss),
            'P40_comp_to_fold_concat',
        ))

    # ── 11. flatmap → OMap + chain (structural) ──
    if term.name == 'flatmap' and len(term.args) == 2:
        f, xss = term.args
        results.append((
            OOp('chain_from_iterable', (OMap(f, xss),)),
            'P40_flatmap_to_chain_map',
        ))

    # ── 12. sum_flatten with literal nested seq → OSeq ──
    if term.name == 'sum_flatten' and len(term.args) == 1:
        xss = term.args[0]
        if isinstance(xss, OSeq) and all(
                isinstance(s, OSeq) for s in xss.elements):
            flat_elems: list[OTerm] = []
            for sub in xss.elements:
                assert isinstance(sub, OSeq)
                flat_elems.extend(sub.elements)
            results.append((
                OSeq(tuple(flat_elems)),
                'P40_sum_literal_to_seq',
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Return reverse rewrites (chain/functional → manual/loop form)."""
    inverse_labels = {
        'P40_chain_to_comp', 'P40_chain_to_sum',
        'P40_chain_to_reduce', 'P40_chain_to_extend',
        'P40_iterative_to_recursive', 'P40_chain_to_concat',
        'P40_one_level_to_depth1', 'P40_flatmap_to_nested_map',
    }
    return [(t, l) for t, l in apply(term, ctx) if l in inverse_labels]


def recognizes(term: OTerm) -> bool:
    """Return True if the term's root operator is a flatten op."""
    if isinstance(term, OOp) and term.name in _FLATTEN_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Heuristic relevance for search-guided rewriting."""
    sc, tc = source.canon(), target.canon()
    for kw in ('flatten', 'chain', 'concat', 'extend', 'reduce',
               'flatmap', 'nested', 'sum'):
        if kw in sc and kw in tc:
            return 0.9
    if ('flatten' in sc and 'chain' in tc) or \
       ('chain' in sc and 'flatten' in tc):
        return 0.85
    if ('sum' in sc and 'chain' in tc) or \
       ('chain' in sc and 'sum' in tc):
        return 0.85
    if ('comp' in sc and 'chain' in tc) or \
       ('chain' in sc and 'comp' in tc):
        return 0.8
    if ('flatmap' in sc and 'nested' in tc) or \
       ('nested' in sc and 'flatmap' in tc):
        return 0.8
    if any(k in sc for k in ('flatten', 'chain', 'concat', 'flatmap')):
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

    # 1. nested_comp_flatten → chain_from_iterable
    t = OOp('nested_comp_flatten', (OVar('xss'),))
    r = apply(t)
    _assert(any(l == 'P40_comp_to_chain' for _, l in r),
            "comp → chain")

    # 2. chain_from_iterable → nested_comp_flatten
    t2 = OOp('chain_from_iterable', (OVar('xss'),))
    r2 = apply(t2)
    _assert(any(l == 'P40_chain_to_comp' for _, l in r2),
            "chain → comp")

    # 3. sum_flatten → chain_flatten
    t3 = OOp('sum_flatten', (OVar('xss'),))
    r3 = apply(t3)
    _assert(any(l == 'P40_sum_to_chain' for _, l in r3),
            "sum → chain")

    # 4. sum_flatten → chain_from_iterable (perf)
    _assert(any(l == 'P40_sum_to_chain_perf' for _, l in r3),
            "sum → chain perf")

    # 5. chain_flatten → sum_flatten
    t5 = OOp('chain_flatten', (OVar('xss'),))
    r5 = apply(t5)
    _assert(any(l == 'P40_chain_to_sum' for _, l in r5),
            "chain → sum")

    # 6. reduce_iadd → chain_reduce
    t6 = OOp('reduce_iadd', (OVar('xss'),))
    r6 = apply(t6)
    _assert(any(l == 'P40_reduce_to_chain' for _, l in r6),
            "reduce → chain")

    # 7. chain_reduce → reduce_iadd
    t7 = OOp('chain_reduce', (OVar('xss'),))
    r7 = apply(t7)
    _assert(any(l == 'P40_chain_to_reduce' for _, l in r7),
            "chain → reduce")

    # 8. extend_loop → chain_extend
    t8 = OOp('extend_loop', (OVar('xss'),))
    r8 = apply(t8)
    _assert(any(l == 'P40_extend_to_chain' for _, l in r8),
            "extend → chain")

    # 9. chain_extend → extend_loop
    t9 = OOp('chain_extend', (OVar('xss'),))
    r9 = apply(t9)
    _assert(any(l == 'P40_chain_to_extend' for _, l in r9),
            "chain → extend")

    # 10. recursive_flatten → iterative_flatten
    t10 = OOp('recursive_flatten', (OVar('xs'),))
    r10 = apply(t10)
    _assert(any(l == 'P40_recursive_to_iterative' for _, l in r10),
            "recursive → iterative")

    # 11. iterative_flatten → recursive_flatten
    t11 = OOp('iterative_flatten', (OVar('xs'),))
    r11 = apply(t11)
    _assert(any(l == 'P40_iterative_to_recursive' for _, l in r11),
            "iterative → recursive")

    # 12. concat_lists → chain_concat
    t12 = OOp('concat_lists', (OVar('a'), OVar('b')))
    r12 = apply(t12)
    _assert(any(l == 'P40_concat_to_chain' for _, l in r12),
            "concat → chain")

    # 13. chain_concat → concat_lists
    t13 = OOp('chain_concat', (OVar('a'), OVar('b')))
    r13 = apply(t13)
    _assert(any(l == 'P40_chain_to_concat' for _, l in r13),
            "chain → concat")

    # 14. flatten_depth(xs, 1) → flatten_one_level
    t14 = OOp('flatten_depth', (OVar('xs'), OLit(1)))
    r14 = apply(t14)
    _assert(any(l == 'P40_depth1_to_one_level' for _, l in r14),
            "depth(1) → one_level")

    # 15. flatten_one_level → flatten_depth(xs, 1)
    t15 = OOp('flatten_one_level', (OVar('xs'),))
    r15 = apply(t15)
    _assert(any(l == 'P40_one_level_to_depth1' for _, l in r15),
            "one_level → depth(1)")

    # 16. nested_map_flatten → flatmap
    t16 = OOp('nested_map_flatten', (OVar('f'), OVar('xss')))
    r16 = apply(t16)
    _assert(any(l == 'P40_nested_map_to_flatmap' for _, l in r16),
            "nested_map → flatmap")

    # 17. flatmap → nested_map_flatten
    t17 = OOp('flatmap', (OVar('f'), OVar('xss')))
    r17 = apply(t17)
    _assert(any(l == 'P40_flatmap_to_nested_map' for _, l in r17),
            "flatmap → nested_map")

    # 18. flatmap → chain_from_iterable(map(…))
    _assert(any(l == 'P40_flatmap_to_chain_map' for _, l in r17),
            "flatmap → chain(map)")

    # 19. nested_comp_flatten → extend_loop (alternative)
    _assert(any(l == 'P40_comp_to_extend' for _, l in r),
            "comp → extend")

    # 20. nested_comp_flatten → OFold form
    _assert(any(l == 'P40_comp_to_fold_concat' for _, l in r),
            "comp → fold(concat)")

    # 21. flatten_one_level → chain_from_iterable
    _assert(any(l == 'P40_one_level_to_chain' for _, l in r15),
            "one_level → chain")

    # 22. sum_flatten with literal nested → OSeq
    t22 = OOp('sum_flatten', (OSeq((
        OSeq((OLit(1), OLit(2))),
        OSeq((OLit(3),)),
        OSeq((OLit(4), OLit(5))),
    )),))
    r22 = apply(t22)
    _assert(any(l == 'P40_sum_literal_to_seq' for _, l in r22),
            "sum literal → seq")
    seq_results = [(t, l) for t, l in r22 if l == 'P40_sum_literal_to_seq']
    if seq_results:
        seq_term = seq_results[0][0]
        _assert(isinstance(seq_term, OSeq) and len(seq_term.elements) == 5,
                "flattened seq has 5 elements")
    else:
        _assert(False, "flattened seq has 5 elements")

    # 23. inverse: chain → comp
    r23_inv = apply_inverse(OOp('chain_from_iterable', (OVar('xss'),)))
    _assert(any(l == 'P40_chain_to_comp' for _, l in r23_inv),
            "inv: chain → comp")

    # 24. inverse: chain → extend
    r24_inv = apply_inverse(OOp('chain_extend', (OVar('xss'),)))
    _assert(any(l == 'P40_chain_to_extend' for _, l in r24_inv),
            "inv: chain → extend")

    # 25. recognizes flatten ops
    _assert(recognizes(OOp('nested_comp_flatten', (OVar('xss'),))),
            "recognizes nested_comp_flatten")
    _assert(recognizes(OOp('chain_from_iterable', (OVar('xss'),))),
            "recognizes chain_from_iterable")
    _assert(recognizes(OOp('flatmap', (OVar('f'), OVar('xss')))),
            "recognizes flatmap")
    _assert(not recognizes(OLit(42)), "!recognizes literal")
    _assert(not recognizes(OVar('x')), "!recognizes var")

    # 26. relevance: flatten ↔ chain high
    _assert(relevance_score(
        OOp('nested_comp_flatten', (OVar('xss'),)),
        OOp('chain_from_iterable', (OVar('xss'),)),
    ) > 0.7, "flatten/chain relevance high")

    # 27. relevance: flatmap ↔ nested high
    _assert(relevance_score(
        OOp('flatmap', (OVar('f'), OVar('xss'))),
        OOp('nested_map_flatten', (OVar('f'), OVar('xss'))),
    ) > 0.7, "flatmap/nested relevance high")

    # 28. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2,
            "unrelated relevance low")

    # 29. reduce_iadd → chain_from_iterable direct
    _assert(any(l == 'P40_reduce_to_chain_direct' for _, l in r6),
            "reduce → chain direct")

    # 30. inverse: iterative → recursive
    r30_inv = apply_inverse(OOp('iterative_flatten', (OVar('xs'),)))
    _assert(any(l == 'P40_iterative_to_recursive' for _, l in r30_inv),
            "inv: iterative → recursive")

    print(f"P40 flatten: {_pass} passed, {_fail} failed")
