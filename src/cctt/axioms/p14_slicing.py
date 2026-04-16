"""P14 Axiom: Sequence Slicing Equivalences.

Establishes equivalences between different Python sequence access
patterns: indexing, slicing, reversal, concatenation, repetition.

Mathematical basis: A Python list is a finite sequence
    xs : Fin(n) → T
Slicing is a restriction to a sub-index set:
    xs[i:j] = xs ∘ ι   where ι : Fin(j-i) ↪ Fin(n), k ↦ i+k.
Reversal is pre-composition with the order-reversing bijection:
    xs[::-1] = xs ∘ σ   where σ(k) = n-1-k.
Concatenation is the coproduct in FinSeq:
    xs + ys : Fin(m+n) → T.

Key rewrites:
  • xs[0]    ↔ next(iter(xs))        (first element)
  • xs[-1]   ↔ xs[len(xs)-1]         (last element)
  • xs[:n]   ↔ list(islice(xs, n))   (prefix)
  • xs[::2]  ↔ [xs[i] for i in range(0, len(xs), 2)]  (stride)
  • xs[::-1] ↔ list(reversed(xs))    (reversal)
  • xs + ys  ↔ [*xs, *ys]            (concatenation)
  • xs * n   ↔ chain.from_iterable([xs]*n)  (repetition)

(§P14, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P14_slicing"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["D4_comp_fusion", "D1_fold_unfold", "P13_bool_idioms"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P14 Slicing Equivalence).

Let xs : List[T] with len(xs) = n.

1. xs[0] ≡ next(iter(xs))
   Both denote the first element xs₀.  iter(xs) produces elements
   in order; next yields the first.  Undefined when n = 0.

2. xs[-1] ≡ xs[len(xs)-1]
   Python negative indexing: xs[-k] = xs[n-k].

3. xs[::-1] ≡ list(reversed(xs))
   Both compute [xₙ₋₁, xₙ₋₂, ..., x₀].  reversed() returns an
   iterator, list() materializes it.  The slice notation is sugar
   for the same reversal.

4. xs + ys ≡ [*xs, *ys]
   Both denote the concatenation sequence of length m+n.

5. xs * k ≡ xs ++ xs ++ ... ++ xs  (k times)
   Sequence repetition is iterated concatenation.

6. xs[:n] ≡ list(itertools.islice(xs, n))
   Both restrict to the first min(n, len(xs)) elements.
"""

EXAMPLES = [
    ("getitem($xs, 0)", "next(iter($xs))", "P14_first_element"),
    ("getitem($xs, -1)", "getitem($xs, sub(len($xs), 1))", "P14_last_neg"),
    ("slice_rev($xs)", "list(reversed($xs))", "P14_reverse"),
    ("add($xs, $ys)", "unpack_concat($xs, $ys)", "P14_concat"),
]


def _is_zero(term: OTerm) -> bool:
    return isinstance(term, OLit) and term.value == 0


def _is_neg_one(term: OTerm) -> bool:
    return isinstance(term, OLit) and term.value == -1


def _is_getitem(term: OTerm) -> bool:
    return isinstance(term, OOp) and term.name == 'getitem' and len(term.args) == 2


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P14: Sequence slicing rewrites.

    Handles:
      1. getitem(xs, 0) → next(iter(xs))
      2. getitem(xs, -1) → getitem(xs, sub(len(xs), 1))
      3. slice_rev(xs) → reversed(xs)
      4. add(xs, ys) → unpack_concat(xs, ys)  [*xs, *ys]
      5. slice(xs) → list(islice(xs, ...))
      6. mult(xs, n) → chain_repeat(xs, n)
      7. reversed(reversed(xs)) → xs  (involution)
      8. list(reversed(xs)) ↔ slice_rev(xs)
    """
    results: List[Tuple[OTerm, str]] = []

    # ── 1. getitem(xs, 0) → next(iter(xs)) ──
    if _is_getitem(term):
        xs, idx = term.args
        if _is_zero(idx):
            results.append((
                OOp('next', (OOp('iter', (xs,)),)),
                'P14_index0_to_next_iter',
            ))
        # ── 2. getitem(xs, -1) → getitem(xs, sub(len(xs), 1)) ──
        if _is_neg_one(idx):
            results.append((
                OOp('getitem', (xs, OOp('sub', (OOp('len', (xs,)), OLit(1))))),
                'P14_neg1_to_len_minus1',
            ))

    # ── 3. slice_rev(xs) ↔ list(reversed(xs)) ──
    if isinstance(term, OOp) and term.name == 'slice_rev' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OOp('list', (OOp('reversed', (xs,)),)),
            'P14_slice_rev_to_reversed',
        ))

    if isinstance(term, OOp) and term.name == 'list' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'reversed' and len(inner.args) == 1:
            results.append((
                OOp('slice_rev', (inner.args[0],)),
                'P14_reversed_to_slice_rev',
            ))

    # ── 4. add(xs, ys) → unpack_concat ──
    if isinstance(term, OOp) and term.name == 'add' and len(term.args) == 2:
        xs, ys = term.args
        results.append((
            OOp('unpack_concat', (xs, ys)),
            'P14_add_to_unpack_concat',
        ))

    if isinstance(term, OOp) and term.name == 'unpack_concat' and len(term.args) == 2:
        xs, ys = term.args
        results.append((
            OOp('add', (xs, ys)),
            'P14_unpack_concat_to_add',
        ))

    # ── 5. slice_prefix(xs, n) ↔ list(islice(xs, n)) ──
    if isinstance(term, OOp) and term.name == 'slice_prefix' and len(term.args) == 2:
        xs, n = term.args
        results.append((
            OOp('list', (OOp('islice', (xs, n)),)),
            'P14_slice_prefix_to_islice',
        ))

    if isinstance(term, OOp) and term.name == 'list' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'islice' and len(inner.args) == 2:
            results.append((
                OOp('slice_prefix', inner.args),
                'P14_islice_to_slice_prefix',
            ))

    # ── 6. mult(xs, n) → chain_repeat(xs, n) ──
    if isinstance(term, OOp) and term.name == 'mult' and len(term.args) == 2:
        xs, n = term.args
        results.append((
            OOp('chain_repeat', (xs, n)),
            'P14_mult_to_chain_repeat',
        ))

    # ── 7. reversed(reversed(xs)) → xs ──
    if isinstance(term, OOp) and term.name == 'reversed' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'reversed' and len(inner.args) == 1:
            results.append((
                inner.args[0],
                'P14_reversed_involution',
            ))

    # ── 8. slice_stride(xs, 2) ↔ comp form ──
    if isinstance(term, OOp) and term.name == 'slice_stride' and len(term.args) == 2:
        xs, step = term.args
        lam = OLam(('_i',), OOp('getitem', (xs, OVar('_i'))))
        rng = OOp('range', (OLit(0), OOp('len', (xs,)), step))
        results.append((
            OMap(lam, rng),
            'P14_stride_to_comprehension',
        ))

    # ── 9. slice_range(xs, i, j) ↔ [xs[k] for k in range(i,j)] ──
    if isinstance(term, OOp) and term.name == 'slice_range' and len(term.args) == 3:
        xs, i, j = term.args
        lam = OLam(('_k',), OOp('getitem', (xs, OVar('_k'))))
        rng = OOp('range', (i, j))
        results.append((
            OMap(lam, rng),
            'P14_slice_range_to_comprehension',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Recognizer & scoring
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    if isinstance(term, OOp):
        if term.name in ('getitem', 'slice_rev', 'slice_prefix', 'slice_stride',
                         'slice_range', 'reversed', 'mult', 'add', 'unpack_concat'):
            return True
        if term.name == 'list' and len(term.args) == 1:
            inner = term.args[0]
            if isinstance(inner, OOp) and inner.name in ('reversed', 'islice'):
                return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    sc, tc = source.canon(), target.canon()
    if 'slice' in sc or 'slice' in tc:
        return 0.8
    if 'getitem' in sc and ('next' in tc or 'iter' in tc):
        return 0.7
    if 'reversed' in sc or 'reversed' in tc:
        return 0.7
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse: expand back to original forms."""
    results: List[Tuple[OTerm, str]] = []

    # next(iter(xs)) → getitem(xs, 0)
    if isinstance(term, OOp) and term.name == 'next' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'iter' and len(inner.args) == 1:
            results.append((
                OOp('getitem', (inner.args[0], OLit(0))),
                'P14_inv_next_iter_to_index0',
            ))

    # chain_repeat(xs, n) → mult(xs, n)
    if isinstance(term, OOp) and term.name == 'chain_repeat' and len(term.args) == 2:
        results.append((
            OOp('mult', term.args),
            'P14_inv_chain_repeat_to_mult',
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

    # 1. getitem(xs, 0) → next(iter(xs))
    t1 = OOp('getitem', (OVar('xs'), OLit(0)))
    r1 = apply(t1)
    _assert(any(a == 'P14_index0_to_next_iter' for _, a in r1), "xs[0] → next(iter(xs))")

    # 2. getitem(xs, -1) → getitem(xs, len(xs)-1)
    t2 = OOp('getitem', (OVar('xs'), OLit(-1)))
    r2 = apply(t2)
    _assert(any(a == 'P14_neg1_to_len_minus1' for _, a in r2), "xs[-1] → xs[len-1]")

    # 3. slice_rev → reversed
    t3 = OOp('slice_rev', (OVar('xs'),))
    r3 = apply(t3)
    _assert(any(a == 'P14_slice_rev_to_reversed' for _, a in r3), "slice_rev → reversed")

    # 4. list(reversed(xs)) → slice_rev(xs)
    t4 = OOp('list', (OOp('reversed', (OVar('xs'),)),))
    r4 = apply(t4)
    _assert(any(a == 'P14_reversed_to_slice_rev' for _, a in r4), "list(reversed) → slice_rev")

    # 5. add(xs, ys) → unpack_concat
    t5 = OOp('add', (OVar('xs'), OVar('ys')))
    r5 = apply(t5)
    _assert(any(a == 'P14_add_to_unpack_concat' for _, a in r5), "add → unpack_concat")

    # 6. unpack_concat → add
    t6 = OOp('unpack_concat', (OVar('xs'), OVar('ys')))
    r6 = apply(t6)
    _assert(any(a == 'P14_unpack_concat_to_add' for _, a in r6), "unpack_concat → add")

    # 7. slice_prefix → islice
    t7 = OOp('slice_prefix', (OVar('xs'), OLit(3)))
    r7 = apply(t7)
    _assert(any(a == 'P14_slice_prefix_to_islice' for _, a in r7), "slice_prefix → islice")

    # 8. list(islice(xs, n)) → slice_prefix
    t8 = OOp('list', (OOp('islice', (OVar('xs'), OLit(3))),))
    r8 = apply(t8)
    _assert(any(a == 'P14_islice_to_slice_prefix' for _, a in r8), "islice → slice_prefix")

    # 9. mult → chain_repeat
    t9 = OOp('mult', (OVar('xs'), OLit(3)))
    r9 = apply(t9)
    _assert(any(a == 'P14_mult_to_chain_repeat' for _, a in r9), "mult → chain_repeat")

    # 10. reversed(reversed(xs)) → xs
    t10 = OOp('reversed', (OOp('reversed', (OVar('xs'),)),))
    r10 = apply(t10)
    _assert(any(a == 'P14_reversed_involution' for _, a in r10), "reversed involution")

    # 11. slice_stride → comprehension
    t11 = OOp('slice_stride', (OVar('xs'), OLit(2)))
    r11 = apply(t11)
    _assert(any(a == 'P14_stride_to_comprehension' for _, a in r11), "stride → comp")

    # 12. slice_range → comprehension
    t12 = OOp('slice_range', (OVar('xs'), OLit(1), OLit(5)))
    r12 = apply(t12)
    _assert(any(a == 'P14_slice_range_to_comprehension' for _, a in r12), "range → comp")

    # 13. recognizes
    _assert(recognizes(t1), "recognizes getitem")
    _assert(recognizes(t3), "recognizes slice_rev")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # 14. inverse: next(iter) → getitem 0
    t14 = OOp('next', (OOp('iter', (OVar('xs'),)),))
    r14 = apply_inverse(t14)
    _assert(any(a == 'P14_inv_next_iter_to_index0' for _, a in r14), "inv next → xs[0]")

    # 15. inverse: chain_repeat → mult
    t15 = OOp('chain_repeat', (OVar('xs'), OLit(3)))
    r15 = apply_inverse(t15)
    _assert(any(a == 'P14_inv_chain_repeat_to_mult' for _, a in r15), "inv chain → mult")

    print(f"P14 slicing: {_pass} passed, {_fail} failed")
