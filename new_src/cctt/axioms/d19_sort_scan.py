"""D19: Sort Absorption Axiom — Sort-then-Scan ↔ Direct Sweep.

§22.5 of the CCTT monograph.  Theorem 22.5.1 (Sort Absorption):
fold(op, sorted(x)) ≡ fold(op, x) when op is commutative+associative.

Key rewrites:
  • fold(op, sorted(x)) → fold(op, x)       [order-invariant fold]
  • fold(op, sorted_key(x, k)) → fold(op, x) [keyed-sort irrelevant]
  • reversed(sorted(x)) → sorted_reverse(x)  [normalisation]
  • fold(op, Q[perm](x)) → fold(op, x)       [quotient-fold interaction]
  • stable_sort(x) ↔ sorted(x) ↔ unstable_sort(x)  [stability axiom]
  • sorted(sorted(x)) → sorted(x)            [idempotence]
  • list(sorted(x)) → sorted(x)              [list absorption]
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "D19_sort_scan"
AXIOM_CATEGORY = "algorithmic_strategy"

SOUNDNESS_PROOF = """
Theorem 22.5.1 (Sort Absorption).  Let (M, ⊕, e) be a commutative
monoid.  Then for any finite multiset S,
    fold(⊕, e, sort(S)) = fold(⊕, e, S)
because commutativity + associativity make fold invariant under
permutations.  Formally: the fold lifts through the quotient
map π: List → Multiset, so sorted order is absorbed.

Sort idempotence: sorted ∘ sorted = sorted by definition —
the image of sorted is already in sorted order.

Quotient-fold: fold(⊕, Q[perm](x)) = fold(⊕, x) because
the quotient forgets ordering, and ⊕ is permutation-invariant.
"""

COMPOSES_WITH = ["QUOT", "D17_assoc", "FOLD", "ALG"]
REQUIRES: List[str] = []

EXAMPLES = [
    ("fold[add](0, sorted(xs))", "fold[add](0, xs)", "D19_sort_irrelevant"),
    ("fold[mul](1, sorted_key(xs, key))", "fold[mul](1, xs)", "D19_keyed_sort_irrelevant"),
    ("reversed(sorted(xs))", "sorted_reverse(xs)", "D19_reversed_sorted_normalise"),
    ("fold[add](0, Q[perm](xs))", "fold[add](0, xs)", "D19_quotient_fold_absorb"),
    ("sorted(sorted(xs))", "sorted(xs)", "D19_sort_idempotent"),
]

# ── Commutative-op check ─────────────────────────────────────

COMMUTATIVE_OPS: FrozenSet[str] = frozenset({
    'add', '.add', 'iadd', 'mul', '.mul', 'imul', 'mult',
    'and', 'or', 'bitor', 'bitand', 'bitxor',
    'min', 'max', 'eq', 'noteq',
    'union', 'intersection', '.count',
    'gcd', 'lcm',
})


def _is_commutative_op(op_name: str) -> bool:
    return op_name in COMMUTATIVE_OPS


# ── FiberCtx (local lightweight copy) ─────────────────────

@dataclass
class FiberCtx:
    param_duck_types: Dict[str, str] = field(default_factory=dict)

    def is_numeric(self, term: OTerm) -> bool:
        return True  # conservative for standalone use


# ── Core axiom application ──────────────────────────────────

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D19 sort-absorption rewrites to *term*.

    Returns list of (rewritten_term, axiom_label) pairs.
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── 1. fold(op, sorted(x)) → fold(op, x)  [commutative fold] ──
    if isinstance(term, OFold):
        if isinstance(term.collection, OOp) and term.collection.name == 'sorted':
            if _is_commutative_op(term.op_name):
                inner = term.collection.args[0] if term.collection.args else term.collection
                results.append((
                    OFold(term.op_name, term.init, inner),
                    'D19_sort_irrelevant',
                ))

        # ── 2. fold(op, sorted_key(x, k)) → fold(op, x) ──
        if isinstance(term.collection, OOp) and term.collection.name == 'sorted_key':
            if _is_commutative_op(term.op_name):
                if len(term.collection.args) >= 1:
                    results.append((
                        OFold(term.op_name, term.init, term.collection.args[0]),
                        'D19_keyed_sort_irrelevant',
                    ))

        # ── 3. fold(op, sorted_rev(x)) → fold(op, x) ──
        if isinstance(term.collection, OOp) and term.collection.name in ('sorted_rev', 'sorted_reverse'):
            if _is_commutative_op(term.op_name):
                if len(term.collection.args) >= 1:
                    results.append((
                        OFold(term.op_name, term.init, term.collection.args[0]),
                        'D19_reverse_sort_fold_irrelevant',
                    ))

        # ── 4. fold(op, reversed(sorted(x))) → fold(op, x) ──
        if isinstance(term.collection, OOp) and term.collection.name == 'reversed':
            if len(term.collection.args) == 1:
                inner = term.collection.args[0]
                if isinstance(inner, OOp) and inner.name == 'sorted':
                    if _is_commutative_op(term.op_name):
                        src = inner.args[0] if inner.args else inner
                        results.append((
                            OFold(term.op_name, term.init, src),
                            'D19_reverse_sort_irrelevant',
                        ))

        # ── 5. fold(op, Q[perm](x)) → fold(op, x)  [quotient absorption] ──
        if isinstance(term.collection, OQuotient) and term.collection.equiv_class == 'perm':
            if _is_commutative_op(term.op_name):
                results.append((
                    OFold(term.op_name, term.init, term.collection.inner),
                    'D19_quotient_fold_absorb',
                ))

    # ── 6. reversed(sorted(x)) → sorted_reverse(x)  [normalisation] ──
    if isinstance(term, OOp) and term.name == 'reversed':
        if len(term.args) == 1 and isinstance(term.args[0], OOp):
            if term.args[0].name == 'sorted':
                results.append((
                    OOp('sorted_reverse', term.args[0].args),
                    'D19_reversed_sorted_normalise',
                ))

    # ── 7. sorted(sorted(x)) → sorted(x)  [idempotence] ──
    if isinstance(term, OOp) and term.name == 'sorted':
        if len(term.args) == 1 and isinstance(term.args[0], OOp):
            if term.args[0].name == 'sorted':
                results.append((
                    term.args[0],
                    'D19_sort_idempotent',
                ))

    # ── 8. list(sorted(x)) → sorted(x)  [list-of-sorted absorption] ──
    if isinstance(term, OOp) and term.name == 'list':
        if len(term.args) == 1 and isinstance(term.args[0], OOp):
            if term.args[0].name == 'sorted':
                results.append((
                    term.args[0],
                    'D19_list_sorted_absorb',
                ))

    # ── 9. Sort stability: stable_sort ↔ sorted ──
    if isinstance(term, OOp) and term.name == 'stable_sort':
        results.append((
            OOp('sorted', term.args),
            'D19_stability_to_sorted',
        ))
    if isinstance(term, OOp) and term.name == 'sorted':
        results.append((
            OOp('stable_sort', term.args),
            'D19_sorted_to_stability',
        ))
    if isinstance(term, OOp) and term.name in ('sorted', 'stable_sort'):
        if len(term.args) == 1:
            results.append((
                OOp('unstable_sort', term.args),
                'D19_sort_unique_keys_unstable',
            ))

    # ── 10. sorted(x) with reverse=True normalisation ──
    if isinstance(term, OOp) and term.name == 'sorted_rev':
        if len(term.args) >= 1:
            results.append((
                OOp('reversed', (OOp('sorted', (term.args[0],)),)),
                'D19_sorted_rev_expand',
            ))

    return results


def recognizes(term: OTerm) -> bool:
    """Return True if D19 can potentially rewrite *term*."""
    if isinstance(term, OFold):
        coll = term.collection
        if isinstance(coll, OOp) and coll.name in ('sorted', 'sorted_key', 'sorted_rev',
                                                     'sorted_reverse', 'reversed'):
            return True
        if isinstance(coll, OQuotient) and coll.equiv_class == 'perm':
            return True
    if isinstance(term, OOp) and term.name in ('reversed', 'sorted', 'stable_sort',
                                                 'sorted_rev', 'list', 'unstable_sort'):
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D19's relevance for bridging *source* → *target*."""
    sc = source.canon()
    tc = target.canon()
    s_sorted = 'sorted(' in sc or 'sorted_key(' in sc or 'stable_sort(' in sc
    t_sorted = 'sorted(' in tc or 'sorted_key(' in tc or 'stable_sort(' in tc
    if s_sorted != t_sorted:
        return 0.9
    if s_sorted and t_sorted:
        return 0.3
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse direction: inject sorting where it is absent.

    fold(op, x) → fold(op, sorted(x)) when op is commutative.
    This is sound but rarely useful — included for bidirectional search.
    """
    results: List[Tuple[OTerm, str]] = []

    if isinstance(term, OFold):
        if not (isinstance(term.collection, OOp) and
                term.collection.name in ('sorted', 'sorted_key', 'reversed')):
            if _is_commutative_op(term.op_name):
                results.append((
                    OFold(term.op_name, term.init, OOp('sorted', (term.collection,))),
                    'D19_sort_inject',
                ))

    if isinstance(term, OOp) and term.name == 'sorted_reverse':
        if len(term.args) >= 1:
            results.append((
                OOp('reversed', (OOp('sorted', (term.args[0],)),)),
                'D19_sorted_reverse_expand',
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

    # fold(add, 0, sorted(xs)) → fold(add, 0, xs)
    t1 = OFold('add', OLit(0), OOp('sorted', (xs,)))
    r1 = apply(t1, ctx)
    _assert(any(a == 'D19_sort_irrelevant' for _, a in r1), "sort absorption for add fold")

    # Keyed sort absorption
    t2 = OFold('mul', OLit(1), OOp('sorted_key', (xs, OLam(('x',), OVar('x')))))
    r2 = apply(t2, ctx)
    _assert(any(a == 'D19_keyed_sort_irrelevant' for _, a in r2), "keyed sort absorption")

    # reversed(sorted(xs)) normalisation
    t3 = OOp('reversed', (OOp('sorted', (xs,)),))
    r3 = apply(t3, ctx)
    _assert(any(a == 'D19_reversed_sorted_normalise' for _, a in r3), "reversed-sorted normalise")

    # Quotient-fold absorption
    t4 = OFold('add', OLit(0), OQuotient(xs, 'perm'))
    r4 = apply(t4, ctx)
    _assert(any(a == 'D19_quotient_fold_absorb' for _, a in r4), "quotient-fold absorb")

    # Sort idempotence
    t5 = OOp('sorted', (OOp('sorted', (xs,)),))
    r5 = apply(t5, ctx)
    _assert(any(a == 'D19_sort_idempotent' for _, a in r5), "sort idempotence")

    # list(sorted(x)) → sorted(x)
    t6 = OOp('list', (OOp('sorted', (xs,)),))
    r6 = apply(t6, ctx)
    _assert(any(a == 'D19_list_sorted_absorb' for _, a in r6), "list-sorted absorption")

    # Stability axiom
    t7 = OOp('stable_sort', (xs,))
    r7 = apply(t7, ctx)
    _assert(any(a == 'D19_stability_to_sorted' for _, a in r7), "stability to sorted")

    # Non-commutative fold should NOT fire
    t8 = OFold('sub', OLit(0), OOp('sorted', (xs,)))
    r8 = apply(t8, ctx)
    _assert(not any(a == 'D19_sort_irrelevant' for _, a in r8), "sub is not commutative")

    # Recognizes
    _assert(recognizes(t1), "recognizes fold-over-sorted")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # Inverse
    t9 = OFold('add', OLit(0), xs)
    r9 = apply_inverse(t9, ctx)
    _assert(any(a == 'D19_sort_inject' for _, a in r9), "inverse sort injection")

    # Relevance
    _assert(relevance_score(t1, OFold('add', OLit(0), xs)) > 0.5,
            "high relevance when sorted on one side")

    # reversed(sorted(x)) in fold
    t10 = OFold('add', OLit(0), OOp('reversed', (OOp('sorted', (xs,)),)))
    r10 = apply(t10, ctx)
    _assert(any(a == 'D19_reverse_sort_irrelevant' for _, a in r10),
            "reversed-sorted fold absorption")

    print(f"D19 sort-scan: {_pass} passed, {_fail} failed")
