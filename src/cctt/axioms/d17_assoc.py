"""D17: Associativity-Mediated Refactoring (Theorem 22.3.1).

Tree-fold vs flat-fold, left-fold vs right-fold for associative ops.

Mathematical foundation:
  When (M, ⊕) is a semigroup (⊕ is associative), the evaluation
  order of a multi-argument expression is irrelevant:
    (a ⊕ b) ⊕ c  =  a ⊕ (b ⊕ c)

  This generalises to arbitrary binary trees: any two bracketings
  of the same sequence under an associative operation are equal.
  When ⊕ is additionally commutative (AC), argument *order* is also
  irrelevant — the AC-completion procedure generates all valid forms.

  Concretely:
    fold(⊕, e, tree_split(xs))  ≡  fold(⊕, e, xs)
    foldl(⊕, e, xs)  ≡  foldr(⊕, e, xs)       (when ⊕ is associative)
    merge_sort-style divide-and-conquer  ≡  linear scan

Covers:
  • Tree-fold → linear fold (flatten tree_split / divide / bisect)
  • Left-fold ↔ right-fold for associative ops
  • AC-completion: all parenthesisations of AC expressions
  • AC-canonical form (left-associated, sorted arguments)
  • Implicit tree-split detection (slice-based D&C)
  • Merge-sort style D&C → fold (when op is associative)
  • reduce() ↔ fold equivalence
"""
from __future__ import annotations

import hashlib
from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Sequence, Set, Tuple, Union

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)


# ═══════════════════════════════════════════════════════════
# Axiom metadata
# ═══════════════════════════════════════════════════════════

AXIOM_NAME = 'D17_assoc'
AXIOM_CATEGORY = 'algorithm_strategy'  # §22

SOUNDNESS_PROOF = """
Theorem 22.3.1 (Associativity-Mediated Equivalence):
  Let (M, ⊕) be a semigroup.  For any sequence xs = [x₁,...,xₙ]:
    foldl(⊕, e, xs)  =  foldr(⊕, e, xs)  =  tree_fold(⊕, e, xs)
  where tree_fold applies ⊕ in a balanced binary tree over xs.

Proof:
  By the generalised associativity theorem (Mac Lane's coherence),
  any two well-typed parenthesisations of x₁ ⊕ x₂ ⊕ ... ⊕ xₙ
  are equal.  Each fold strategy corresponds to a different
  parenthesisation.  ∎

AC-Completion (Theorem 22.3.2):
  When ⊕ is additionally commutative, the canonical form is
  unique up to left-association with sorted arguments:
    canon(⊕, {a,b,c}) = (a ⊕ b) ⊕ c  where a ≤ b ≤ c lexically.
"""

COMPOSES_WITH = ['D15_traversal', 'D16_memo_dp', 'FOLD_extended', 'D19_sort']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'Tree fold → linear fold',
        'before': "fold[add](0, tree_split(xs))",
        'after': "fold[add](0, xs)",
        'axiom': 'D17_tree_to_linear_fold',
    },
    {
        'name': 'Left-fold → right-fold',
        'before': "foldl[add](0, xs)",
        'after': "foldr[add](0, xs)",
        'axiom': 'D17_left_to_right_fold',
    },
    {
        'name': 'AC canonical form',
        'before': "add(c, add(a, b))",
        'after': "add(add(a, b), c)",
        'axiom': 'D17_ac_canonicalize',
    },
    {
        'name': 'Merge-sort D&C → fold',
        'before': "fix[merge_add](case(len≤1, xs, merge(f(left), f(right))))",
        'after': "fold[add](0, xs)",
        'axiom': 'D17_mergesort_to_fold',
    },
    {
        'name': 'reduce → fold',
        'before': "reduce(add, xs, 0)",
        'after': "fold[add](0, xs)",
        'axiom': 'D17_reduce_to_fold',
    },
]

# ── Operation classification ──
# bitor/bitand/bitxor are commutative/associative on integers
# but NOT on dicts (| is merge, which is not commutative)
_ALWAYS_COMMUTATIVE: FrozenSet[str] = frozenset({
    'mul', '.mul', 'imul', 'mult',
    'and', 'or',
    'min', 'max', 'eq', 'noteq',
    'union', 'intersection', '.count',
    'gcd', 'lcm',
})
_FIBER_COMMUTATIVE: FrozenSet[str] = frozenset({
    'add', '.add', 'iadd',
    'bitor', 'bitand', 'bitxor',
})
COMMUTATIVE_OPS: FrozenSet[str] = _ALWAYS_COMMUTATIVE | _FIBER_COMMUTATIVE

_ALWAYS_ASSOCIATIVE: FrozenSet[str] = frozenset({
    'mul', '.mul', 'imul', 'mult',
    'and', 'or',
    'min', 'max', 'concat',
    'union', 'intersection',
    'gcd', 'lcm',
})
_FIBER_ASSOCIATIVE: FrozenSet[str] = frozenset({
    'add', '.add', 'iadd',
    'bitor', 'bitand', 'bitxor',
})
ASSOCIATIVE_OPS: FrozenSet[str] = _ALWAYS_ASSOCIATIVE | _FIBER_ASSOCIATIVE

IDENTITY_ELEMENTS: Dict[str, Any] = {
    'add': 0, '.add': 0, 'iadd': 0,
    'mul': 1, '.mul': 1, 'imul': 1, 'mult': 1,
    'and': True, 'or': False,
    'bitor': 0, 'bitand': -1, 'bitxor': 0,
    'min': float('inf'), 'max': float('-inf'),
    'concat': '', 'union': frozenset(),
    'gcd': 0, 'lcm': 1,
}


# ═══════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════

@dataclass
class FiberCtx:
    """Lightweight fiber context for standalone axiom evaluation."""
    param_duck_types: Dict[str, str] = field(default_factory=dict)


def _is_commutative(op_name: str, ctx=None) -> bool:
    if op_name in _ALWAYS_COMMUTATIVE:
        return True
    if op_name in _FIBER_COMMUTATIVE:
        # Only commutative on integer fibers
        if ctx is not None and hasattr(ctx, 'is_integer'):
            # Without concrete term info, check general param types
            for dt in ctx.param_duck_types.values():
                if dt not in ('int',):
                    return False
            return True
        return False  # Unknown fiber → conservative
    return False


def _is_associative(op_name: str, ctx=None) -> bool:
    if op_name in _ALWAYS_ASSOCIATIVE:
        return True
    if op_name in _FIBER_ASSOCIATIVE:
        if ctx is not None and hasattr(ctx, 'is_integer'):
            for dt in ctx.param_duck_types.values():
                if dt not in ('int',):
                    return False
            return True
        return False
    return False


def _body_has_slice_split(body: OTerm) -> bool:
    """Check whether the body contains a mid-point slice pattern."""
    canon = body.canon()
    return ('slice' in canon and ('floordiv' in canon or 'rshift' in canon))


# ═══════════════════════════════════════════════════════════
# AC-completion and canonical forms
# ═══════════════════════════════════════════════════════════

def collect_ac_leaves(op_name: str, term: OTerm) -> List[OTerm]:
    """Collect leaves of a nested AC operator tree.

    add(add(a, b), c) → [a, b, c]
    """
    if isinstance(term, OOp) and term.name == op_name:
        result: List[OTerm] = []
        for a in term.args:
            result.extend(collect_ac_leaves(op_name, a))
        return result
    return [term]


def ac_canonical_form(op_name: str, term: OTerm) -> OTerm:
    """Flatten an AC expression to left-associated, sorted canonical form.

    add(c, add(a, b)) → add(add(a, b), c)  (after sorting: a < b < c)
    """
    leaves = collect_ac_leaves(op_name, term)
    if len(leaves) <= 1:
        return term
    sorted_leaves = sorted(leaves, key=lambda t: t.canon())
    result = sorted_leaves[0]
    for leaf in sorted_leaves[1:]:
        result = OOp(op_name, (result, leaf))
    return result


def ac_completion(
    op_name: str,
    terms: Sequence[OTerm],
) -> List[OTerm]:
    """AC-unification: generate all distinct parenthesisations.

    For AC ops, the bag is first sorted by canon() (commutativity
    normalisation).  Then associativity produces all binary trees.
    """
    if not _is_associative(op_name) or not _is_commutative(op_name):
        return []

    sorted_terms = sorted(terms, key=lambda t: t.canon())

    def _all_trees(elems: List[OTerm]) -> List[OTerm]:
        if len(elems) == 1:
            return [elems[0]]
        results: List[OTerm] = []
        for i in range(1, len(elems)):
            for lt in _all_trees(elems[:i]):
                for rt in _all_trees(elems[i:]):
                    results.append(OOp(op_name, (lt, rt)))
        return results

    return _all_trees(sorted_terms)


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D17 associativity-mediated equivalences to *term*."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── Tree fold → linear fold ──
    if isinstance(term, OFold):
        flat = _try_flatten_tree_fold(term)
        if flat is not None:
            results.append((flat, 'D17_tree_to_linear_fold'))

    # ── Left-fold ↔ right-fold ──
    if isinstance(term, OOp) and term.name == 'foldl' and len(term.args) == 3:
        op, init, coll = term.args
        if isinstance(op, OVar) and _is_associative(op.name, ctx):
            results.append((
                OOp('foldr', (op, init, coll)),
                'D17_left_to_right_fold',
            ))
    if isinstance(term, OOp) and term.name == 'foldr' and len(term.args) == 3:
        op, init, coll = term.args
        if isinstance(op, OVar) and _is_associative(op.name, ctx):
            results.append((
                OOp('foldl', (op, init, coll)),
                'D17_right_to_left_fold',
            ))

    # ── AC-canonical form for nested binary ops ──
    if isinstance(term, OOp) and _is_associative(term.name, ctx) and _is_commutative(term.name, ctx):
        leaves = collect_ac_leaves(term.name, term)
        if len(leaves) >= 3:
            canon = ac_canonical_form(term.name, term)
            if canon.canon() != term.canon():
                results.append((canon, 'D17_ac_canonicalize'))

    # ── Re-association: (a ⊕ b) ⊕ c → a ⊕ (b ⊕ c) ──
    if isinstance(term, OOp) and _is_associative(term.name, ctx) and len(term.args) == 2:
        lhs, rhs = term.args
        # Left-associated → right-associated
        if isinstance(lhs, OOp) and lhs.name == term.name and len(lhs.args) == 2:
            a, b = lhs.args
            results.append((
                OOp(term.name, (a, OOp(term.name, (b, rhs)))),
                'D17_reassoc_left_to_right',
            ))
        # Right-associated → left-associated
        if isinstance(rhs, OOp) and rhs.name == term.name and len(rhs.args) == 2:
            b, c = rhs.args
            results.append((
                OOp(term.name, (OOp(term.name, (lhs, b)), c)),
                'D17_reassoc_right_to_left',
            ))

    # ── Merge-sort D&C → fold (when op is associative) ──
    if isinstance(term, OFix):
        if _body_has_slice_split(term.body):
            op_name = term.name
            if _is_associative(op_name, ctx):
                identity = IDENTITY_ELEMENTS.get(op_name, OLit(0))
                if not isinstance(identity, OTerm):
                    identity = OLit(identity)
                results.append((
                    OFold(op_name, identity, OVar('_input')),
                    'D17_mergesort_to_fold',
                ))

    # ── reduce(op, xs, init) → fold[op](init, xs) ──
    if isinstance(term, OOp) and term.name in ('reduce', 'functools.reduce'):
        if len(term.args) >= 2:
            op_term = term.args[0]
            coll = term.args[1]
            init = term.args[2] if len(term.args) >= 3 else OLit(None)
            op_str = op_term.name if isinstance(op_term, OVar) else op_term.canon()
            results.append((
                OFold(op_str, init, coll),
                'D17_reduce_to_fold',
            ))

    # ── fold[op](init, xs) → reduce(op, xs, init) (reverse) ──
    if isinstance(term, OFold):
        results.append((
            OOp('reduce', (OVar(term.op_name), term.collection, term.init)),
            'D17_fold_to_reduce',
        ))

    # ── Identity elimination: op(x, identity) → x ──
    if isinstance(term, OOp) and _is_associative(term.name, ctx) and len(term.args) == 2:
        identity = IDENTITY_ELEMENTS.get(term.name)
        if identity is not None:
            for i in range(2):
                arg = term.args[i]
                other = term.args[1 - i]
                if isinstance(arg, OLit) and arg.value == identity:
                    results.append((other, 'D17_identity_elim'))
                    break

    # ── Fold over singleton: fold[op](init, [x]) → op(init, x) ──
    if isinstance(term, OFold):
        if isinstance(term.collection, OSeq) and len(term.collection.elements) == 1:
            elem = term.collection.elements[0]
            results.append((
                OOp(term.op_name, (term.init, elem)),
                'D17_fold_singleton',
            ))

    return results


def _try_flatten_tree_fold(term: OFold) -> Optional[OFold]:
    """Flatten tree-structured folds, including implicit splits."""
    if isinstance(term.collection, OOp):
        # Explicit tree_split / divide / bisect_split
        if term.collection.name in ('tree_split', 'divide', 'bisect_split'):
            if _is_associative(term.op_name):
                if len(term.collection.args) >= 1:
                    return OFold(term.op_name, term.init, term.collection.args[0])

        # Implicit split via slicing
        if term.collection.name == 'getitem' and len(term.collection.args) == 2:
            inner = term.collection.args[1]
            if isinstance(inner, OOp) and inner.name == 'slice':
                if _is_associative(term.op_name):
                    return OFold(term.op_name, term.init, term.collection.args[0])

    return None


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D17 in reverse: linear → tree, etc."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # fold[op](init, xs) → fold[op](init, tree_split(xs))
    if isinstance(term, OFold) and _is_associative(term.op_name):
        coll = term.collection
        if not (isinstance(coll, OOp) and coll.name in (
            'tree_split', 'divide', 'bisect_split',
        )):
            results.append((
                OFold(term.op_name, term.init,
                      OOp('tree_split', (coll,))),
                'D17_inv_linear_to_tree',
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D17 is potentially applicable."""
    if isinstance(term, OFold):
        if isinstance(term.collection, OOp) and term.collection.name in (
            'tree_split', 'divide', 'bisect_split',
        ):
            return True
        # Any fold with associative op → re-association possible
        if _is_associative(term.op_name):
            return True
    if isinstance(term, OOp):
        if term.name in ('foldl', 'foldr', 'reduce', 'functools.reduce'):
            return True
        if _is_associative(term.name) and len(term.args) >= 2:
            # Nested associative ops → AC-normalisation possible
            for arg in term.args:
                if isinstance(arg, OOp) and arg.name == term.name:
                    return True
    if isinstance(term, OFix):
        if _body_has_slice_split(term.body):
            return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D17 relevance for bridging *source* → *target*."""
    sc = source.canon()
    tc = target.canon()

    has_fold_s = 'fold[' in sc
    has_fold_t = 'fold[' in tc
    has_tree_s = 'tree_split' in sc or 'divide(' in sc
    has_tree_t = 'tree_split' in tc or 'divide(' in tc
    has_reduce = 'reduce(' in sc or 'reduce(' in tc

    # Tree vs flat
    if has_tree_s != has_tree_t:
        return 0.90
    # Both folds — possible re-association
    if has_fold_s and has_fold_t:
        return 0.70
    # reduce involved
    if has_reduce:
        return 0.65
    # Nested ops suggest re-association
    depth_s = sc.count('(')
    depth_t = tc.count('(')
    if abs(depth_s - depth_t) >= 3:
        return 0.50
    return 0.10


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
    a, b, c = OVar('a'), OVar('b'), OVar('c')

    # ── Tree fold → linear fold ──
    print("D17: tree fold → linear ...")
    tree_fold = OFold('add', OLit(0), OOp('tree_split', (xs,)))
    r = apply(tree_fold, ctx)
    _assert(any(lbl == 'D17_tree_to_linear_fold' for _, lbl in r), "tree→linear")
    if r:
        flat = [t for t, lbl in r if lbl == 'D17_tree_to_linear_fold'][0]
        _assert(isinstance(flat, OFold), "result is OFold")
        _assert(flat.collection.canon() == xs.canon(), "collection is xs")

    # ── Re-association ──
    print("D17: re-association ...")
    left_assoc = OOp('add', (OOp('add', (a, b)), c))
    r2 = apply(left_assoc, ctx)
    _assert(any(lbl == 'D17_reassoc_left_to_right' for _, lbl in r2),
            "left→right assoc")

    right_assoc = OOp('add', (a, OOp('add', (b, c))))
    r3 = apply(right_assoc, ctx)
    _assert(any(lbl == 'D17_reassoc_right_to_left' for _, lbl in r3),
            "right→left assoc")

    # ── AC canonical form ──
    print("D17: AC canonical form ...")
    ac_expr = OOp('add', (c, OOp('add', (a, b))))
    r4 = apply(ac_expr, ctx)
    _assert(any(lbl == 'D17_ac_canonicalize' for _, lbl in r4), "AC canonicalize")

    # ── AC completion ──
    print("D17: AC completion ...")
    forms = ac_completion('add', [a, b, c])
    _assert(len(forms) >= 2, f"AC completion produces {len(forms)} forms (≥2)")

    # ── collect_ac_leaves ──
    print("D17: collect_ac_leaves ...")
    leaves = collect_ac_leaves('add', OOp('add', (a, OOp('add', (b, c)))))
    _assert(len(leaves) == 3, f"3 leaves found: {len(leaves)}")

    # ── reduce → fold ──
    print("D17: reduce → fold ...")
    reduce_term = OOp('reduce', (OVar('add'), xs, OLit(0)))
    r5 = apply(reduce_term, ctx)
    _assert(any(lbl == 'D17_reduce_to_fold' for _, lbl in r5), "reduce→fold")

    # ── fold → reduce ──
    print("D17: fold → reduce ...")
    fold_term = OFold('add', OLit(0), xs)
    r6 = apply(fold_term, ctx)
    _assert(any(lbl == 'D17_fold_to_reduce' for _, lbl in r6), "fold→reduce")

    # ── Identity elimination ──
    print("D17: identity elimination ...")
    add_zero = OOp('add', (OVar('x'), OLit(0)))
    r7 = apply(add_zero, ctx)
    _assert(any(lbl == 'D17_identity_elim' for _, lbl in r7), "identity elim")

    mul_one = OOp('mul', (OLit(1), OVar('y')))
    r8 = apply(mul_one, ctx)
    _assert(any(lbl == 'D17_identity_elim' for _, lbl in r8), "mul identity")

    # ── Fold singleton ──
    print("D17: fold singleton ...")
    fold_single = OFold('add', OLit(0), OSeq((OVar('x'),)))
    r9 = apply(fold_single, ctx)
    _assert(any(lbl == 'D17_fold_singleton' for _, lbl in r9), "fold singleton")

    # ── recognizes ──
    print("D17: recognizes ...")
    _assert(recognizes(tree_fold), "recognizes tree fold")
    _assert(recognizes(left_assoc), "recognizes nested assoc")
    _assert(recognizes(reduce_term), "recognizes reduce")
    _assert(not recognizes(OOp('Counter', (xs,))), "does not recognise Counter")

    # ── relevance_score ──
    print("D17: relevance_score ...")
    score = relevance_score(tree_fold, fold_term)
    _assert(score > 0.8, f"tree↔flat score={score:.2f} > 0.8")

    # ── apply_inverse ──
    print("D17: apply_inverse ...")
    inv = apply_inverse(fold_term, ctx)
    _assert(len(inv) >= 1, "inverse linear→tree")

    # ── Non-associative ops should NOT trigger re-assoc ──
    print("D17: non-associative guard ...")
    non_assoc = OOp('sub', (OOp('sub', (a, b)), c))
    r10 = apply(non_assoc, ctx)
    _assert(not any('reassoc' in lbl for _, lbl in r10),
            "sub is not associative — no re-association")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  D17 assoc: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
