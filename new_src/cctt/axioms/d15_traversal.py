"""D15: Traversal Equivalences (Theorem 22.1.1).

Different iteration patterns over the same collection produce the same
result when the accumulation is order-invariant.

Mathematical foundation:
  When the fold monoid (M, ⊕, e) is commutative, the traversal order
  of the underlying collection is irrelevant:
    fold(⊕, e, BFS(G))  ≡  fold(⊕, e, DFS(G))
  because commutativity makes the fold a morphism from Free(X)/~_comm
  into M — the quotient by permutation kills ordering.

  More generally, any two traversals τ₁, τ₂ : Tree → List that visit
  every node exactly once satisfy  fold(⊕, e, τ₁(T)) = fold(⊕, e, τ₂(T))
  when ⊕ is commutative and associative (i.e. the fold lifts through
  the permutation quotient).

Covers:
  • BFS ↔ DFS when fold is commutative
  • Inorder ↔ preorder ↔ postorder when fold is commutative
  • Forward ↔ reverse iteration under commutative fold
  • for-each ↔ iterator ↔ while-based iteration
  • Parallel / chunked iteration equivalence
"""
from __future__ import annotations

import hashlib
from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple, Union

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)


# ═══════════════════════════════════════════════════════════
# Axiom metadata
# ═══════════════════════════════════════════════════════════

AXIOM_NAME = 'D15_traversal'
AXIOM_CATEGORY = 'algorithm_strategy'  # §22

SOUNDNESS_PROOF = """
Theorem 22.1.1 (Traversal Equivalence):
  Let (M, ⊕, e) be a commutative monoid and T a finite tree (or graph).
  For any two complete traversals τ₁, τ₂ of T:
    fold(⊕, e, τ₁(T))  =  fold(⊕, e, τ₂(T))

Proof:
  Both τ₁(T) and τ₂(T) are permutations of the same multiset of nodes.
  Since ⊕ is commutative and associative, fold is invariant under
  permutation of the input sequence.  ∎

Corollary: fold(⊕, e, BFS(G)) = fold(⊕, e, DFS(G)) for commutative ⊕.
Corollary: fold(⊕, e, reversed(xs)) = fold(⊕, e, xs) for commutative ⊕.
"""

COMPOSES_WITH = ['D17_assoc', 'D14_indexing', 'D19_sort']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'BFS to DFS under commutative fold',
        'before': "fold[add](0, BFS(graph))",
        'after': "fold[add](0, DFS(graph))",
        'axiom': 'D15_bfs_to_dfs',
    },
    {
        'name': 'DFS to BFS under commutative fold',
        'before': "fold[add](0, DFS(graph))",
        'after': "fold[add](0, BFS(graph))",
        'axiom': 'D15_dfs_to_bfs',
    },
    {
        'name': 'reversed iteration under commutative fold',
        'before': "fold[add](0, reversed(xs))",
        'after': "fold[add](0, xs)",
        'axiom': 'D15_reversed_fold',
    },
    {
        'name': 'inorder to preorder under commutative fold',
        'before': "fold[add](0, inorder(tree))",
        'after': "fold[add](0, preorder(tree))",
        'axiom': 'D15_inorder_to_preorder',
    },
    {
        'name': 'iter to list under fold',
        'before': "fold[add](0, iter(xs))",
        'after': "fold[add](0, xs)",
        'axiom': 'D15_iter_strip',
    },
]

COMMUTATIVE_OPS: FrozenSet[str] = frozenset({
    'add', '.add', 'iadd', 'mul', '.mul', 'imul', 'mult',
    'and', 'or', 'bitor', 'bitand', 'bitxor',
    'min', 'max', 'eq', 'noteq',
    'union', 'intersection', '.count',
    'gcd', 'lcm',
})

ASSOCIATIVE_OPS: FrozenSet[str] = frozenset({
    'add', '.add', 'iadd', 'mul', '.mul', 'imul', 'mult',
    'and', 'or', 'bitor', 'bitand', 'bitxor',
    'min', 'max', 'concat',
    'union', 'intersection',
    'gcd', 'lcm',
})

# Traversal operations that produce an ordering of nodes
_TRAVERSAL_OPS = frozenset({
    'BFS', 'DFS', 'bfs', 'dfs',
    'inorder', 'preorder', 'postorder',
    'levelorder', 'reversed', 'iter', 'values',
})

# Pairs of traversals that are permutations of each other
_TRAVERSAL_PAIRS: List[Tuple[str, str]] = [
    ('BFS', 'DFS'), ('bfs', 'dfs'),
    ('DFS', 'BFS'), ('dfs', 'bfs'),
    ('inorder', 'preorder'), ('preorder', 'postorder'),
    ('postorder', 'inorder'), ('inorder', 'postorder'),
    ('preorder', 'inorder'), ('postorder', 'preorder'),
]


# ═══════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════

@dataclass
class FiberCtx:
    """Lightweight fiber context for standalone axiom evaluation."""
    param_duck_types: Dict[str, str] = field(default_factory=dict)


def _is_commutative(op_name: str) -> bool:
    return op_name in COMMUTATIVE_OPS


def _is_associative(op_name: str) -> bool:
    return op_name in ASSOCIATIVE_OPS


def _is_traversal_op(name: str) -> bool:
    return name in _TRAVERSAL_OPS


def _get_traversal_source(term: OTerm) -> Optional[Tuple[str, OTerm]]:
    """If term is a traversal(source), return (traversal_name, source)."""
    if isinstance(term, OOp) and term.name in _TRAVERSAL_OPS:
        if len(term.args) == 1:
            return (term.name, term.args[0])
    return None


def _traversal_partner(name: str) -> Optional[str]:
    """Return a canonical partner traversal for swapping."""
    for a, b in _TRAVERSAL_PAIRS:
        if a == name:
            return b
    return None


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D15 traversal equivalences to *term*."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── fold over traversal → fold over partner traversal (commutative) ──
    if isinstance(term, OFold) and _is_commutative(term.op_name):
        trav = _get_traversal_source(term.collection)
        if trav is not None:
            trav_name, source = trav

            # BFS ↔ DFS
            partner = _traversal_partner(trav_name)
            if partner is not None:
                results.append((
                    OFold(term.op_name, term.init,
                          OOp(partner, (source,))),
                    f'D15_{trav_name.lower()}_to_{partner.lower()}',
                ))

            # Strip traversal entirely (fold directly over source)
            if trav_name in ('iter', 'values'):
                results.append((
                    OFold(term.op_name, term.init, source),
                    'D15_iter_strip',
                ))

    # ── fold over reversed(xs) → fold over xs (commutative) ──
    if isinstance(term, OFold) and _is_commutative(term.op_name):
        if (isinstance(term.collection, OOp)
                and term.collection.name == 'reversed'
                and len(term.collection.args) == 1):
            results.append((
                OFold(term.op_name, term.init, term.collection.args[0]),
                'D15_reversed_fold',
            ))

    # ── fold over reversed(xs) → fold over xs (also when assoc+comm) ──
    # already covered above

    # ── map over traversal → map over partner (commutative result) ──
    if isinstance(term, OMap):
        trav = _get_traversal_source(term.collection)
        if trav is not None:
            trav_name, source = trav
            partner = _traversal_partner(trav_name)
            if partner is not None:
                results.append((
                    OMap(term.transform,
                         OOp(partner, (source,)),
                         term.filter_pred),
                    f'D15_map_{trav_name.lower()}_to_{partner.lower()}',
                ))

    # ── Quotient traversal: Q[perm](traversal(x)) → Q[perm](x) ──
    if isinstance(term, OQuotient) and term.equiv_class == 'perm':
        trav = _get_traversal_source(term.inner)
        if trav is not None:
            _, source = trav
            results.append((
                OQuotient(source, 'perm'),
                'D15_quotient_traversal_absorb',
            ))

    # ── fold[op](init, iter(xs)) → fold[op](init, xs) ──
    if isinstance(term, OFold):
        if (isinstance(term.collection, OOp)
                and term.collection.name == 'iter'
                and len(term.collection.args) == 1):
            results.append((
                OFold(term.op_name, term.init, term.collection.args[0]),
                'D15_iter_strip',
            ))

    # ── fold[op](init, list(xs)) → fold[op](init, xs) ──
    if isinstance(term, OFold):
        if (isinstance(term.collection, OOp)
                and term.collection.name == 'list'
                and len(term.collection.args) == 1):
            results.append((
                OFold(term.op_name, term.init, term.collection.args[0]),
                'D15_list_strip',
            ))

    # ── Chunk equivalence: fold(op, chunk(xs, k)) ≡ fold(op, xs) when assoc ──
    if isinstance(term, OFold) and _is_associative(term.op_name):
        if (isinstance(term.collection, OOp)
                and term.collection.name in ('chunk', 'batched', 'partition_chunks')
                and len(term.collection.args) >= 1):
            results.append((
                OFold(term.op_name, term.init, term.collection.args[0]),
                'D15_chunk_fold_flatten',
            ))

    # ── deque-based iteration → list iteration ──
    if isinstance(term, OFold):
        if (isinstance(term.collection, OOp)
                and term.collection.name == 'deque'
                and len(term.collection.args) == 1):
            results.append((
                OFold(term.op_name, term.init, term.collection.args[0]),
                'D15_deque_to_list',
            ))

    # ── Sorted traversal equivalence (special case: sort is a traversal) ──
    # fold(comm_op, sorted(xs)) = fold(comm_op, xs)
    # This overlaps with D19 but we include it for completeness
    if isinstance(term, OFold) and _is_commutative(term.op_name):
        if (isinstance(term.collection, OOp)
                and term.collection.name == 'sorted'
                and len(term.collection.args) >= 1):
            results.append((
                OFold(term.op_name, term.init, term.collection.args[0]),
                'D15_sorted_commutative_fold',
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D15 in reverse: introduce traversal wrappers."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # fold(op, xs) → fold(op, reversed(xs)) when commutative
    if isinstance(term, OFold) and _is_commutative(term.op_name):
        coll = term.collection
        # Only apply if not already a traversal wrapper
        if not (isinstance(coll, OOp) and coll.name in _TRAVERSAL_OPS | {'reversed', 'sorted'}):
            results.append((
                OFold(term.op_name, term.init,
                      OOp('reversed', (coll,))),
                'D15_inv_introduce_reversed',
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D15 is potentially applicable."""
    if isinstance(term, OFold):
        coll = term.collection
        if isinstance(coll, OOp) and coll.name in (
            _TRAVERSAL_OPS | {'reversed', 'sorted', 'list', 'iter',
                              'deque', 'chunk', 'batched', 'partition_chunks'}
        ):
            return True
    if isinstance(term, OMap):
        coll = term.collection
        if isinstance(coll, OOp) and coll.name in _TRAVERSAL_OPS:
            return True
    if isinstance(term, OQuotient) and term.equiv_class == 'perm':
        if isinstance(term.inner, OOp) and term.inner.name in _TRAVERSAL_OPS:
            return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D15 relevance for bridging *source* → *target*."""
    sc = source.canon()
    tc = target.canon()

    traversal_keywords = ['BFS', 'DFS', 'bfs', 'dfs', 'inorder',
                          'preorder', 'postorder', 'reversed(', 'iter(']

    has_trav_s = any(kw in sc for kw in traversal_keywords)
    has_trav_t = any(kw in tc for kw in traversal_keywords)

    if has_trav_s and has_trav_t:
        # Both have traversals but possibly different ones
        return 0.90
    if has_trav_s != has_trav_t:
        return 0.80
    if 'reversed(' in sc or 'reversed(' in tc:
        return 0.70
    if 'fold[' in sc and 'fold[' in tc:
        return 0.30
    return 0.05


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
    graph = OVar('graph')
    tree = OVar('tree')

    # ── BFS → DFS under commutative fold ──
    print("D15: BFS → DFS ...")
    bfs_fold = OFold('add', OLit(0), OOp('BFS', (graph,)))
    r = apply(bfs_fold, ctx)
    _assert(any(lbl == 'D15_bfs_to_dfs' for _, lbl in r), "BFS→DFS")

    # ── DFS → BFS ──
    print("D15: DFS → BFS ...")
    dfs_fold = OFold('add', OLit(0), OOp('DFS', (graph,)))
    r2 = apply(dfs_fold, ctx)
    _assert(any(lbl == 'D15_dfs_to_bfs' for _, lbl in r2), "DFS→BFS")

    # ── Roundtrip BFS↔DFS ──
    print("D15: roundtrip ...")
    fwd = [t for t, lbl in r if lbl == 'D15_bfs_to_dfs']
    _assert(len(fwd) >= 1, "forward BFS→DFS produces result")
    bwd = apply(fwd[0], ctx)
    _assert(any('bfs' in lbl for _, lbl in bwd), "roundtrip DFS→BFS")

    # ── reversed fold ──
    print("D15: reversed fold ...")
    rev_fold = OFold('add', OLit(0), OOp('reversed', (xs,)))
    r3 = apply(rev_fold, ctx)
    _assert(any(lbl == 'D15_reversed_fold' for _, lbl in r3), "reversed fold")

    # ── Non-commutative fold should NOT strip reversed ──
    print("D15: non-commutative guard ...")
    nc_fold = OFold('concat', OLit(''), OOp('reversed', (xs,)))
    r4 = apply(nc_fold, ctx)
    _assert(not any(lbl == 'D15_reversed_fold' for _, lbl in r4),
            "concat is not commutative — should not strip reversed")

    # ── inorder → preorder ──
    print("D15: inorder → preorder ...")
    in_fold = OFold('add', OLit(0), OOp('inorder', (tree,)))
    r5 = apply(in_fold, ctx)
    _assert(any('preorder' in lbl for _, lbl in r5), "inorder→preorder")

    # ── iter strip ──
    print("D15: iter strip ...")
    iter_fold = OFold('add', OLit(0), OOp('iter', (xs,)))
    r6 = apply(iter_fold, ctx)
    _assert(any(lbl == 'D15_iter_strip' for _, lbl in r6), "iter strip")

    # ── list strip ──
    print("D15: list strip ...")
    list_fold = OFold('add', OLit(0), OOp('list', (xs,)))
    r7 = apply(list_fold, ctx)
    _assert(any(lbl == 'D15_list_strip' for _, lbl in r7), "list strip")

    # ── chunk fold ──
    print("D15: chunk fold ...")
    chunk_fold = OFold('add', OLit(0), OOp('chunk', (xs, OLit(10))))
    r8 = apply(chunk_fold, ctx)
    _assert(any(lbl == 'D15_chunk_fold_flatten' for _, lbl in r8), "chunk fold")

    # ── Quotient traversal absorb ──
    print("D15: quotient traversal ...")
    q_trav = OQuotient(OOp('BFS', (graph,)), 'perm')
    r9 = apply(q_trav, ctx)
    _assert(any(lbl == 'D15_quotient_traversal_absorb' for _, lbl in r9),
            "quotient traversal absorb")

    # ── map over traversal ──
    print("D15: map over traversal ...")
    map_bfs = OMap(OLam(('x',), OOp('f', (OVar('x'),))),
                   OOp('BFS', (graph,)))
    r10 = apply(map_bfs, ctx)
    _assert(any('dfs' in lbl.lower() for _, lbl in r10), "map BFS→DFS")

    # ── recognizes ──
    print("D15: recognizes ...")
    _assert(recognizes(bfs_fold), "recognizes BFS fold")
    _assert(recognizes(rev_fold), "recognizes reversed fold")
    _assert(recognizes(iter_fold), "recognizes iter fold")
    _assert(not recognizes(OOp('sorted', (xs,))), "does not recognise bare sorted")

    # ── relevance_score ──
    print("D15: relevance_score ...")
    score = relevance_score(bfs_fold, dfs_fold)
    _assert(score > 0.8, f"BFS↔DFS score={score:.2f} > 0.8")

    # ── apply_inverse ──
    print("D15: apply_inverse ...")
    plain = OFold('add', OLit(0), xs)
    inv = apply_inverse(plain, ctx)
    _assert(len(inv) >= 1, "inverse introduces reversed")

    # ── sorted commutative fold ──
    print("D15: sorted commutative fold ...")
    sorted_fold = OFold('add', OLit(0), OOp('sorted', (xs,)))
    r11 = apply(sorted_fold, ctx)
    _assert(any(lbl == 'D15_sorted_commutative_fold' for _, lbl in r11),
            "sorted commutative fold")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  D15 traversal: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
