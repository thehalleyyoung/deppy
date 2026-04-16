"""Fold Rewrite Axioms — Fold Fusion, Fold-Map Interaction, Canonicalisation.

Fold-specific rewrites that operate on OFold terms and their interactions
with other combinators (map, filter, range).

Key rewrites:
  • fold[add](0, x) ↔ sum(x)
  • fold[mul](1, x) ↔ prod(x)
  • fold[and](True, x) ↔ all(x)
  • fold[or](False, x) ↔ any(x)
  • fold[max](-inf, x) ↔ max(x)
  • fold[min](inf, x) ↔ min(x)
  • fold[append]([], x) ↔ list(x)
  • fold[union]({}, x) ↔ set(x)
  • fold[count](0, x) ↔ len(x)
  • fold over range(0, n) → fold over range(n)
  • fold fusion: fold(f, map(g, x)) → fold(f∘g, x)
  • fold-map interaction: map(f, fold(g, x)) normalisation
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "FOLD_fold"
AXIOM_CATEGORY = "utility"

SOUNDNESS_PROOF = """
Fold identities:
  fold[⊕](e, xs) = xs[0] ⊕ xs[1] ⊕ ... ⊕ xs[n-1]
  where e is the identity element of ⊕.

When ⊕ = +, e = 0: fold[+](0, xs) = sum(xs).
When ⊕ = *, e = 1: fold[*](1, xs) = prod(xs).

Fold fusion (banana-split theorem):
  fold(f, map(g, xs)) = fold(f ∘ g, xs)
  when f distributes over the map combinator.

Range normalisation:
  range(0, n) = range(n) by Python semantics.
"""

COMPOSES_WITH = ["ALG", "D19_sort_scan", "D20_spec", "QUOT"]
REQUIRES: List[str] = []

EXAMPLES = [
    ("fold[add](0, xs)", "sum(xs)", "FOLD_sum"),
    ("fold[mul](1, xs)", "prod(xs)", "FOLD_prod"),
    ("fold[and](True, xs)", "all(xs)", "FOLD_and_to_all"),
    ("fold[append]([], xs)", "list(xs)", "FOLD_append_to_list"),
    ("fold[add](0, range(0, n))", "fold[add](0, range(n))", "FOLD_range_normalize"),
]

# ── Fold identity map ────────────────────────────────────────

FOLD_IDENTITIES: Dict[str, Tuple[Any, str, str]] = {
    # op_name: (init_value, collapsed_name, axiom_label)
    'add': (0, 'sum', 'FOLD_sum'),
    '.add': (0, 'sum', 'FOLD_sum'),
    'iadd': (0, 'sum', 'FOLD_sum'),
    'mul': (1, 'prod', 'FOLD_prod'),
    '.mul': (1, 'prod', 'FOLD_prod'),
    'imul': (1, 'prod', 'FOLD_prod'),
    'mult': (1, 'prod', 'FOLD_prod'),
    'and': (True, 'all', 'FOLD_and_to_all'),
    'or': (False, 'any', 'FOLD_or_to_any'),
    '.count': (0, 'len', 'FOLD_len'),
    'count': (0, 'len', 'FOLD_len'),
}


@dataclass
class FiberCtx:
    param_duck_types: Dict[str, str] = field(default_factory=dict)

    def is_numeric(self, term: OTerm) -> bool:
        return True


def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply fold-specific rewrite rules."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    if isinstance(term, OFold):
        # ── 1. Range normalisation: range(0, n) → range(n) ──
        if isinstance(term.collection, OOp) and term.collection.name == 'range':
            if (len(term.collection.args) == 2
                    and isinstance(term.collection.args[0], OLit)
                    and term.collection.args[0].value == 0):
                results.append((
                    OFold(term.op_name, term.init,
                          OOp('range', (term.collection.args[1],))),
                    'FOLD_range_normalize',
                ))

        # ── 2. Fold identity collapse: fold[add](0, x) → sum(x) ──
        if term.op_name in FOLD_IDENTITIES:
            expected_init, collapsed_name, label = FOLD_IDENTITIES[term.op_name]
            if isinstance(term.init, OLit) and term.init.value == expected_init:
                results.append((
                    OOp(collapsed_name, (term.collection,)),
                    label,
                ))

        # ── 3. fold[max](-inf, x) → max(x) ──
        if term.op_name in ('max', '.max'):
            if isinstance(term.init, OLit) and term.init.value == float('-inf'):
                results.append((
                    OOp('max', (term.collection,)),
                    'FOLD_max_collapse',
                ))

        # ── 4. fold[min](inf, x) → min(x) ──
        if term.op_name in ('min', '.min'):
            if isinstance(term.init, OLit) and term.init.value == float('inf'):
                results.append((
                    OOp('min', (term.collection,)),
                    'FOLD_min_collapse',
                ))

        # ── 5. fold[append]([], x) → list(x) ──
        if term.op_name in ('append', 'list_append'):
            if isinstance(term.init, OSeq) and len(term.init.elements) == 0:
                results.append((
                    OOp('list', (term.collection,)),
                    'FOLD_append_to_list',
                ))

        # ── 6. fold[union]({}, x) → set(x) ──
        if term.op_name in ('union', 'set_add'):
            if isinstance(term.init, OOp) and term.init.name == 'set' and not term.init.args:
                results.append((
                    OOp('set', (term.collection,)),
                    'FOLD_union_to_set',
                ))

        # ── 7. Fold fusion: fold(f, map(g, x)) → fold(f∘g, x) ──
        if isinstance(term.collection, OMap):
            map_term = term.collection
            if isinstance(map_term.transform, OLam) and map_term.filter_pred is None:
                # fold[op](init, map(λy.body, x)) →
                # fold[op_hash](init, x) where hash encodes both op and transform
                import hashlib
                transform_canon = map_term.transform.canon()
                fused_hash = hashlib.md5(
                    f'{term.op_name}:{transform_canon}'.encode()
                ).hexdigest()[:8]
                results.append((
                    OFold(f'fused_{fused_hash}', term.init, map_term.collection),
                    'FOLD_map_fusion',
                ))

        # ── 8. fold over single-element: fold[op](init, [x]) → op(init, x) ──
        if isinstance(term.collection, OSeq) and len(term.collection.elements) == 1:
            elem = term.collection.elements[0]
            results.append((
                OOp(term.op_name, (term.init, elem)),
                'FOLD_singleton',
            ))

        # ── 9. fold over empty: fold[op](init, []) → init ──
        if isinstance(term.collection, OSeq) and len(term.collection.elements) == 0:
            results.append((
                term.init,
                'FOLD_empty',
            ))

        # ── 10. fold[concat]([], x) → flatten(x) ──
        if term.op_name in ('concat', 'extend', '.extend'):
            if isinstance(term.init, OSeq) and len(term.init.elements) == 0:
                results.append((
                    OOp('flatten', (term.collection,)),
                    'FOLD_concat_to_flatten',
                ))
            if isinstance(term.init, OOp) and term.init.name == 'list' and not term.init.args:
                results.append((
                    OOp('flatten', (term.collection,)),
                    'FOLD_concat_to_flatten',
                ))

    # ── Reverse direction: collapse back to fold ──
    if isinstance(term, OOp):
        # sum(x) → fold[add](0, x)
        if term.name == 'sum' and len(term.args) == 1:
            results.append((
                OFold('.add', OLit(0), term.args[0]),
                'FOLD_sum_expand',
            ))

        # prod(x) → fold[mul](1, x)
        if term.name == 'prod' and len(term.args) == 1:
            results.append((
                OFold('.mul', OLit(1), term.args[0]),
                'FOLD_prod_expand',
            ))

        # len(x) → fold[count](0, x)
        if term.name == 'len' and len(term.args) == 1:
            results.append((
                OFold('.count', OLit(0), term.args[0]),
                'FOLD_len_expand',
            ))

        # all(x) → fold[and](True, x)
        if term.name == 'all' and len(term.args) == 1:
            results.append((
                OFold('and', OLit(True), term.args[0]),
                'FOLD_all_expand',
            ))

        # any(x) → fold[or](False, x)
        if term.name == 'any' and len(term.args) == 1:
            results.append((
                OFold('or', OLit(False), term.args[0]),
                'FOLD_any_expand',
            ))

        # max(x) → fold[max](-inf, x)
        if term.name == 'max' and len(term.args) == 1:
            results.append((
                OFold('max', OLit(float('-inf')), term.args[0]),
                'FOLD_max_expand',
            ))

        # min(x) → fold[min](inf, x)
        if term.name == 'min' and len(term.args) == 1:
            results.append((
                OFold('min', OLit(float('inf')), term.args[0]),
                'FOLD_min_expand',
            ))

        # list(x) → fold[append]([], x)
        if term.name == 'list' and len(term.args) == 1:
            results.append((
                OFold('append', OSeq(()), term.args[0]),
                'FOLD_list_expand',
            ))

        # set(x) → fold[union](set(), x)
        if term.name == 'set' and len(term.args) == 1:
            results.append((
                OFold('union', OOp('set', ()), term.args[0]),
                'FOLD_set_expand',
            ))

        # flatten(x) → fold[concat]([], x)
        if term.name == 'flatten' and len(term.args) == 1:
            results.append((
                OFold('concat', OSeq(()), term.args[0]),
                'FOLD_flatten_expand',
            ))

    return results


def recognizes(term: OTerm) -> bool:
    """Return True if fold axioms can potentially rewrite *term*."""
    if isinstance(term, OFold):
        return True
    if isinstance(term, OOp) and term.name in ('sum', 'prod', 'len', 'all', 'any',
                                                 'max', 'min', 'list', 'set', 'flatten'):
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score FOLD's relevance."""
    sc = source.canon()
    tc = target.canon()
    s_fold = 'fold[' in sc
    t_fold = 'fold[' in tc
    has_sum = 'sum(' in sc or 'sum(' in tc
    has_prod = 'prod(' in sc or 'prod(' in tc
    if s_fold or t_fold:
        return 0.7
    if has_sum or has_prod:
        return 0.5
    return 0.1


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse direction — apply gives both directions already."""
    return apply(term, ctx)


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
    n = OVar('n')

    # fold[add](0, x) → sum(x)
    t1 = OFold('add', OLit(0), xs)
    r1 = apply(t1, ctx)
    _assert(any(a == 'FOLD_sum' for _, a in r1), "fold add → sum")

    # fold[mul](1, x) → prod(x)
    t2 = OFold('mul', OLit(1), xs)
    r2 = apply(t2, ctx)
    _assert(any(a == 'FOLD_prod' for _, a in r2), "fold mul → prod")

    # fold[and](True, x) → all(x)
    t3 = OFold('and', OLit(True), xs)
    r3 = apply(t3, ctx)
    _assert(any(a == 'FOLD_and_to_all' for _, a in r3), "fold and → all")

    # fold[or](False, x) → any(x)
    t4 = OFold('or', OLit(False), xs)
    r4 = apply(t4, ctx)
    _assert(any(a == 'FOLD_or_to_any' for _, a in r4), "fold or → any")

    # fold[max](-inf, x) → max(x)
    t5 = OFold('max', OLit(float('-inf')), xs)
    r5 = apply(t5, ctx)
    _assert(any(a == 'FOLD_max_collapse' for _, a in r5), "fold max collapse")

    # fold[min](inf, x) → min(x)
    t6 = OFold('min', OLit(float('inf')), xs)
    r6 = apply(t6, ctx)
    _assert(any(a == 'FOLD_min_collapse' for _, a in r6), "fold min collapse")

    # fold[append]([], x) → list(x)
    t7 = OFold('append', OSeq(()), xs)
    r7 = apply(t7, ctx)
    _assert(any(a == 'FOLD_append_to_list' for _, a in r7), "fold append → list")

    # Range normalisation: range(0, n) → range(n)
    t8 = OFold('add', OLit(0), OOp('range', (OLit(0), n)))
    r8 = apply(t8, ctx)
    _assert(any(a == 'FOLD_range_normalize' for _, a in r8), "range normalise")

    # sum(x) → fold[add](0, x)
    t9 = OOp('sum', (xs,))
    r9 = apply(t9, ctx)
    _assert(any(a == 'FOLD_sum_expand' for _, a in r9), "sum → fold expand")

    # len(x) → fold[count](0, x)
    t10 = OOp('len', (xs,))
    r10 = apply(t10, ctx)
    _assert(any(a == 'FOLD_len_expand' for _, a in r10), "len → fold expand")

    # fold over empty → init
    t11 = OFold('add', OLit(0), OSeq(()))
    r11 = apply(t11, ctx)
    _assert(any(a == 'FOLD_empty' for _, a in r11), "fold empty → init")

    # fold over singleton
    t12 = OFold('add', OLit(0), OSeq((OLit(5),)))
    r12 = apply(t12, ctx)
    _assert(any(a == 'FOLD_singleton' for _, a in r12), "fold singleton")

    # fold[concat]([], x) → flatten(x)
    t13 = OFold('concat', OSeq(()), xs)
    r13 = apply(t13, ctx)
    _assert(any(a == 'FOLD_concat_to_flatten' for _, a in r13), "fold concat → flatten")

    # Fold fusion: fold(op, map(g, x))
    t14 = OFold('add', OLit(0), OMap(OLam(('y',), OOp('neg', (OVar('y'),))), xs))
    r14 = apply(t14, ctx)
    _assert(any(a == 'FOLD_map_fusion' for _, a in r14), "fold-map fusion")

    # list(x) → fold[append]([], x)
    t15 = OOp('list', (xs,))
    r15 = apply(t15, ctx)
    _assert(any(a == 'FOLD_list_expand' for _, a in r15), "list → fold expand")

    # flatten(x) → fold[concat]([], x)
    t16 = OOp('flatten', (xs,))
    r16 = apply(t16, ctx)
    _assert(any(a == 'FOLD_flatten_expand' for _, a in r16), "flatten → fold expand")

    # recognizes
    _assert(recognizes(t1), "recognizes OFold")
    _assert(recognizes(t9), "recognizes sum")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    print(f"FOLD fold: {_pass} passed, {_fail} failed")
