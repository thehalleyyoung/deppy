"""P15 Axiom: Set Operation Equivalences.

Establishes equivalences between Python set operations and
their comprehension / dictionary equivalents.

Mathematical basis: Python sets are finite subsets S ⊆ U of a
universe U.  Set operations are the lattice operations of
the Boolean algebra P(U):
    S ∩ T = {x ∈ S : x ∈ T}          (meet)
    S ∪ T = {x : x ∈ S ∨ x ∈ T}     (join)
    S \ T = {x ∈ S : x ∉ T}          (relative complement)
    S △ T = (S ∪ T) \ (S ∩ T)         (symmetric difference)

Key rewrites:
  • set(xs) & set(ys)   ↔ {x for x in xs if x in ys}
  • set(xs) | set(ys)   ↔ set(list(xs) + list(ys))
  • set(xs) - set(ys)   ↔ {x for x in xs if x not in ys}
  • set(xs) ^ set(ys)   ↔ (set(xs)|set(ys)) - (set(xs)&set(ys))
  • len(set(xs))        ↔ len({x: None for x in xs})
  • list(set(xs))       ↔ list(dict.fromkeys(xs))  (order-preserving)

(§P15, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P15_set_ops"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["D12_map_construct", "D4_comp_fusion", "D5_fold_universal"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P15 Set Operation Equivalence).

1. set(xs) & set(ys) ≡ {x for x in xs if x in ys}
   Intersection: x ∈ S ∩ T ⟺ x ∈ S ∧ x ∈ T.
   The comprehension filters xs keeping elements in ys.
   Note: result is a set (unordered, deduplicated).

2. set(xs) | set(ys) ≡ set(list(xs) + list(ys))
   Union: S ∪ T = {x : x ∈ S ∨ x ∈ T}.
   Concatenation then set() deduplicates.

3. set(xs) - set(ys) ≡ {x for x in xs if x not in ys}
   Set difference: S \ T = {x ∈ S : x ∉ T}.

4. set(xs) ^ set(ys) ≡ (S | T) - (S & T)
   Symmetric difference = union minus intersection.

5. list(set(xs)) ≡ list(dict.fromkeys(xs))
   Python 3.7+ dicts preserve insertion order, so
   dict.fromkeys(xs) deduplicates while preserving first-occurrence
   order.  list(set(xs)) does NOT preserve order, so this is
   a refinement (order-preserving unique).

6. len(set(xs)) ≡ len({x: None for x in xs})
   Both count distinct elements.
"""

EXAMPLES = [
    ("set_and(set($xs), set($ys))", "filter_map(λ(x).in(x,$ys), id, $xs)", "P15_intersection"),
    ("set_or(set($xs), set($ys))", "set(add(list($xs), list($ys)))", "P15_union"),
    ("set_sub(set($xs), set($ys))", "filter_map(λ(x).notin(x,$ys), id, $xs)", "P15_difference"),
]

# Set operation names
_SET_BINARY = frozenset({'set_and', 'set_or', 'set_sub', 'set_xor',
                         '__and__', '__or__', '__sub__', '__xor__'})


def _is_set_call(term: OTerm) -> Optional[OTerm]:
    """Check if term is set(xs) and return xs."""
    if isinstance(term, OOp) and term.name == 'set' and len(term.args) == 1:
        return term.args[0]
    if isinstance(term, OQuotient) and term.equiv_class == 'perm':
        if isinstance(term.inner, OOp) and term.inner.name == 'set':
            return term.inner.args[0] if term.inner.args else None
    return None


def _is_frozenset_call(term: OTerm) -> Optional[OTerm]:
    """Check if term is frozenset(xs) and return xs."""
    if isinstance(term, OOp) and term.name == 'frozenset' and len(term.args) == 1:
        return term.args[0]
    return None


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P15: Set operation rewrites.

    Handles:
      1. set_and(set(xs), set(ys)) → filter comprehension
      2. set_or(set(xs), set(ys)) → set(list(xs) + list(ys))
      3. set_sub(set(xs), set(ys)) → filter comprehension
      4. set_xor(set(xs), set(ys)) → set_sub(set_or, set_and)
      5. len(set(xs)) → len(dict_fromkeys(xs))
      6. list(set(xs)) → list(dict_fromkeys(xs))  (preserves order)
      7. set(set(xs)) → set(xs)  (idempotent)
      8. set_and(s, s) → s  (idempotent)
      9. set_or(s, s) → s  (idempotent)
    """
    results: List[Tuple[OTerm, str]] = []

    # ── 1. set_and(set(xs), set(ys)) → filter comp ──
    if isinstance(term, OOp) and term.name in ('set_and', '__and__') and len(term.args) == 2:
        left, right = term.args
        xs = _is_set_call(left)
        ys = _is_set_call(right)
        if xs is not None and ys is not None:
            pred = OLam(('_x',), OOp('in', (OVar('_x'), ys)))
            identity = OLam(('_x',), OVar('_x'))
            results.append((
                OOp('set', (OMap(identity, xs, pred),)),
                'P15_intersection_to_comprehension',
            ))
        # ── 8. set_and(s, s) → s ──
        if left.canon() == right.canon():
            results.append((left, 'P15_and_idempotent'))

    # ── 2. set_or(set(xs), set(ys)) → set(list(xs) + list(ys)) ──
    if isinstance(term, OOp) and term.name in ('set_or', '__or__') and len(term.args) == 2:
        left, right = term.args
        xs = _is_set_call(left)
        ys = _is_set_call(right)
        if xs is not None and ys is not None:
            results.append((
                OOp('set', (OOp('add', (OOp('list', (xs,)), OOp('list', (ys,)))),)),
                'P15_union_to_concat',
            ))
        # ── 9. set_or(s, s) → s ──
        if left.canon() == right.canon():
            results.append((left, 'P15_or_idempotent'))

    # ── 3. set_sub(set(xs), set(ys)) → filter comp ──
    if isinstance(term, OOp) and term.name in ('set_sub', '__sub__') and len(term.args) == 2:
        left, right = term.args
        xs = _is_set_call(left)
        ys = _is_set_call(right)
        if xs is not None and ys is not None:
            pred = OLam(('_x',), OOp('notin', (OVar('_x'), ys)))
            identity = OLam(('_x',), OVar('_x'))
            results.append((
                OOp('set', (OMap(identity, xs, pred),)),
                'P15_difference_to_comprehension',
            ))

    # ── 4. set_xor → (union - intersection) ──
    if isinstance(term, OOp) and term.name in ('set_xor', '__xor__') and len(term.args) == 2:
        left, right = term.args
        union = OOp('set_or', (left, right))
        inter = OOp('set_and', (left, right))
        results.append((
            OOp('set_sub', (union, inter)),
            'P15_xor_to_union_minus_inter',
        ))

    # ── 5. len(set(xs)) → len(dict_fromkeys(xs)) ──
    if isinstance(term, OOp) and term.name == 'len' and len(term.args) == 1:
        xs = _is_set_call(term.args[0])
        if xs is not None:
            results.append((
                OOp('len', (OOp('fromkeys', (xs, OLit(None))),)),
                'P15_len_set_to_fromkeys',
            ))

    # ── 6. list(set(xs)) → list(dict.fromkeys(xs)) ──
    if isinstance(term, OOp) and term.name == 'list' and len(term.args) == 1:
        xs = _is_set_call(term.args[0])
        if xs is not None:
            results.append((
                OOp('list', (OOp('fromkeys', (xs, OLit(None))),)),
                'P15_list_set_to_fromkeys',
            ))

    # ── 7. set(set(xs)) → set(xs) ──
    if isinstance(term, OOp) and term.name == 'set' and len(term.args) == 1:
        inner_xs = _is_set_call(term.args[0])
        if inner_xs is not None:
            results.append((
                OOp('set', (inner_xs,)),
                'P15_set_idempotent',
            ))

    # ── frozenset(s) ↔ set-as-immutable ──
    if isinstance(term, OOp) and term.name == 'frozenset' and len(term.args) == 1:
        inner_xs = _is_set_call(term.args[0])
        if inner_xs is not None:
            results.append((
                OOp('frozenset', (inner_xs,)),
                'P15_frozenset_of_set',
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Recognizer & scoring
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    if isinstance(term, OOp):
        if term.name in _SET_BINARY:
            return True
        if term.name in ('set', 'frozenset') and len(term.args) == 1:
            return True
        if term.name in ('len', 'list') and len(term.args) == 1:
            if _is_set_call(term.args[0]) is not None:
                return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    sc, tc = source.canon(), target.canon()
    if 'set' in sc and 'set' in tc:
        return 0.85
    if any(op in sc for op in ('set_and', 'set_or', 'set_sub', 'set_xor')):
        return 0.7
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse: expand set comprehension back to operator form."""
    results: List[Tuple[OTerm, str]] = []

    # filter_map over xs checking in(ys) → set_and
    if isinstance(term, OOp) and term.name == 'set' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OMap) and inner.filter_pred is not None:
            pred = inner.filter_pred
            if isinstance(pred, OLam) and isinstance(pred.body, OOp):
                if pred.body.name == 'in' and len(pred.body.args) == 2:
                    ys = pred.body.args[1]
                    results.append((
                        OOp('set_and', (OOp('set', (inner.collection,)),
                                        OOp('set', (ys,)))),
                        'P15_inv_comp_to_intersection',
                    ))
                if pred.body.name == 'notin' and len(pred.body.args) == 2:
                    ys = pred.body.args[1]
                    results.append((
                        OOp('set_sub', (OOp('set', (inner.collection,)),
                                        OOp('set', (ys,)))),
                        'P15_inv_comp_to_difference',
                    ))

    # list(fromkeys(xs)) → list(set(xs))
    if isinstance(term, OOp) and term.name == 'list' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'fromkeys' and len(inner.args) == 2:
            results.append((
                OOp('list', (OOp('set', (inner.args[0],)),)),
                'P15_inv_fromkeys_to_set',
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

    # 1. intersection → comprehension
    t1 = OOp('set_and', (OOp('set', (OVar('xs'),)), OOp('set', (OVar('ys'),))))
    r1 = apply(t1)
    _assert(any(a == 'P15_intersection_to_comprehension' for _, a in r1), "intersection → comp")

    # 2. union → concat
    t2 = OOp('set_or', (OOp('set', (OVar('xs'),)), OOp('set', (OVar('ys'),))))
    r2 = apply(t2)
    _assert(any(a == 'P15_union_to_concat' for _, a in r2), "union → concat")

    # 3. difference → comprehension
    t3 = OOp('set_sub', (OOp('set', (OVar('xs'),)), OOp('set', (OVar('ys'),))))
    r3 = apply(t3)
    _assert(any(a == 'P15_difference_to_comprehension' for _, a in r3), "difference → comp")

    # 4. xor → union - intersection
    t4 = OOp('set_xor', (OOp('set', (OVar('xs'),)), OOp('set', (OVar('ys'),))))
    r4 = apply(t4)
    _assert(any(a == 'P15_xor_to_union_minus_inter' for _, a in r4), "xor → union - inter")

    # 5. len(set(xs)) → len(fromkeys)
    t5 = OOp('len', (OOp('set', (OVar('xs'),)),))
    r5 = apply(t5)
    _assert(any(a == 'P15_len_set_to_fromkeys' for _, a in r5), "len(set) → fromkeys")

    # 6. list(set(xs)) → list(fromkeys)
    t6 = OOp('list', (OOp('set', (OVar('xs'),)),))
    r6 = apply(t6)
    _assert(any(a == 'P15_list_set_to_fromkeys' for _, a in r6), "list(set) → fromkeys")

    # 7. set(set(xs)) → set(xs)
    t7 = OOp('set', (OOp('set', (OVar('xs'),)),))
    r7 = apply(t7)
    _assert(any(a == 'P15_set_idempotent' for _, a in r7), "set idempotent")

    # 8. set_and(s, s) → s
    s8 = OOp('set', (OVar('xs'),))
    t8 = OOp('set_and', (s8, s8))
    r8 = apply(t8)
    _assert(any(a == 'P15_and_idempotent' for _, a in r8), "and idempotent")

    # 9. set_or(s, s) → s
    t9 = OOp('set_or', (s8, s8))
    r9 = apply(t9)
    _assert(any(a == 'P15_or_idempotent' for _, a in r9), "or idempotent")

    # 10. recognizes
    _assert(recognizes(t1), "recognizes set_and")
    _assert(recognizes(t5), "recognizes len(set)")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # 11. relevance
    _assert(relevance_score(t1, t2) > 0.5, "set-set relevance high")

    # 12. inverse
    pred = OLam(('_x',), OOp('in', (OVar('_x'), OVar('ys'))))
    ident = OLam(('_x',), OVar('_x'))
    comp_set = OOp('set', (OMap(ident, OVar('xs'), pred),))
    ri = apply_inverse(comp_set)
    _assert(any(a == 'P15_inv_comp_to_intersection' for _, a in ri), "inv comp → intersection")

    print(f"P15 set_ops: {_pass} passed, {_fail} failed")
