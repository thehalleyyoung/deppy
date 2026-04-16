"""P16 Axiom: Type Conversion Chain Equivalences.

Establishes equivalences for redundant type conversion chains
in Python, canonicalizing them to minimal forms.

Mathematical basis: Type constructors list(), tuple(), set(), int(),
str(), float() are endomorphisms on the category of Python values.
Many compositions are idempotent or can be simplified:
    list ∘ tuple ∘ list = list       (intermediate tuple is no-op)
    list ∘ list = list               (idempotent)
    sorted ∘ list = sorted           (list is redundant before sorted)

The axiom identifies and eliminates redundant conversions.

Key rewrites:
  • list(tuple(xs))     →  list(xs)
  • tuple(list(xs))     →  tuple(xs)
  • list(list(xs))      →  list(xs)    (idempotent)
  • set(set(xs))        →  set(xs)     (idempotent)
  • sorted(list(xs))    →  sorted(xs)
  • list(map(int, s.split()))  ↔  [int(x) for x in s.split()]

(§P16, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P16_type_convert"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["D4_comp_fusion", "D24_eta", "P14_slicing"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P16 Type Conversion Chain Simplification).

1. list(tuple(xs)) ≡ list(xs)
   tuple(xs) produces a sequence; list() re-materializes.
   Since tuple preserves order and elements, the intermediate
   tuple is a no-op for the final list result.

2. tuple(list(xs)) ≡ tuple(xs)
   Symmetric to (1).

3. list(list(xs)) ≡ list(xs)   (idempotent)
   list(xs) when xs is already a list creates a shallow copy.
   Semantically the result is the same sequence.

4. set(set(xs)) ≡ set(xs)     (idempotent)
   set() on a set is a copy.

5. sorted(list(xs)) ≡ sorted(xs)
   sorted() accepts any iterable; wrapping in list() first
   is redundant.

6. list(map(f, xs)) ≡ [f(x) for x in xs]
   By definition of map and list comprehension.
"""

EXAMPLES = [
    ("list(tuple($xs))", "list($xs)", "P16_list_tuple"),
    ("tuple(list($xs))", "tuple($xs)", "P16_tuple_list"),
    ("list(list($xs))", "list($xs)", "P16_list_idempotent"),
    ("sorted(list($xs))", "sorted($xs)", "P16_sorted_list"),
    ("list(map(int, split($s)))", "[int(x) for x in split($s)]", "P16_map_to_comp"),
]

# Sequence constructors that are transparent pass-throughs
_SEQ_CONSTRUCTORS = frozenset({'list', 'tuple'})

# Idempotent constructors: f(f(x)) = f(x)
_IDEMPOTENT = frozenset({'list', 'tuple', 'set', 'frozenset', 'str', 'bytes',
                          'int', 'float', 'bool'})

# Constructors that accept any iterable — wrapping in list first is redundant
_ITERABLE_CONSUMERS = frozenset({'sorted', 'set', 'frozenset', 'tuple',
                                  'min', 'max', 'sum', 'any', 'all',
                                  'enumerate', 'reversed'})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P16: Type conversion chain simplification.

    Handles:
      1. list(tuple(xs)) → list(xs)  (intermediate transparent)
      2. tuple(list(xs)) → tuple(xs)
      3. f(f(xs)) → f(xs)  for idempotent constructors
      4. sorted(list(xs)) → sorted(xs)  (list before consumer)
      5. list(map(f, xs)) ↔ comp(f, xs)
      6. str(int(s)) → strip(s) pattern
      7. int(float(x)) → int(x) when valid
    """
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp) or len(term.args) != 1:
        return results

    outer = term.name
    inner_term = term.args[0]

    # ── Pattern: outer(inner(xs)) ──
    if isinstance(inner_term, OOp) and len(inner_term.args) == 1:
        inner = inner_term.name
        xs = inner_term.args[0]

        # ── 1–2. Transparent intermediates ──
        if outer in _SEQ_CONSTRUCTORS and inner in _SEQ_CONSTRUCTORS and outer != inner:
            results.append((
                OOp(outer, (xs,)),
                f'P16_{outer}_{inner}_transparent',
            ))

        # ── 3. Idempotent: f(f(x)) → f(x) ──
        if outer == inner and outer in _IDEMPOTENT:
            results.append((
                inner_term,
                f'P16_{outer}_idempotent',
            ))

        # ── 4. Consumer absorbs list: sorted(list(xs)) → sorted(xs) ──
        if outer in _ITERABLE_CONSUMERS and inner == 'list':
            results.append((
                OOp(outer, (xs,)),
                f'P16_{outer}_absorbs_list',
            ))

        # ── 4b. Consumer absorbs tuple: sorted(tuple(xs)) → sorted(xs) ──
        if outer in _ITERABLE_CONSUMERS and inner == 'tuple':
            results.append((
                OOp(outer, (xs,)),
                f'P16_{outer}_absorbs_tuple',
            ))

        # ── 7. int(float(x)) → int(x) ──
        if outer == 'int' and inner == 'float':
            results.append((
                OOp('int', (xs,)),
                'P16_int_float_collapse',
            ))

        # ── str(int(s)) pattern ──
        if outer == 'str' and inner == 'int':
            results.append((
                OOp('.strip', (xs,)),
                'P16_str_int_to_strip',
            ))

    # ── 5. list(map(f, xs)) → comprehension ──
    if outer == 'list' and isinstance(inner_term, OOp):
        if inner_term.name == 'map' and len(inner_term.args) == 2:
            fn, coll = inner_term.args
            results.append((
                OMap(fn, coll),
                'P16_list_map_to_comprehension',
            ))

    # ── Inverse: comprehension → list(map(...)) ──
    if outer == 'list' and isinstance(inner_term, OMap):
        results.append((
            OOp('list', (OOp('map', (inner_term.transform, inner_term.collection)),)),
            'P16_comprehension_to_list_map',
        ))

    # ── sorted absorbs list wrapper from OMap ──
    if outer == 'sorted' and isinstance(inner_term, OOp):
        if inner_term.name == 'list' and len(inner_term.args) == 1:
            # sorted(list(...)) is handled above; also handle sorted(list(map))
            pass

    return results


# ═══════════════════════════════════════════════════════════
# Recognizer & scoring
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    if not isinstance(term, OOp) or len(term.args) != 1:
        return False
    outer = term.name
    inner = term.args[0]
    if isinstance(inner, OOp) and len(inner.args) >= 1:
        if outer in _IDEMPOTENT | _ITERABLE_CONSUMERS | _SEQ_CONSTRUCTORS:
            return True
    if outer == 'list' and isinstance(inner, (OOp, OMap)):
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    sc, tc = source.canon(), target.canon()
    for c in ('list', 'tuple', 'set', 'sorted', 'int', 'float', 'str'):
        if c in sc and c in tc:
            return 0.7
    if 'map(' in sc and 'map(' in tc:
        return 0.6
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse: add intermediate conversions back."""
    results: List[Tuple[OTerm, str]] = []

    # list(xs) → list(tuple(xs))
    if isinstance(term, OOp) and term.name == 'list' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OOp('list', (OOp('tuple', (xs,)),)),
            'P16_inv_add_tuple',
        ))

    # sorted(xs) → sorted(list(xs))
    if isinstance(term, OOp) and term.name == 'sorted' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OOp('sorted', (OOp('list', (xs,)),)),
            'P16_inv_add_list_before_sorted',
        ))

    # comprehension → list(map(...))
    if isinstance(term, OMap) and term.filter_pred is None:
        results.append((
            OOp('list', (OOp('map', (term.transform, term.collection)),)),
            'P16_inv_comp_to_list_map',
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

    # 1. list(tuple(xs)) → list(xs)
    t1 = OOp('list', (OOp('tuple', (OVar('xs'),)),))
    r1 = apply(t1)
    _assert(any('P16_list_tuple_transparent' in a for _, a in r1), "list(tuple) → list")

    # 2. tuple(list(xs)) → tuple(xs)
    t2 = OOp('tuple', (OOp('list', (OVar('xs'),)),))
    r2 = apply(t2)
    _assert(any('P16_tuple_list_transparent' in a for _, a in r2), "tuple(list) → tuple")

    # 3. list(list(xs)) → list(xs)
    t3 = OOp('list', (OOp('list', (OVar('xs'),)),))
    r3 = apply(t3)
    _assert(any('P16_list_idempotent' in a for _, a in r3), "list idempotent")

    # 4. set(set(xs)) → set(xs)
    t4 = OOp('set', (OOp('set', (OVar('xs'),)),))
    r4 = apply(t4)
    _assert(any('P16_set_idempotent' in a for _, a in r4), "set idempotent")

    # 5. sorted(list(xs)) → sorted(xs)
    t5 = OOp('sorted', (OOp('list', (OVar('xs'),)),))
    r5 = apply(t5)
    _assert(any('P16_sorted_absorbs_list' in a for _, a in r5), "sorted absorbs list")

    # 6. list(map(f, xs)) → comprehension
    t6 = OOp('list', (OOp('map', (OVar('f'), OVar('xs'))),))
    r6 = apply(t6)
    _assert(any('P16_list_map_to_comprehension' in a for _, a in r6), "list(map) → comp")

    # 7. int(float(x)) → int(x)
    t7 = OOp('int', (OOp('float', (OVar('x'),)),))
    r7 = apply(t7)
    _assert(any('P16_int_float_collapse' in a for _, a in r7), "int(float) → int")

    # 8. recognizes
    _assert(recognizes(t1), "recognizes list(tuple)")
    _assert(recognizes(t5), "recognizes sorted(list)")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # 9. relevance
    _assert(relevance_score(t1, OOp('list', (OVar('xs'),))) > 0.5, "relevance high")

    # 10. inverse: list(xs) → list(tuple(xs))
    t10 = OOp('list', (OVar('xs'),))
    r10 = apply_inverse(t10)
    _assert(any(a == 'P16_inv_add_tuple' for _, a in r10), "inv add tuple")

    # 11. inverse: sorted(xs) → sorted(list(xs))
    t11 = OOp('sorted', (OVar('xs'),))
    r11 = apply_inverse(t11)
    _assert(any(a == 'P16_inv_add_list_before_sorted' for _, a in r11), "inv add list")

    # 12. inverse: comprehension → list(map)
    t12 = OMap(OLam(('x',), OOp('f', (OVar('x'),))), OVar('xs'))
    r12 = apply_inverse(t12)
    _assert(any(a == 'P16_inv_comp_to_list_map' for _, a in r12), "inv comp → list(map)")

    print(f"P16 type_convert: {_pass} passed, {_fail} failed")
