"""P24 Axiom: Copy / Mutability Equivalences.

Establishes equivalences between Python copy and mutability
patterns: shallow copy idioms, deep copy, immutable conversions,
and mutable-vs-immutable operation pairs.

Mathematical basis: Python values live in a category with
sharing (aliasing).  A copy operation creates a fresh object
with the same value but distinct identity:
    copy(x) ≡ x  as values, but  copy(x) is not x  as objects.

For immutable types (int, str, tuple, frozenset), copy is the
identity — there is no aliasing issue.

Key rewrites:
  • xs.copy() ↔ list(xs) ↔ xs[:] ↔ [*xs]  (shallow list copy)
  • d.copy() ↔ dict(d) ↔ {**d}              (shallow dict copy)
  • copy.deepcopy(x) ↔ manual recursive copy
  • sorted(xs) returns new list vs xs.sort() mutates
  • tuple(xs) as immutable version of list(xs)
  • frozenset(s) ↔ immutable set

(§P24, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P24_copy"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P14_slicing", "P15_set_ops", "P16_type_convert"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P24 Copy / Mutability Equivalence).

1. xs.copy() ≡ list(xs) ≡ xs[:] ≡ [*xs]
   All produce a new list with the same elements (shallow copy).
   list(xs) iterates xs and collects; xs[:] is slice-copy;
   [*xs] is star-unpack into a new list.

2. d.copy() ≡ dict(d) ≡ {**d}
   All produce a new dict with the same key-value pairs.

3. copy.deepcopy(x) recursively copies all nested mutable objects.
   For flat structures, deepcopy ≡ shallow copy.

4. sorted(xs) always returns a new list; xs.sort() mutates in-place.
   As pure functions on values: sorted(xs) ≡ inplace_sort(copy(xs)).

5. tuple(xs) produces an immutable version of list xs.
   frozenset(s) produces an immutable version of set s.
   These are injections into the immutable sub-category.
"""

EXAMPLES = [
    (".copy($xs)", "list($xs)", "P24_copy_to_list"),
    (".copy($xs)", "slice_all($xs)", "P24_copy_to_slice"),
    (".copy($xs)", "unpack_list($xs)", "P24_copy_to_unpack"),
    (".copy($d)", "dict($d)", "P24_dict_copy_to_dict"),
    (".copy($d)", "dict_unpack($d)", "P24_dict_copy_to_unpack"),
    ("sorted($xs)", "inplace_sort(copy($xs))", "P24_sorted_vs_sort"),
]

# Copy-related operations
_COPY_OPS = frozenset({
    '.copy', 'list_copy', 'dict_copy', 'set_copy',
    'slice_all', 'unpack_list', 'unpack_dict',
    'deepcopy', 'copy',
})

# Mutable-immutable pairs
_MUTABLE_IMMUTABLE = {
    'list': 'tuple',
    'set': 'frozenset',
    'dict': 'types.MappingProxyType',
}


def _is_list_copy(term: OTerm) -> Optional[OTerm]:
    """Detect various list copy patterns."""
    if isinstance(term, OOp) and term.name == '.copy' and len(term.args) == 1:
        return term.args[0]
    if isinstance(term, OOp) and term.name == 'list_copy' and len(term.args) == 1:
        return term.args[0]
    if isinstance(term, OOp) and term.name == 'slice_all' and len(term.args) == 1:
        return term.args[0]
    if isinstance(term, OOp) and term.name == 'unpack_list' and len(term.args) == 1:
        return term.args[0]
    return None


def _is_dict_copy(term: OTerm) -> Optional[OTerm]:
    """Detect various dict copy patterns."""
    if isinstance(term, OOp) and term.name == 'dict_copy' and len(term.args) == 1:
        return term.args[0]
    if isinstance(term, OOp) and term.name == 'unpack_dict' and len(term.args) == 1:
        return term.args[0]
    return None


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P24: Copy / mutability rewrites.

    Handles:
      1. .copy(xs) → list(xs)
      2. .copy(xs) → slice_all(xs)  (xs[:])
      3. .copy(xs) → unpack_list(xs)  ([*xs])
      4. list(xs) → .copy(xs)
      5. slice_all(xs) → list(xs)
      6. unpack_list(xs) → list(xs)
      7. dict_copy(d) → dict(d)
      8. dict_copy(d) → unpack_dict(d)  ({**d})
      9. dict(d) → dict_copy(d)
     10. deepcopy(x) → copy(x)  (for flat types)
     11. sorted(xs) ↔ inplace_sort(copy(xs))
     12. tuple(xs) as immutable list
     13. frozenset(s) as immutable set
     14. .sort(xs) → sorted(xs) — mutating to pure
    """
    results: List[Tuple[OTerm, str]] = []

    # ── List copy equivalences ──
    xs = _is_list_copy(term)
    if xs is not None:
        orig_name = term.name if isinstance(term, OOp) else ''
        # .copy → list
        if orig_name != 'list':
            results.append((OOp('list', (xs,)), 'P24_copy_to_list'))
        # .copy → slice_all
        if orig_name != 'slice_all':
            results.append((OOp('slice_all', (xs,)), 'P24_copy_to_slice_all'))
        # .copy → unpack_list
        if orig_name != 'unpack_list':
            results.append((OOp('unpack_list', (xs,)), 'P24_copy_to_unpack_list'))

    # ── list(xs) → .copy(xs)  (when xs is known to be a list) ──
    if isinstance(term, OOp) and term.name == 'list' and len(term.args) == 1:
        xs = term.args[0]
        results.append((OOp('.copy', (xs,)), 'P24_list_to_copy'))
        results.append((OOp('slice_all', (xs,)), 'P24_list_to_slice_all'))
        results.append((OOp('unpack_list', (xs,)), 'P24_list_to_unpack_list'))

    # ── Dict copy equivalences ──
    d = _is_dict_copy(term)
    if d is not None:
        orig_name = term.name if isinstance(term, OOp) else ''
        if orig_name != 'dict':
            results.append((OOp('dict', (d,)), 'P24_dict_copy_to_dict'))
        if orig_name != 'unpack_dict':
            results.append((OOp('unpack_dict', (d,)), 'P24_dict_copy_to_unpack'))

    if isinstance(term, OOp) and term.name == 'dict' and len(term.args) == 1:
        d = term.args[0]
        results.append((OOp('dict_copy', (d,)), 'P24_dict_to_dict_copy'))
        results.append((OOp('unpack_dict', (d,)), 'P24_dict_to_unpack'))

    # ── Deep copy ↔ shallow copy (for flat structures) ──
    if isinstance(term, OOp) and term.name == 'deepcopy' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OOp('copy', (xs,)),
            'P24_deepcopy_to_shallow',
        ))

    if isinstance(term, OOp) and term.name == 'copy' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OOp('deepcopy', (xs,)),
            'P24_shallow_to_deepcopy',
        ))

    # ── sorted(xs) ↔ inplace_sort(copy(xs)) ──
    if isinstance(term, OOp) and term.name == 'sorted' and len(term.args) >= 1:
        xs = term.args[0]
        results.append((
            OOp('inplace_sort', (OOp('.copy', (xs,)),)),
            'P24_sorted_to_inplace_sort_copy',
        ))

    if isinstance(term, OOp) and term.name == 'inplace_sort' and len(term.args) == 1:
        inner = term.args[0]
        copy_xs = _is_list_copy(inner)
        if copy_xs is not None:
            results.append((
                OOp('sorted', (copy_xs,)),
                'P24_inplace_sort_copy_to_sorted',
            ))

    # ── .sort(xs) → sorted(xs)  (mutating to pure) ──
    if isinstance(term, OOp) and term.name == '.sort' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OOp('sorted', (xs,)),
            'P24_sort_to_sorted',
        ))

    # ── tuple(xs) ↔ immutable list ──
    if isinstance(term, OOp) and term.name == 'tuple' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OOp('immutable_list', (xs,)),
            'P24_tuple_as_immutable_list',
        ))

    if isinstance(term, OOp) and term.name == 'immutable_list' and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OOp('tuple', (xs,)),
            'P24_immutable_list_to_tuple',
        ))

    # ── frozenset(s) ↔ immutable set ──
    if isinstance(term, OOp) and term.name == 'frozenset' and len(term.args) == 1:
        results.append((
            OOp('immutable_set', term.args),
            'P24_frozenset_as_immutable_set',
        ))

    if isinstance(term, OOp) and term.name == 'immutable_set' and len(term.args) == 1:
        results.append((
            OOp('frozenset', term.args),
            'P24_immutable_set_to_frozenset',
        ))

    # ── set_copy(s) → set(s) ──
    if isinstance(term, OOp) and term.name == 'set_copy' and len(term.args) == 1:
        results.append((
            OOp('set', term.args),
            'P24_set_copy_to_set',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Recognizer & scoring
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    if isinstance(term, OOp):
        if term.name in _COPY_OPS:
            return True
        if term.name in ('list', 'dict', 'sorted', 'inplace_sort', '.sort',
                         'tuple', 'frozenset', 'immutable_list', 'immutable_set',
                         'set_copy'):
            return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    sc, tc = source.canon(), target.canon()
    for kw in ('copy', 'slice_all', 'unpack', 'list(', 'dict(',
               'sorted', 'sort', 'tuple', 'frozenset', 'deepcopy'):
        if kw in sc and kw in tc:
            return 0.8
    if '.copy' in sc and ('list' in tc or 'slice' in tc or 'unpack' in tc):
        return 0.75
    if 'sorted' in sc and 'sort' in tc:
        return 0.7
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse: expand copy patterns."""
    results: List[Tuple[OTerm, str]] = []

    # sorted(xs) → .sort mutating
    if isinstance(term, OOp) and term.name == 'sorted' and len(term.args) == 1:
        results.append((
            OOp('.sort', term.args),
            'P24_inv_sorted_to_sort',
        ))

    # tuple → list (mutable form)
    if isinstance(term, OOp) and term.name == 'tuple' and len(term.args) == 1:
        results.append((
            OOp('list', term.args),
            'P24_inv_tuple_to_list',
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

    # 1. .copy → list
    t1 = OOp('.copy', (OVar('xs'),))
    r1 = apply(t1)
    _assert(any(a == 'P24_copy_to_list' for _, a in r1), ".copy → list")

    # 2. .copy → slice_all
    _assert(any(a == 'P24_copy_to_slice_all' for _, a in r1), ".copy → slice_all")

    # 3. .copy → unpack_list
    _assert(any(a == 'P24_copy_to_unpack_list' for _, a in r1), ".copy → unpack_list")

    # 4. list(xs) → .copy, slice_all, unpack_list
    t4 = OOp('list', (OVar('xs'),))
    r4 = apply(t4)
    _assert(any(a == 'P24_list_to_copy' for _, a in r4), "list → .copy")
    _assert(any(a == 'P24_list_to_slice_all' for _, a in r4), "list → slice_all")

    # 5. dict_copy → dict
    t5 = OOp('dict_copy', (OVar('d'),))
    r5 = apply(t5)
    _assert(any(a == 'P24_dict_copy_to_dict' for _, a in r5), "dict_copy → dict")

    # 6. dict_copy → unpack_dict
    _assert(any(a == 'P24_dict_copy_to_unpack' for _, a in r5), "dict_copy → unpack")

    # 7. dict(d) → dict_copy, unpack_dict
    t7 = OOp('dict', (OVar('d'),))
    r7 = apply(t7)
    _assert(any(a == 'P24_dict_to_dict_copy' for _, a in r7), "dict → dict_copy")

    # 8. deepcopy → copy
    t8 = OOp('deepcopy', (OVar('x'),))
    r8 = apply(t8)
    _assert(any(a == 'P24_deepcopy_to_shallow' for _, a in r8), "deepcopy → shallow")

    # 9. copy → deepcopy
    t9 = OOp('copy', (OVar('x'),))
    r9 = apply(t9)
    _assert(any(a == 'P24_shallow_to_deepcopy' for _, a in r9), "shallow → deepcopy")

    # 10. sorted → inplace_sort(copy)
    t10 = OOp('sorted', (OVar('xs'),))
    r10 = apply(t10)
    _assert(any(a == 'P24_sorted_to_inplace_sort_copy' for _, a in r10), "sorted → sort(copy)")

    # 11. inplace_sort(.copy(xs)) → sorted(xs)
    t11 = OOp('inplace_sort', (OOp('.copy', (OVar('xs'),)),))
    r11 = apply(t11)
    _assert(any(a == 'P24_inplace_sort_copy_to_sorted' for _, a in r11), "sort(copy) → sorted")

    # 12. .sort → sorted
    t12 = OOp('.sort', (OVar('xs'),))
    r12 = apply(t12)
    _assert(any(a == 'P24_sort_to_sorted' for _, a in r12), ".sort → sorted")

    # 13. tuple → immutable_list
    t13 = OOp('tuple', (OVar('xs'),))
    r13 = apply(t13)
    _assert(any(a == 'P24_tuple_as_immutable_list' for _, a in r13), "tuple → immutable_list")

    # 14. frozenset → immutable_set
    t14 = OOp('frozenset', (OVar('s'),))
    r14 = apply(t14)
    _assert(any(a == 'P24_frozenset_as_immutable_set' for _, a in r14), "frozenset → immut_set")

    # 15. immutable_list → tuple
    t15 = OOp('immutable_list', (OVar('xs'),))
    r15 = apply(t15)
    _assert(any(a == 'P24_immutable_list_to_tuple' for _, a in r15), "immut_list → tuple")

    # 16. set_copy → set
    t16 = OOp('set_copy', (OVar('s'),))
    r16 = apply(t16)
    _assert(any(a == 'P24_set_copy_to_set' for _, a in r16), "set_copy → set")

    # 17. recognizes
    _assert(recognizes(t1), "recognizes .copy")
    _assert(recognizes(t8), "recognizes deepcopy")
    _assert(recognizes(t10), "recognizes sorted")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # 18. relevance
    _assert(relevance_score(t1, t4) > 0.5, "copy/list relevance")

    # 19. inverse: sorted → .sort
    r19 = apply_inverse(t10)
    _assert(any(a == 'P24_inv_sorted_to_sort' for _, a in r19), "inv sorted → sort")

    # 20. inverse: tuple → list
    r20 = apply_inverse(t13)
    _assert(any(a == 'P24_inv_tuple_to_list' for _, a in r20), "inv tuple → list")

    print(f"P24 copy: {_pass} passed, {_fail} failed")
