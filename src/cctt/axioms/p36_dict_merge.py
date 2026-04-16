"""P36 Axiom: Dict Merge / Update Equivalences.

Establishes equivalences between different Python dictionary merging
and update patterns: unpacking merge {**a, **b}, the pipe operator
a | b (3.9+), dict.update(), augmented assignment |=, ChainMap,
dict constructor merge, and conditional-merge idioms.

Mathematical basis: Dictionaries are partial functions
  d : K ⇀ V
with finite support.  Merging two dicts is the right-biased union
of partial functions:

  (a | b)(k) = b(k)  if k ∈ dom(b),  else a(k)

This operation is associative but NOT commutative (the right operand
wins on key collisions).  All the following notations denote the same
right-biased union:

  {**a, **b}  ≡  a | b  ≡  (c := a.copy(); c.update(b); c)
            ≡  dict(a, **b)  (when b keys are strings)

ChainMap(b, a) reverses lookup order but is semantically equivalent
to a | b for read-only access (first-found semantics with b first).

dict.setdefault(k, v) is the left-biased insertion:
  d' = d  if k ∈ dom(d),  else d ∪ {k↦v}
which equals  if k not in d: d[k] = v.

Key rewrites:
  • {**a, **b} ↔ a | b
  • dict.update(b) ↔ d |= b
  • ChainMap(b, a) ↔ a | b (read-only)
  • dict(a, **b) ↔ {**a, **b}
  • dict.setdefault(k, v) ↔ if k not in d: d[k] = v
  • conditional merge patterns
  • dict.fromkeys(keys, val) ↔ {k: val for k in keys}
  • d.copy(); d.update(b) ↔ d | b

(§P36, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P36_dict_merge"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P03_dict_ops", "P01_comprehension", "P08_unpacking"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P36 Dict Merge / Update Equivalences).

1. dict_unpack_merge(a, b) ≡ dict_pipe_merge(a, b)
   {**a, **b} and a | b both compute the right-biased union of
   partial functions a and b.  PEP 584 defines | as exactly this.

2. dict_update(d, b) ≡ dict_ior(d, b)
   d.update(b) mutates d in-place, as does d |= b.  Both set
   d(k) = b(k) for all k ∈ dom(b), preserving existing keys.

3. chainmap(b, a) ≡ dict_merged(a, b)
   ChainMap(b, a) searches b first, then a.  For read-only
   access this is equivalent to {**a, **b} where b overrides a.

4. dict_constructor_merge(a, b) ≡ dict_unpack_merge_alt(a, b)
   dict(a, **b) and {**a, **b} produce the same dict when b has
   string keys (required by the dict() keyword-arg syntax).

5. dict_setdefault(d, k, v) ≡ dict_if_not_in(d, k, v)
   d.setdefault(k, v) and "if k not in d: d[k] = v" both
   implement left-biased insertion.

6. dict_conditional_merge(d, k, v, cond) ≡ dict_update_if(d, k, v, cond)
   Merge key k with value v only if cond holds.

7. dict_fromkeys(keys, val) ≡ dict_comprehension_keys(keys, val)
   dict.fromkeys(keys, val) and {k: val for k in keys} both
   construct a dict mapping each key to val.

8. dict_copy_update(d, b) ≡ dict_new_merge(d, b)
   d2 = d.copy(); d2.update(b) is equivalent to d | b,
   producing a new dict without mutating d.

9. dict_unpack_merge(a, b) ≡ dict_constructor_merge(a, b)
   {**a, **b} ≡ dict(a, **b) when b keys are all strings.

10. chainmap(a) ≡ dict_merged(a)
    ChainMap with a single dict is equivalent to the dict itself.
"""

EXAMPLES = [
    ("dict_unpack_merge($a, $b)", "dict_pipe_merge($a, $b)",
     "P36_unpack_to_pipe"),
    ("dict_update($d, $b)", "dict_ior($d, $b)", "P36_update_to_ior"),
    ("chainmap($b, $a)", "dict_merged($a, $b)", "P36_chainmap_to_merged"),
    ("dict_setdefault($d, $k, $v)", "dict_if_not_in($d, $k, $v)",
     "P36_setdefault_to_if"),
    ("dict_fromkeys($keys, $val)", "dict_comprehension_keys($keys, $val)",
     "P36_fromkeys_to_comp"),
]

_DICT_MERGE_OPS = frozenset({
    'dict_unpack_merge', 'dict_pipe_merge', 'dict_update', 'dict_ior',
    'chainmap', 'dict_merged', 'dict_constructor_merge',
    'dict_unpack_merge_alt', 'dict_setdefault', 'dict_if_not_in',
    'dict_conditional_merge', 'dict_update_if', 'dict_fromkeys',
    'dict_comprehension_keys', 'dict_copy_update', 'dict_new_merge',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P36: Dict merge/update equivalence rewrites (forward)."""
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp):
        return results

    # ── 1. dict_unpack_merge ↔ dict_pipe_merge ──
    if term.name == 'dict_unpack_merge' and len(term.args) == 2:
        results.append((
            OOp('dict_pipe_merge', term.args),
            'P36_unpack_to_pipe',
        ))

    if term.name == 'dict_pipe_merge' and len(term.args) == 2:
        results.append((
            OOp('dict_unpack_merge', term.args),
            'P36_pipe_to_unpack',
        ))

    # ── 2. dict_update ↔ dict_ior ──
    if term.name == 'dict_update' and len(term.args) == 2:
        results.append((
            OOp('dict_ior', term.args),
            'P36_update_to_ior',
        ))

    if term.name == 'dict_ior' and len(term.args) == 2:
        results.append((
            OOp('dict_update', term.args),
            'P36_ior_to_update',
        ))

    # ── 3. chainmap ↔ dict_merged ──
    if term.name == 'chainmap' and len(term.args) == 2:
        # ChainMap(b, a) → {**a, **b} — note argument order flip
        a, b = term.args[1], term.args[0]
        results.append((
            OOp('dict_merged', (a, b)),
            'P36_chainmap_to_merged',
        ))

    if term.name == 'dict_merged' and len(term.args) == 2:
        a, b = term.args
        results.append((
            OOp('chainmap', (b, a)),
            'P36_merged_to_chainmap',
        ))

    # ── 4. dict_constructor_merge ↔ dict_unpack_merge_alt ──
    if term.name == 'dict_constructor_merge' and len(term.args) == 2:
        results.append((
            OOp('dict_unpack_merge_alt', term.args),
            'P36_constructor_to_unpack',
        ))

    if term.name == 'dict_unpack_merge_alt' and len(term.args) == 2:
        results.append((
            OOp('dict_constructor_merge', term.args),
            'P36_unpack_to_constructor',
        ))

    # ── 5. dict_setdefault ↔ dict_if_not_in ──
    if term.name == 'dict_setdefault' and len(term.args) == 3:
        results.append((
            OOp('dict_if_not_in', term.args),
            'P36_setdefault_to_if',
        ))

    if term.name == 'dict_if_not_in' and len(term.args) == 3:
        results.append((
            OOp('dict_setdefault', term.args),
            'P36_if_to_setdefault',
        ))

    # ── 6. dict_conditional_merge ↔ dict_update_if ──
    if term.name == 'dict_conditional_merge' and len(term.args) >= 3:
        results.append((
            OOp('dict_update_if', term.args),
            'P36_cond_merge_to_update_if',
        ))

    if term.name == 'dict_update_if' and len(term.args) >= 3:
        results.append((
            OOp('dict_conditional_merge', term.args),
            'P36_update_if_to_cond_merge',
        ))

    # ── 7. dict_fromkeys ↔ dict_comprehension_keys ──
    if term.name == 'dict_fromkeys' and len(term.args) == 2:
        results.append((
            OOp('dict_comprehension_keys', term.args),
            'P36_fromkeys_to_comp',
        ))

    if term.name == 'dict_comprehension_keys' and len(term.args) == 2:
        results.append((
            OOp('dict_fromkeys', term.args),
            'P36_comp_to_fromkeys',
        ))

    # ── 8. dict_copy_update ↔ dict_new_merge ──
    if term.name == 'dict_copy_update' and len(term.args) == 2:
        results.append((
            OOp('dict_new_merge', term.args),
            'P36_copy_update_to_new',
        ))

    if term.name == 'dict_new_merge' and len(term.args) == 2:
        results.append((
            OOp('dict_copy_update', term.args),
            'P36_new_to_copy_update',
        ))

    # ── 9. dict_unpack_merge → dict_constructor_merge (transitive) ──
    if term.name == 'dict_unpack_merge' and len(term.args) == 2:
        results.append((
            OOp('dict_constructor_merge', term.args),
            'P36_unpack_to_constructor_direct',
        ))

    # ── 10. dict_copy_update → dict_pipe_merge (modern form) ──
    if term.name == 'dict_copy_update' and len(term.args) == 2:
        results.append((
            OOp('dict_pipe_merge', term.args),
            'P36_copy_update_to_pipe',
        ))

    # ── 11. chainmap single arg → identity ──
    if term.name == 'chainmap' and len(term.args) == 1:
        results.append((
            OOp('dict_merged', term.args),
            'P36_chainmap_single_to_dict',
        ))

    # ── 12. dict_pipe_merge → dict_new_merge (non-mutating alias) ──
    if term.name == 'dict_pipe_merge' and len(term.args) == 2:
        results.append((
            OOp('dict_new_merge', term.args),
            'P36_pipe_to_new_merge',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Return reverse rewrites (new-style → old-style dict merge)."""
    inverse_labels = {
        'P36_pipe_to_unpack', 'P36_ior_to_update',
        'P36_merged_to_chainmap', 'P36_unpack_to_constructor',
        'P36_if_to_setdefault', 'P36_update_if_to_cond_merge',
        'P36_comp_to_fromkeys', 'P36_new_to_copy_update',
    }
    return [(t, l) for t, l in apply(term, ctx) if l in inverse_labels]


def recognizes(term: OTerm) -> bool:
    """Return True if the term's root operator is a dict-merge op."""
    if isinstance(term, OOp) and term.name in _DICT_MERGE_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Heuristic relevance for search-guided rewriting."""
    sc, tc = source.canon(), target.canon()
    for kw in ('dict', 'merge', 'update', 'chainmap', 'unpack',
               'pipe', 'setdefault', 'fromkeys'):
        if kw in sc and kw in tc:
            return 0.9
    if ('unpack' in sc and 'pipe' in tc) or \
       ('pipe' in sc and 'unpack' in tc):
        return 0.85
    if ('update' in sc and 'ior' in tc) or \
       ('ior' in sc and 'update' in tc):
        return 0.85
    if ('chainmap' in sc and 'merge' in tc) or \
       ('merge' in sc and 'chainmap' in tc):
        return 0.8
    if any(k in sc for k in ('dict', 'merge', 'update', 'chainmap')):
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

    # 1. dict_unpack_merge → dict_pipe_merge
    t = OOp('dict_unpack_merge', (OVar('a'), OVar('b')))
    r = apply(t)
    _assert(any(l == 'P36_unpack_to_pipe' for _, l in r),
            "unpack → pipe")

    # 2. dict_pipe_merge → dict_unpack_merge
    t2 = OOp('dict_pipe_merge', (OVar('a'), OVar('b')))
    r2 = apply(t2)
    _assert(any(l == 'P36_pipe_to_unpack' for _, l in r2),
            "pipe → unpack")

    # 3. dict_update → dict_ior
    t3 = OOp('dict_update', (OVar('d'), OVar('b')))
    r3 = apply(t3)
    _assert(any(l == 'P36_update_to_ior' for _, l in r3),
            "update → ior")

    # 4. dict_ior → dict_update
    t4 = OOp('dict_ior', (OVar('d'), OVar('b')))
    r4 = apply(t4)
    _assert(any(l == 'P36_ior_to_update' for _, l in r4),
            "ior → update")

    # 5. chainmap → dict_merged
    t5 = OOp('chainmap', (OVar('b'), OVar('a')))
    r5 = apply(t5)
    _assert(any(l == 'P36_chainmap_to_merged' for _, l in r5),
            "chainmap → merged")

    # 6. dict_merged → chainmap
    t6 = OOp('dict_merged', (OVar('a'), OVar('b')))
    r6 = apply(t6)
    _assert(any(l == 'P36_merged_to_chainmap' for _, l in r6),
            "merged → chainmap")

    # 7. dict_constructor_merge → dict_unpack_merge_alt
    t7 = OOp('dict_constructor_merge', (OVar('a'), OVar('b')))
    r7 = apply(t7)
    _assert(any(l == 'P36_constructor_to_unpack' for _, l in r7),
            "constructor → unpack")

    # 8. dict_unpack_merge_alt → dict_constructor_merge
    t8 = OOp('dict_unpack_merge_alt', (OVar('a'), OVar('b')))
    r8 = apply(t8)
    _assert(any(l == 'P36_unpack_to_constructor' for _, l in r8),
            "unpack_alt → constructor")

    # 9. dict_setdefault → dict_if_not_in
    t9 = OOp('dict_setdefault', (OVar('d'), OVar('k'), OLit(0)))
    r9 = apply(t9)
    _assert(any(l == 'P36_setdefault_to_if' for _, l in r9),
            "setdefault → if_not_in")

    # 10. dict_if_not_in → dict_setdefault
    t10 = OOp('dict_if_not_in', (OVar('d'), OVar('k'), OLit(0)))
    r10 = apply(t10)
    _assert(any(l == 'P36_if_to_setdefault' for _, l in r10),
            "if_not_in → setdefault")

    # 11. dict_conditional_merge → dict_update_if
    t11 = OOp('dict_conditional_merge', (OVar('d'), OVar('k'), OVar('v')))
    r11 = apply(t11)
    _assert(any(l == 'P36_cond_merge_to_update_if' for _, l in r11),
            "cond_merge → update_if")

    # 12. dict_update_if → dict_conditional_merge
    t12 = OOp('dict_update_if', (OVar('d'), OVar('k'), OVar('v')))
    r12 = apply(t12)
    _assert(any(l == 'P36_update_if_to_cond_merge' for _, l in r12),
            "update_if → cond_merge")

    # 13. dict_fromkeys → dict_comprehension_keys
    t13 = OOp('dict_fromkeys', (OVar('keys'), OLit(0)))
    r13 = apply(t13)
    _assert(any(l == 'P36_fromkeys_to_comp' for _, l in r13),
            "fromkeys → comp")

    # 14. dict_comprehension_keys → dict_fromkeys
    t14 = OOp('dict_comprehension_keys', (OVar('keys'), OLit(0)))
    r14 = apply(t14)
    _assert(any(l == 'P36_comp_to_fromkeys' for _, l in r14),
            "comp → fromkeys")

    # 15. dict_copy_update → dict_new_merge
    t15 = OOp('dict_copy_update', (OVar('d'), OVar('b')))
    r15 = apply(t15)
    _assert(any(l == 'P36_copy_update_to_new' for _, l in r15),
            "copy_update → new_merge")

    # 16. dict_new_merge → dict_copy_update
    t16 = OOp('dict_new_merge', (OVar('d'), OVar('b')))
    r16 = apply(t16)
    _assert(any(l == 'P36_new_to_copy_update' for _, l in r16),
            "new_merge → copy_update")

    # 17. dict_unpack_merge → dict_constructor_merge (transitive)
    _assert(any(l == 'P36_unpack_to_constructor_direct' for _, l in r),
            "unpack → constructor (transitive)")

    # 18. dict_copy_update → dict_pipe_merge (modern)
    _assert(any(l == 'P36_copy_update_to_pipe' for _, l in r15),
            "copy_update → pipe")

    # 19. chainmap single → dict identity
    t19 = OOp('chainmap', (OVar('a'),))
    r19 = apply(t19)
    _assert(any(l == 'P36_chainmap_single_to_dict' for _, l in r19),
            "chainmap(a) → dict(a)")

    # 20. dict_pipe_merge → dict_new_merge
    _assert(any(l == 'P36_pipe_to_new_merge' for _, l in r2),
            "pipe → new_merge")

    # 21. inverse: dict_pipe_merge → dict_unpack_merge
    r21_inv = apply_inverse(OOp('dict_pipe_merge', (OVar('a'), OVar('b'))))
    _assert(any(l == 'P36_pipe_to_unpack' for _, l in r21_inv),
            "inv: pipe → unpack")

    # 22. inverse: dict_ior → dict_update
    r22_inv = apply_inverse(OOp('dict_ior', (OVar('d'), OVar('b'))))
    _assert(any(l == 'P36_ior_to_update' for _, l in r22_inv),
            "inv: ior → update")

    # 23. recognizes dict merge ops
    _assert(recognizes(OOp('dict_unpack_merge', (OVar('a'), OVar('b')))),
            "recognizes dict_unpack_merge")
    _assert(recognizes(OOp('dict_pipe_merge', (OVar('a'), OVar('b')))),
            "recognizes dict_pipe_merge")
    _assert(recognizes(OOp('chainmap', (OVar('a'), OVar('b')))),
            "recognizes chainmap")
    _assert(not recognizes(OLit(42)), "!recognizes literal")
    _assert(not recognizes(OVar('x')), "!recognizes var")

    # 24. relevance: dict ↔ merge high
    _assert(relevance_score(
        OOp('dict_unpack_merge', (OVar('a'), OVar('b'))),
        OOp('dict_pipe_merge', (OVar('a'), OVar('b'))),
    ) > 0.7, "dict merge relevance high")

    # 25. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2,
            "unrelated relevance low")

    print(f"P36 dict_merge: {_pass} passed, {_fail} failed")
