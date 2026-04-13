"""Quotient Type Rewrite Axioms — OQuotient Normalisation.

Quotient types model equivalence classes where certain distinctions
are irrelevant.  The main equivalence class is 'perm' (permutation
group), used for sets and dicts where iteration order is irrelevant.

Key rewrites:
  • Q[perm](sorted(x)) → sorted(x)        [sorted is canonical rep]
  • sorted(Q[perm](x)) → sorted(x)        [sorting absorbs quotient]
  • set(sorted(x)) → set(x)               [set discards order]
  • len(Q[perm](x)) → len(x)              [length ignores order]
  • Q[perm](Q[perm](x)) → Q[perm](x)     [idempotence]
  • Q[dup](set(x)) → set(x)              [set already deduplicates]
  • set(Q[perm](x)) → set(x)             [set absorbs quotient]
  • Q[perm](list(x)) → set(x)            [quotient list = set]
  • frozenset(x) → Q[perm](x)            [frozenset is perm-quotient]
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "QUOT_quotient"
AXIOM_CATEGORY = "utility"

SOUNDNESS_PROOF = """
Quotient types form a coequaliser in the presheaf category.
Q[perm](x) = x / ~_perm  where x ~_perm y iff x is a permutation of y.

sorted(x) picks a canonical representative of each equivalence class,
so Q[perm](sorted(x)) = sorted(x) (the quotient is trivial when
a canonical rep is already chosen).

Idempotence: Q[perm](Q[perm](x)) = Q[perm](x) because quotienting
an already-quotiented type doesn't create new identifications.

set() is the terminal quotient: set(x) = Q[perm](Q[dup](x)).
"""

COMPOSES_WITH = ["D19_sort_scan", "FOLD", "D23_sort_process"]
REQUIRES: List[str] = []

EXAMPLES = [
    ("Q[perm](sorted(xs))", "sorted(xs)", "QUOT_sorted_canonical"),
    ("sorted(Q[perm](xs))", "sorted(xs)", "QUOT_sorted_absorb"),
    ("Q[perm](Q[perm](xs))", "Q[perm](xs)", "QUOT_idempotent"),
    ("set(Q[perm](xs))", "set(xs)", "QUOT_set_perm_absorb"),
    ("Q[dup](set(xs))", "set(xs)", "QUOT_dup_set_absorb"),
]


@dataclass
class FiberCtx:
    param_duck_types: Dict[str, str] = field(default_factory=dict)

    def is_numeric(self, term: OTerm) -> bool:
        return True


def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply quotient-type rewrite rules."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── 1. Q[perm](sorted(x)) → sorted(x)  [sorted is canonical rep] ──
    if isinstance(term, OQuotient) and term.equiv_class == 'perm':
        if isinstance(term.inner, OOp) and term.inner.name in ('sorted', 'stable_sort'):
            results.append((term.inner, 'QUOT_sorted_canonical'))

    # ── 2. sorted(Q[perm](x)) → sorted(x)  [sorting absorbs quotient] ──
    if isinstance(term, OOp) and term.name == 'sorted':
        if len(term.args) == 1 and isinstance(term.args[0], OQuotient):
            if term.args[0].equiv_class == 'perm':
                results.append((
                    OOp('sorted', (term.args[0].inner,)),
                    'QUOT_sorted_absorb',
                ))

    # ── 3. set(sorted(x)) → set(x)  [set discards order] ──
    if isinstance(term, OOp) and term.name == 'set':
        if len(term.args) == 1 and isinstance(term.args[0], OOp):
            if term.args[0].name in ('sorted', 'stable_sort', 'reversed'):
                results.append((
                    OOp('set', term.args[0].args),
                    'QUOT_set_sort_absorb',
                ))

    # ── 4. len(Q[perm](x)) → len(x)  [length ignores order] ──
    if isinstance(term, OOp) and term.name == 'len':
        if len(term.args) == 1 and isinstance(term.args[0], OQuotient):
            if term.args[0].equiv_class == 'perm':
                results.append((
                    OOp('len', (term.args[0].inner,)),
                    'QUOT_len_absorb',
                ))

    # ── 5. Q[perm](Q[perm](x)) → Q[perm](x)  [idempotence] ──
    if isinstance(term, OQuotient) and isinstance(term.inner, OQuotient):
        if term.equiv_class == term.inner.equiv_class:
            results.append((term.inner, 'QUOT_idempotent'))

    # ── 6. Q[dup](set(x)) → set(x)  [set already deduplicates] ──
    if isinstance(term, OQuotient) and term.equiv_class == 'dup':
        if isinstance(term.inner, OOp) and term.inner.name == 'set':
            results.append((term.inner, 'QUOT_dup_set_absorb'))

    # ── 7. set(Q[perm](x)) → set(x)  [set absorbs quotient] ──
    if isinstance(term, OOp) and term.name == 'set' and len(term.args) == 1:
        if isinstance(term.args[0], OQuotient) and term.args[0].equiv_class == 'perm':
            results.append((
                OOp('set', (term.args[0].inner,)),
                'QUOT_set_perm_absorb',
            ))

    # ── 8. frozenset(x) → Q[perm](set(x))  [frozenset normalisation] ──
    if isinstance(term, OOp) and term.name == 'frozenset' and len(term.args) >= 1:
        results.append((
            OQuotient(OOp('set', (term.args[0],)), 'perm'),
            'QUOT_frozenset_normalise',
        ))

    # ── 9. Q[perm](list(x)) → Q[perm](x)  [list is transparent to perm] ──
    if isinstance(term, OQuotient) and term.equiv_class == 'perm':
        if isinstance(term.inner, OOp) and term.inner.name == 'list':
            if len(term.inner.args) == 1:
                results.append((
                    OQuotient(term.inner.args[0], 'perm'),
                    'QUOT_perm_list_absorb',
                ))

    # ── 10. Q[comm](op(a,b)) → op(min(a,b), max(a,b))  [canonical rep] ──
    if isinstance(term, OQuotient) and term.equiv_class == 'comm':
        if isinstance(term.inner, OOp) and len(term.inner.args) == 2:
            a, b = term.inner.args
            canonical = OOp(term.inner.name, (
                OOp('min', (a, b)),
                OOp('max', (a, b)),
            ))
            results.append((canonical, 'QUOT_comm_canonical'))

    # ── 11. sum(Q[perm](x)) → sum(x)  [sum ignores order] ──
    if isinstance(term, OOp) and term.name in ('sum', 'prod', 'len', 'any', 'all'):
        if len(term.args) == 1 and isinstance(term.args[0], OQuotient):
            if term.args[0].equiv_class == 'perm':
                results.append((
                    OOp(term.name, (term.args[0].inner,)),
                    f'QUOT_{term.name}_perm_absorb',
                ))

    # ── 12. Q[idem](Q[perm](x)) → set(x)  [idempotent + perm = set] ──
    if isinstance(term, OQuotient) and term.equiv_class == 'idem':
        if isinstance(term.inner, OQuotient) and term.inner.equiv_class == 'perm':
            results.append((
                OOp('set', (term.inner.inner,)),
                'QUOT_idem_perm_to_set',
            ))

    # ── 13. Q[perm](Q[idem](x)) → set(x)  [perm + idempotent = set] ──
    if isinstance(term, OQuotient) and term.equiv_class == 'perm':
        if isinstance(term.inner, OQuotient) and term.inner.equiv_class == 'idem':
            results.append((
                OOp('set', (term.inner.inner,)),
                'QUOT_perm_idem_to_set',
            ))

    # ── 14. dict(Q[perm](x)) → dict(x) ──
    if isinstance(term, OOp) and term.name == 'dict' and len(term.args) == 1:
        if isinstance(term.args[0], OQuotient) and term.args[0].equiv_class == 'perm':
            results.append((
                OOp('dict', (term.args[0].inner,)),
                'QUOT_dict_perm_absorb',
            ))

    return results


def recognizes(term: OTerm) -> bool:
    """Return True if quotient axioms can potentially rewrite *term*."""
    if isinstance(term, OQuotient):
        return True
    if isinstance(term, OOp):
        if term.name in ('sorted', 'set', 'frozenset', 'len', 'sum',
                         'prod', 'any', 'all', 'dict'):
            if len(term.args) >= 1:
                if isinstance(term.args[0], OQuotient):
                    return True
                if isinstance(term.args[0], OOp) and term.args[0].name in ('sorted', 'reversed'):
                    return True
        if term.name == 'frozenset':
            return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score QUOT's relevance."""
    sc = source.canon()
    tc = target.canon()
    s_quot = 'Q[' in sc
    t_quot = 'Q[' in tc
    s_set = 'set(' in sc or 'frozenset(' in sc
    t_set = 'set(' in tc or 'frozenset(' in tc
    if s_quot or t_quot:
        return 0.7
    if s_set or t_set:
        return 0.3
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse: wrap terms in quotient types."""
    results: List[Tuple[OTerm, str]] = []

    # set(x) → Q[perm](x) when viewing set as quotient
    if isinstance(term, OOp) and term.name == 'set' and len(term.args) == 1:
        results.append((
            OQuotient(term.args[0], 'perm'),
            'QUOT_set_to_quotient',
        ))

    # sorted(x) → sorted(Q[perm](x))
    if isinstance(term, OOp) and term.name == 'sorted' and len(term.args) == 1:
        results.append((
            OOp('sorted', (OQuotient(term.args[0], 'perm'),)),
            'QUOT_inject_perm_sorted',
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

    # Q[perm](sorted(x)) → sorted(x)
    t1 = OQuotient(OOp('sorted', (xs,)), 'perm')
    r1 = apply(t1, ctx)
    _assert(any(a == 'QUOT_sorted_canonical' for _, a in r1), "sorted canonical")

    # sorted(Q[perm](x)) → sorted(x)
    t2 = OOp('sorted', (OQuotient(xs, 'perm'),))
    r2 = apply(t2, ctx)
    _assert(any(a == 'QUOT_sorted_absorb' for _, a in r2), "sorted absorb quotient")

    # set(sorted(x)) → set(x)
    t3 = OOp('set', (OOp('sorted', (xs,)),))
    r3 = apply(t3, ctx)
    _assert(any(a == 'QUOT_set_sort_absorb' for _, a in r3), "set sort absorb")

    # len(Q[perm](x)) → len(x)
    t4 = OOp('len', (OQuotient(xs, 'perm'),))
    r4 = apply(t4, ctx)
    _assert(any(a == 'QUOT_len_absorb' for _, a in r4), "len absorb")

    # Q[perm](Q[perm](x)) → Q[perm](x)
    t5 = OQuotient(OQuotient(xs, 'perm'), 'perm')
    r5 = apply(t5, ctx)
    _assert(any(a == 'QUOT_idempotent' for _, a in r5), "idempotent")

    # Q[dup](set(x)) → set(x)
    t6 = OQuotient(OOp('set', (xs,)), 'dup')
    r6 = apply(t6, ctx)
    _assert(any(a == 'QUOT_dup_set_absorb' for _, a in r6), "dup set absorb")

    # set(Q[perm](x)) → set(x)
    t7 = OOp('set', (OQuotient(xs, 'perm'),))
    r7 = apply(t7, ctx)
    _assert(any(a == 'QUOT_set_perm_absorb' for _, a in r7), "set perm absorb")

    # frozenset normalisation
    t8 = OOp('frozenset', (xs,))
    r8 = apply(t8, ctx)
    _assert(any(a == 'QUOT_frozenset_normalise' for _, a in r8), "frozenset normalise")

    # Q[perm](list(x)) → Q[perm](x)
    t9 = OQuotient(OOp('list', (xs,)), 'perm')
    r9 = apply(t9, ctx)
    _assert(any(a == 'QUOT_perm_list_absorb' for _, a in r9), "perm list absorb")

    # sum(Q[perm](x)) → sum(x)
    t10 = OOp('sum', (OQuotient(xs, 'perm'),))
    r10 = apply(t10, ctx)
    _assert(any(a == 'QUOT_sum_perm_absorb' for _, a in r10), "sum perm absorb")

    # Q[idem](Q[perm](x)) → set(x)
    t11 = OQuotient(OQuotient(xs, 'perm'), 'idem')
    r11 = apply(t11, ctx)
    _assert(any(a == 'QUOT_idem_perm_to_set' for _, a in r11), "idem+perm → set")

    # recognizes
    _assert(recognizes(t1), "recognizes quotient")
    _assert(recognizes(t8), "recognizes frozenset")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # inverse
    t12 = OOp('set', (xs,))
    r12 = apply_inverse(t12, ctx)
    _assert(any(a == 'QUOT_set_to_quotient' for _, a in r12), "set → quotient inverse")

    print(f"QUOT quotient: {_pass} passed, {_fail} failed")
