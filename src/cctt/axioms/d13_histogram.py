"""D13: Histogram / Counter Equivalences (Theorem 21.5.1).

Counter(xs) ↔ fold-based counting ↔ manual dict accumulation.

Mathematical foundation:
  A histogram is a morphism  h: Free(X) → ℕ^X  in the category of
  commutative monoids.  All Python representations (Counter, defaultdict,
  manual loop) compute the same morphism — they differ only in the
  carrier object used to represent ℕ^X.

  The equivalence is witnessed by a natural isomorphism in the
  presheaf category: Counter ≅ fold[count_freq] ≅ manual_dict_incr.

Covers:
  • Counter(xs) ↔ fold[count_freq](defaultdict(int), xs)
  • Counter.most_common(k) ↔ sorted(items, key=count, reverse=True)[:k]
  • Counter arithmetic (addition, subtraction)
  • defaultdict(int) accumulation ↔ Counter
  • Manual ``for x in xs: d[x] = d.get(x,0)+1`` pattern
  • Histogram normalisation variants
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

AXIOM_NAME = 'D13_histogram'
AXIOM_CATEGORY = 'data_structure'  # §21 — Data-structure dichotomies

SOUNDNESS_PROOF = """
Theorem 21.5.1 (Histogram Fold Equivalence):
  For any iterable xs: X*,
    Counter(xs)  ≡  fold(λ(d, x). d[x] ← d[x]+1, {}, xs)
  as morphisms Free(X) → ℕ^X in CMon.

Proof sketch:
  1. Counter(xs) is defined as the frequency map  x ↦ |{i : xs[i]=x}|.
  2. fold[count_freq]({}, xs) computes the same map by induction on |xs|:
     - Base: fold({}, []) = {} = Counter([])  ✓
     - Step: fold(d, xs++[x]) = d[x ← d[x]+1] = Counter(xs++[x])  ✓
  3. defaultdict(int) and manual d.get(x,0)+1 are implementation details
     of the same fold body.  ∎

Counter arithmetic:
  Counter(a) + Counter(b) = Counter(a ++ b)
  by the universal property of the free commutative monoid.
"""

COMPOSES_WITH = ['D19_sort', 'FOLD_extended', 'D14_indexing']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'Counter to fold',
        'before': "Counter(xs)",
        'after': "fold[count_freq](defaultdict(int), xs)",
        'axiom': 'D13_counter_to_fold',
    },
    {
        'name': 'fold to Counter',
        'before': "fold[count_freq](defaultdict(int), xs)",
        'after': "Counter(xs)",
        'axiom': 'D13_fold_to_counter',
    },
    {
        'name': 'most_common to sorted slice',
        'before': "Counter(xs).most_common(k)",
        'after': "sorted(Counter(xs).items(), key=λp.p[1], reverse=True)[:k]",
        'axiom': 'D13_most_common_to_sorted_slice',
    },
    {
        'name': 'Counter addition',
        'before': "Counter(a) + Counter(b)",
        'after': "Counter(a ++ b)",
        'axiom': 'D13_counter_add',
    },
    {
        'name': 'Manual dict to Counter',
        'before': "fold[dict_incr]({}, xs)",
        'after': "Counter(xs)",
        'axiom': 'D13_manual_dict_to_counter',
    },
]


# ═══════════════════════════════════════════════════════════
# Helper: extract params for fiber-awareness
# ═══════════════════════════════════════════════════════════

@dataclass
class FiberCtx:
    """Lightweight fiber context for standalone axiom evaluation."""
    param_duck_types: Dict[str, str] = field(default_factory=dict)


def _extract_free_vars(term: OTerm) -> Set[str]:
    """All free variable names in *term*."""
    if isinstance(term, OVar):
        return {term.name}
    if isinstance(term, OLit) or isinstance(term, OUnknown):
        return set()
    if isinstance(term, OOp):
        r: Set[str] = set()
        for a in term.args:
            r |= _extract_free_vars(a)
        return r
    if isinstance(term, OFold):
        return _extract_free_vars(term.init) | _extract_free_vars(term.collection)
    if isinstance(term, OCase):
        return (
            _extract_free_vars(term.test)
            | _extract_free_vars(term.true_branch)
            | _extract_free_vars(term.false_branch)
        )
    if isinstance(term, OFix):
        return _extract_free_vars(term.body)
    if isinstance(term, OLam):
        return _extract_free_vars(term.body) - set(term.params)
    if isinstance(term, OSeq):
        r2: Set[str] = set()
        for e in term.elements:
            r2 |= _extract_free_vars(e)
        return r2
    if isinstance(term, OMap):
        r3 = _extract_free_vars(term.transform) | _extract_free_vars(term.collection)
        if term.filter_pred:
            r3 |= _extract_free_vars(term.filter_pred)
        return r3
    if isinstance(term, OQuotient):
        return _extract_free_vars(term.inner)
    if isinstance(term, ODict):
        r4: Set[str] = set()
        for k, v in term.pairs:
            r4 |= _extract_free_vars(k) | _extract_free_vars(v)
        return r4
    if isinstance(term, OCatch):
        return _extract_free_vars(term.body) | _extract_free_vars(term.default)
    if isinstance(term, OAbstract):
        r5: Set[str] = set()
        for a in term.inputs:
            r5 |= _extract_free_vars(a)
        return r5
    return set()


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D13 histogram equivalences to *term*.

    Returns list of (rewritten_term, axiom_label) pairs.
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── Counter(xs) → fold[count_freq](defaultdict(int), xs) ──
    if isinstance(term, OOp) and term.name in ('Counter', 'collections.Counter'):
        if len(term.args) == 1:
            results.append((
                OFold('count_freq', OOp('defaultdict', (OLit(0),)), term.args[0]),
                'D13_counter_to_fold',
            ))

    # ── fold[count_freq](...) → Counter(xs) ──
    if isinstance(term, OFold) and term.op_name in ('count_freq', 'freq_count'):
        if isinstance(term.init, OOp) and term.init.name == 'defaultdict':
            results.append((
                OOp('Counter', (term.collection,)),
                'D13_fold_to_counter',
            ))

    # ── Counter.most_common(k) → sorted slice ──
    if isinstance(term, OOp) and term.name == 'most_common':
        if len(term.args) == 2:
            counter_term, k = term.args
            sorted_items = OOp('sorted_key_rev', (
                OOp('.items', (counter_term,)),
                OLam(('p',), OOp('getitem', (OVar('p'), OLit(1)))),
            ))
            sliced = OOp('getitem', (sorted_items, OOp('slice', (OLit(None), k))))
            results.append((sliced, 'D13_most_common_to_sorted_slice'))

    # ── sorted slice → Counter.most_common(k) (reverse) ──
    if isinstance(term, OOp) and term.name == 'getitem':
        if len(term.args) == 2 and isinstance(term.args[0], OOp):
            outer = term.args[0]
            if outer.name in ('sorted', 'sorted_key_rev'):
                if len(outer.args) >= 1 and isinstance(outer.args[0], OOp):
                    if outer.args[0].name == '.items':
                        counter_src = (
                            outer.args[0].args[0]
                            if outer.args[0].args else None
                        )
                        if counter_src is not None and isinstance(term.args[1], OOp):
                            if (term.args[1].name == 'slice'
                                    and len(term.args[1].args) == 2):
                                k = term.args[1].args[1]
                                results.append((
                                    OOp('most_common', (counter_src, k)),
                                    'D13_sorted_slice_to_most_common',
                                ))

    # ── Counter addition: Counter(a) + Counter(b) → Counter(a ++ b) ──
    if isinstance(term, OOp) and term.name == 'add' and len(term.args) == 2:
        lhs, rhs = term.args
        if (_is_counter(lhs) and _is_counter(rhs)):
            la = _counter_arg(lhs)
            ra = _counter_arg(rhs)
            if la is not None and ra is not None:
                results.append((
                    OOp('Counter', (OOp('concat', (la, ra)),)),
                    'D13_counter_add',
                ))

    # ── Counter subtraction ──
    if isinstance(term, OOp) and term.name == 'sub' and len(term.args) == 2:
        lhs, rhs = term.args
        if _is_counter(lhs) and _is_counter(rhs):
            results.append((
                OOp('counter_subtract', (lhs, rhs)),
                'D13_counter_sub',
            ))

    # ── Manual dict accumulation → Counter ──
    if isinstance(term, OFold) and term.op_name in (
        'dict_incr', 'setdefault_add', 'dict_get_incr',
    ):
        if isinstance(term.init, ODict) and len(term.init.pairs) == 0:
            results.append((
                OOp('Counter', (term.collection,)),
                'D13_manual_dict_to_counter',
            ))
        elif isinstance(term.init, OOp) and term.init.name == 'defaultdict':
            results.append((
                OOp('Counter', (term.collection,)),
                'D13_defaultdict_to_counter',
            ))

    # ── defaultdict(int) comprehension → Counter ──
    if isinstance(term, OOp) and term.name == 'defaultdict' and len(term.args) == 1:
        if isinstance(term.args[0], OLit) and term.args[0].value in (0, 'int'):
            # A standalone defaultdict(int) construction — mark as counter-compatible
            results.append((
                OOp('Counter', (OSeq(()),)),
                'D13_defaultdict_int_to_empty_counter',
            ))

    # ── Counter intersection: Counter(a) & Counter(b) ──
    if isinstance(term, OOp) and term.name == 'bitand' and len(term.args) == 2:
        lhs, rhs = term.args
        if _is_counter(lhs) and _is_counter(rhs):
            results.append((
                OOp('counter_intersection', (lhs, rhs)),
                'D13_counter_intersection',
            ))

    # ── Counter union: Counter(a) | Counter(b) ──
    if isinstance(term, OOp) and term.name == 'bitor' and len(term.args) == 2:
        lhs, rhs = term.args
        if _is_counter(lhs) and _is_counter(rhs):
            results.append((
                OOp('counter_union', (lhs, rhs)),
                'D13_counter_union',
            ))

    return results


def _is_counter(term: OTerm) -> bool:
    """Check if term is a Counter(...) construction."""
    return isinstance(term, OOp) and term.name in ('Counter', 'collections.Counter')


def _counter_arg(term: OTerm) -> Optional[OTerm]:
    """Extract the argument from Counter(arg)."""
    if isinstance(term, OOp) and term.name in ('Counter', 'collections.Counter'):
        return term.args[0] if len(term.args) == 1 else None
    return None


# ═══════════════════════════════════════════════════════════
# Inverse axiom
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D13 in reverse: fold-based → Counter, etc.

    Inverse rewrites are already embedded in apply() as bidirectional
    rules; this function filters for only the reverse direction.
    """
    results = apply(term, ctx)
    inverse_labels = {
        'D13_fold_to_counter',
        'D13_sorted_slice_to_most_common',
        'D13_manual_dict_to_counter',
        'D13_defaultdict_to_counter',
        'D13_defaultdict_int_to_empty_counter',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D13 is potentially applicable to *term*."""
    if isinstance(term, OOp):
        if term.name in ('Counter', 'collections.Counter', 'most_common',
                         'defaultdict', 'counter_subtract',
                         'counter_intersection', 'counter_union'):
            return True
        if term.name in ('add', 'sub', 'bitand', 'bitor') and len(term.args) == 2:
            return _is_counter(term.args[0]) or _is_counter(term.args[1])
        if term.name == 'getitem':
            return _has_items_sorted_pattern(term)
    if isinstance(term, OFold):
        if term.op_name in ('count_freq', 'freq_count', 'dict_incr',
                            'setdefault_add', 'dict_get_incr'):
            return True
    return False


def _has_items_sorted_pattern(term: OTerm) -> bool:
    """Check for sorted(counter.items())[:k] pattern."""
    if not isinstance(term, OOp) or term.name != 'getitem':
        return False
    if len(term.args) < 2 or not isinstance(term.args[0], OOp):
        return False
    outer = term.args[0]
    if outer.name not in ('sorted', 'sorted_key_rev'):
        return False
    if len(outer.args) >= 1 and isinstance(outer.args[0], OOp):
        return outer.args[0].name == '.items'
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score how relevant D13 is for bridging *source* → *target*.

    Returns a float in [0, 1].
    """
    sc = source.canon()
    tc = target.canon()

    has_counter_s = 'Counter(' in sc or 'collections.Counter(' in sc
    has_counter_t = 'Counter(' in tc or 'collections.Counter(' in tc
    has_fold_s = 'fold[count_freq]' in sc or 'fold[freq_count]' in sc
    has_fold_t = 'fold[count_freq]' in tc or 'fold[freq_count]' in tc
    has_dict_s = 'dict_incr' in sc or 'defaultdict(' in sc
    has_dict_t = 'dict_incr' in tc or 'defaultdict(' in tc

    # One side Counter, other side fold/dict → high relevance
    if (has_counter_s and (has_fold_t or has_dict_t)):
        return 0.95
    if (has_counter_t and (has_fold_s or has_dict_s)):
        return 0.95

    # Both Counter or both fold → moderate (normalisation)
    if has_counter_s != has_counter_t:
        return 0.85
    if has_fold_s != has_fold_t:
        return 0.80

    # most_common pattern
    if 'most_common' in sc or 'most_common' in tc:
        return 0.75

    # Generic histogram signals
    if has_counter_s or has_counter_t:
        return 0.40

    return 0.05


# ═══════════════════════════════════════════════════════════
# Histogram normalisation variants
# ═══════════════════════════════════════════════════════════

def histogram_normalisation_variants(
    xs: Optional[OTerm] = None,
) -> List[Tuple[str, OTerm]]:
    """Enumerate the three canonical histogram representations.

    All three are provably equal via D13.
    """
    if xs is None:
        xs = OVar('xs')
    counter_form = OOp('Counter', (xs,))
    defaultdict_form = OFold(
        'count_freq', OOp('defaultdict', (OLit(0),)), xs,
    )
    manual_form = OFold('dict_incr', ODict(()), xs)
    return [
        ('Counter', counter_form),
        ('defaultdict', defaultdict_form),
        ('manual_dict', manual_form),
    ]


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

    # ── Counter → fold ──
    print("D13: Counter → fold ...")
    counter_term = OOp('Counter', (xs,))
    r = apply(counter_term, ctx)
    _assert(len(r) >= 1, "Counter(xs) should rewrite")
    _assert(r[0][1] == 'D13_counter_to_fold', "axiom label")
    _assert(isinstance(r[0][0], OFold), "result is OFold")

    # ── fold → Counter ──
    print("D13: fold → Counter ...")
    fold_term = OFold('count_freq', OOp('defaultdict', (OLit(0),)), xs)
    r2 = apply(fold_term, ctx)
    _assert(any(lbl == 'D13_fold_to_counter' for _, lbl in r2), "fold→Counter")

    # ── Roundtrip ──
    print("D13: roundtrip ...")
    rt = apply(r[0][0], ctx)
    _assert(any(lbl == 'D13_fold_to_counter' for _, lbl in rt), "roundtrip works")

    # ── most_common ──
    print("D13: most_common ...")
    mc = OOp('most_common', (counter_term, OLit(3)))
    r3 = apply(mc, ctx)
    _assert(len(r3) >= 1, "most_common rewrites")
    _assert(r3[0][1] == 'D13_most_common_to_sorted_slice', "most_common label")

    # ── Counter addition ──
    print("D13: Counter addition ...")
    add_term = OOp('add', (OOp('Counter', (OVar('a'),)),
                           OOp('Counter', (OVar('b'),))))
    r4 = apply(add_term, ctx)
    _assert(any(lbl == 'D13_counter_add' for _, lbl in r4), "Counter add")

    # ── Counter subtraction ──
    print("D13: Counter subtraction ...")
    sub_term = OOp('sub', (OOp('Counter', (OVar('a'),)),
                           OOp('Counter', (OVar('b'),))))
    r5 = apply(sub_term, ctx)
    _assert(any(lbl == 'D13_counter_sub' for _, lbl in r5), "Counter sub")

    # ── Manual dict → Counter ──
    print("D13: manual dict → Counter ...")
    manual = OFold('dict_incr', ODict(()), xs)
    r6 = apply(manual, ctx)
    _assert(any(lbl == 'D13_manual_dict_to_counter' for _, lbl in r6), "manual→Counter")

    # ── recognizes() ──
    print("D13: recognizes ...")
    _assert(recognizes(counter_term), "recognizes Counter")
    _assert(recognizes(fold_term), "recognizes fold")
    _assert(recognizes(manual), "recognizes manual dict")
    _assert(not recognizes(OOp('sorted', (xs,))), "does not recognise sorted")

    # ── relevance_score ──
    print("D13: relevance_score ...")
    score = relevance_score(counter_term, fold_term)
    _assert(score > 0.8, f"Counter↔fold score={score:.2f} > 0.8")
    low = relevance_score(OOp('sorted', (xs,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── histogram variants ──
    print("D13: histogram variants ...")
    variants = histogram_normalisation_variants()
    _assert(len(variants) == 3, "three variants")

    # ── apply_inverse ──
    print("D13: apply_inverse ...")
    inv = apply_inverse(fold_term, ctx)
    _assert(len(inv) >= 1, "inverse of fold produces Counter")

    # ── Counter intersection ──
    print("D13: Counter intersection ...")
    inter_term = OOp('bitand', (OOp('Counter', (OVar('a'),)),
                                OOp('Counter', (OVar('b'),))))
    r7 = apply(inter_term, ctx)
    _assert(any(lbl == 'D13_counter_intersection' for _, lbl in r7), "Counter &")

    # ── Counter union ──
    print("D13: Counter union ...")
    union_term = OOp('bitor', (OOp('Counter', (OVar('a'),)),
                               OOp('Counter', (OVar('b'),))))
    r8 = apply(union_term, ctx)
    _assert(any(lbl == 'D13_counter_union' for _, lbl in r8), "Counter |")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  D13 histogram: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
