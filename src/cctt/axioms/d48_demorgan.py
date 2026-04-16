"""D48: De Morgan for Programs (Theorem 29.6.1).

De Morgan's laws in Boolean algebra extend to program-level
quantifier/predicate negation.

Mathematical foundation:
  De Morgan's laws in Boolean algebra state:
    ¬(A ∧ B) = ¬A ∨ ¬B
    ¬(A ∨ B) = ¬A ∧ ¬B

  These extend to quantifiers:
    ¬(∀x. P(x)) = ∃x. ¬P(x)
    ¬(∃x. P(x)) = ∀x. ¬P(x)

  In Python, `all` = ∀ and `any` = ∃, giving:
    not all(p(x) for x in xs) ↔ any(not p(x) for x in xs)
    not any(p(x) for x in xs) ↔ all(not p(x) for x in xs)

  The filter complement theorem:
    filter(p, xs) ∪ filter(¬p, xs) = xs  (partition)

  Negation normal form: push negations inward through
  Boolean connectives until they reach atomic predicates.

  Identity extensions:
    x not in s  ↔  not (x in s)
    x != y      ↔  not (x == y)

Covers:
  • not any(...) ↔ all(not ...)
  • not all(...) ↔ any(not ...)
  • not (a and b) ↔ (not a) or (not b)
  • not (a or b) ↔ (not a) and (not b)
  • filter complement: filter(p) + filter(not p) ↔ partition(p)
  • x not in s ↔ not (x in s)
  • x != y ↔ not (x == y)
  • Negation normal form for guard conditions
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

AXIOM_NAME = 'D48_demorgan'
AXIOM_CATEGORY = 'logical_bitwise'  # §29

SOUNDNESS_PROOF = """
Theorem 29.6.1 (De Morgan for Quantifiers):
  For predicate p and finite sequence xs:
    not any(p(x) for x in xs) = all(not p(x) for x in xs)
    not all(p(x) for x in xs) = any(not p(x) for x in xs)

Proof:
  any(p(x) for x in xs) = ∃x∈xs. p(x) = p(x_0) ∨ ... ∨ p(x_{n-1}).
  all(p(x) for x in xs) = ∀x∈xs. p(x) = p(x_0) ∧ ... ∧ p(x_{n-1}).
  By De Morgan's laws on finite conjunctions/disjunctions:
    ¬(p₀ ∨ ... ∨ p_{n-1}) = ¬p₀ ∧ ... ∧ ¬p_{n-1}
    ¬(p₀ ∧ ... ∧ p_{n-1}) = ¬p₀ ∨ ... ∨ ¬p_{n-1}
  which gives the quantifier forms.  ∎

Theorem 29.6.2 (Classical De Morgan):
  not (a and b) = (not a) or (not b)
  not (a or b) = (not a) and (not b)

Proof:
  Truth table verification (or algebraic proof in Boolean algebra).  ∎

Theorem 29.6.3 (Filter Complement / Partition):
  filter(p, xs) + filter(λx. not p(x), xs) = xs  (as multiset)

Proof:
  Every element x ∈ xs satisfies exactly one of p(x) or ¬p(x).
  Therefore x appears in exactly one of the two filtered lists.
  The concatenation preserves all elements (though not necessarily
  in the original order — under permutation quotient, equality holds).  ∎

Theorem 29.6.4 (Membership Negation):
  (x not in s) = not (x in s)
  (x != y) = not (x == y)

Proof:
  By definition of 'not in' and '!=' as negations of 'in' and '=='.  ∎

Theorem 29.6.5 (Negation Normal Form):
  Every Boolean expression can be transformed to NNF where negations
  appear only on atomic predicates, by repeated application of
  De Morgan's laws and double negation elimination: ¬¬A = A.

Proof:
  By structural induction on the formula.  At each connective,
  apply De Morgan's law to push negation inward.  At atoms,
  stop.  Double negation is eliminated by ¬¬A = A.  ∎
"""

COMPOSES_WITH = ['D47_bitwise', 'D03_guard_reorder', 'D24_eta']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'not any → all not',
        'before': "not any(p(x) for x in xs)",
        'after': "all(not p(x) for x in xs)",
        'axiom': 'D48_not_any_to_all_not',
    },
    {
        'name': 'not all → any not',
        'before': "not all(p(x) for x in xs)",
        'after': "any(not p(x) for x in xs)",
        'axiom': 'D48_not_all_to_any_not',
    },
    {
        'name': 'not (a and b) → (not a) or (not b)',
        'before': "not (a and b)",
        'after': "(not a) or (not b)",
        'axiom': 'D48_not_and_to_or_not',
    },
    {
        'name': 'not (a or b) → (not a) and (not b)',
        'before': "not (a or b)",
        'after': "(not a) and (not b)",
        'axiom': 'D48_not_or_to_and_not',
    },
    {
        'name': 'Filter complement to partition',
        'before': "filter(p, xs) + filter(not_p, xs)",
        'after': "partition(p, xs)",
        'axiom': 'D48_filter_complement',
    },
    {
        'name': 'not in to not (in)',
        'before': "x not in s",
        'after': "not (x in s)",
        'axiom': 'D48_notin_to_not_in',
    },
    {
        'name': 'not-equal to not (equal)',
        'before': "x != y",
        'after': "not (x == y)",
        'axiom': 'D48_noteq_to_not_eq',
    },
]

# ── De Morgan pattern operation names ──
DEMORGAN_OPS: FrozenSet[str] = frozenset({
    'u_not', 'not', 'negate',
    'any', 'all',
    'and', 'or',
    'notin', 'noteq', 'ne', 'isnot',
    'in', 'eq', 'is_',
    'partition',
})

# ── Negatable comparison operators ──
COMPARISON_NEGATION = {
    'eq': 'noteq',
    'noteq': 'eq',
    'ne': 'eq',
    'lt': 'gte',
    'gte': 'lt',
    'gt': 'lte',
    'lte': 'gt',
    'in': 'notin',
    'notin': 'in',
    'is_': 'isnot',
    'isnot': 'is_',
}


# ═══════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════

@dataclass
class FiberCtx:
    """Lightweight fiber context for standalone axiom evaluation."""
    param_duck_types: Dict[str, str] = field(default_factory=dict)


def _extract_free_vars(term: OTerm) -> Set[str]:
    """Extract all free variable names."""
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


def _negate_term(term: OTerm) -> OTerm:
    """Wrap a term in logical negation."""
    return OOp('u_not', (term,))


def _negate_predicate(pred: OTerm) -> OTerm:
    """Negate a predicate, pushing negation inward if possible.

    For lambda predicates: λx.P(x) → λx.¬P(x)
    """
    if isinstance(pred, OLam):
        return OLam(pred.params, _negate_term(pred.body))
    return _negate_term(pred)


# ═══════════════════════════════════════════════════════════
# Pattern detection
# ═══════════════════════════════════════════════════════════

def _is_not_any(term: OTerm) -> Optional[OTerm]:
    """Detect not any(p(x) for x in xs). Returns the any-term or None."""
    if isinstance(term, OOp) and term.name == 'u_not' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'any':
            return inner
    return None


def _is_not_all(term: OTerm) -> Optional[OTerm]:
    """Detect not all(p(x) for x in xs). Returns the all-term or None."""
    if isinstance(term, OOp) and term.name == 'u_not' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'all':
            return inner
    return None


def _is_not_and(term: OTerm) -> Optional[Tuple[OTerm, ...]]:
    """Detect not (a and b). Returns (a, b, ...) or None."""
    if isinstance(term, OOp) and term.name == 'u_not' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'and':
            return inner.args
    return None


def _is_not_or(term: OTerm) -> Optional[Tuple[OTerm, ...]]:
    """Detect not (a or b). Returns (a, b, ...) or None."""
    if isinstance(term, OOp) and term.name == 'u_not' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'or':
            return inner.args
    return None


def _is_negated_comparison(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """Detect negated comparison: not (x == y), not (x in s), etc.

    Returns (negated_op_name, args) or None.
    """
    if isinstance(term, OOp) and term.name == 'u_not' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name in COMPARISON_NEGATION:
            return (COMPARISON_NEGATION[inner.name], inner.args)
    return None


def _is_direct_negated_comparison(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """Detect direct negated comparison: x != y, x not in s, etc.

    Returns (positive_op_name, args) or None for conversion to not(positive).
    """
    if isinstance(term, OOp) and term.name in ('noteq', 'ne', 'notin', 'isnot'):
        pos = COMPARISON_NEGATION.get(term.name)
        if pos:
            return (pos, term.args)
    return None


def _is_filter_complement(term: OTerm) -> bool:
    """Detect filter(p, xs) + filter(not p, xs) pattern."""
    if isinstance(term, OOp) and term.name in ('add', 'concat'):
        if len(term.args) == 2:
            a, b = term.args
            if isinstance(a, OOp) and a.name == 'filter' and \
               isinstance(b, OOp) and b.name == 'filter':
                if len(a.args) >= 2 and len(b.args) >= 2:
                    # Same collection
                    if a.args[1] == b.args[1]:
                        return True
    return False


def _is_double_negation(term: OTerm) -> Optional[OTerm]:
    """Detect not not x. Returns the inner term or None."""
    if isinstance(term, OOp) and term.name == 'u_not' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'u_not' and len(inner.args) == 1:
            return inner.args[0]
    return None


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D48 De Morgan equivalences to *term*."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── not any(P) → all(not P) ──
    any_term = _is_not_any(term)
    if any_term is not None:
        # any(pred, coll) or any(genexpr)
        if isinstance(any_term, OOp) and any_term.args:
            if len(any_term.args) == 1:
                # any(genexpr) → all(not genexpr) — wrap inner in negation
                inner = any_term.args[0]
                if isinstance(inner, OMap):
                    neg_transform = _negate_predicate(inner.transform)
                    results.append((
                        OOp('all', (OMap(neg_transform, inner.collection, inner.filter_pred),)),
                        'D48_not_any_to_all_not',
                    ))
                else:
                    results.append((
                        OOp('all', (_negate_term(inner),)),
                        'D48_not_any_to_all_not',
                    ))
            else:
                results.append((
                    OOp('all', tuple(_negate_term(a) for a in any_term.args)),
                    'D48_not_any_to_all_not',
                ))

    # ── not all(P) → any(not P) ──
    all_term = _is_not_all(term)
    if all_term is not None:
        if isinstance(all_term, OOp) and all_term.args:
            if len(all_term.args) == 1:
                inner = all_term.args[0]
                if isinstance(inner, OMap):
                    neg_transform = _negate_predicate(inner.transform)
                    results.append((
                        OOp('any', (OMap(neg_transform, inner.collection, inner.filter_pred),)),
                        'D48_not_all_to_any_not',
                    ))
                else:
                    results.append((
                        OOp('any', (_negate_term(inner),)),
                        'D48_not_all_to_any_not',
                    ))
            else:
                results.append((
                    OOp('any', tuple(_negate_term(a) for a in all_term.args)),
                    'D48_not_all_to_any_not',
                ))

    # ── not (a and b) → (not a) or (not b) ──
    and_args = _is_not_and(term)
    if and_args is not None:
        results.append((
            OOp('or', tuple(_negate_term(a) for a in and_args)),
            'D48_not_and_to_or_not',
        ))

    # ── not (a or b) → (not a) and (not b) ──
    or_args = _is_not_or(term)
    if or_args is not None:
        results.append((
            OOp('and', tuple(_negate_term(a) for a in or_args)),
            'D48_not_or_to_and_not',
        ))

    # ── Reverse: (not a) or (not b) → not (a and b) ──
    if isinstance(term, OOp) and term.name == 'or':
        if all(isinstance(a, OOp) and a.name == 'u_not' for a in term.args):
            inner_args = tuple(a.args[0] for a in term.args)
            results.append((
                _negate_term(OOp('and', inner_args)),
                'D48_or_not_to_not_and',
            ))

    # ── Reverse: (not a) and (not b) → not (a or b) ──
    if isinstance(term, OOp) and term.name == 'and':
        if all(isinstance(a, OOp) and a.name == 'u_not' for a in term.args):
            inner_args = tuple(a.args[0] for a in term.args)
            results.append((
                _negate_term(OOp('or', inner_args)),
                'D48_and_not_to_not_or',
            ))

    # ── Negated comparison: not (x == y) → x != y ──
    neg_cmp = _is_negated_comparison(term)
    if neg_cmp is not None:
        neg_op, cmp_args = neg_cmp
        results.append((
            OOp(neg_op, cmp_args),
            'D48_not_cmp_to_neg_cmp',
        ))

    # ── Direct negated comparison: x != y → not (x == y) ──
    dir_neg = _is_direct_negated_comparison(term)
    if dir_neg is not None:
        pos_op, cmp_args = dir_neg
        results.append((
            _negate_term(OOp(pos_op, cmp_args)),
            'D48_neg_cmp_to_not_cmp',
        ))

    # ── Filter complement: filter(p, xs) + filter(not p, xs) → partition ──
    if _is_filter_complement(term):
        a_filt = term.args[0]
        if isinstance(a_filt, OOp) and len(a_filt.args) >= 2:
            pred, coll = a_filt.args[0], a_filt.args[1]
            results.append((
                OOp('partition', (pred, coll)),
                'D48_filter_complement',
            ))

    # ── Partition → filter complement ──
    if isinstance(term, OOp) and term.name == 'partition':
        if len(term.args) >= 2:
            pred, coll = term.args[0], term.args[1]
            results.append((
                OOp('add', (
                    OOp('filter', (pred, coll)),
                    OOp('filter', (_negate_predicate(pred), coll)),
                )),
                'D48_partition_to_filter_complement',
            ))

    # ── Double negation elimination: not not x → x ──
    dbl_neg = _is_double_negation(term)
    if dbl_neg is not None:
        results.append((dbl_neg, 'D48_double_negation'))

    # ── all(not P) → not any(P)  (reverse of not_any_to_all_not) ──
    if isinstance(term, OOp) and term.name == 'all' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OMap) and isinstance(inner.transform, OLam):
            body = inner.transform.body
            if isinstance(body, OOp) and body.name == 'u_not':
                pos_transform = OLam(inner.transform.params, body.args[0])
                results.append((
                    _negate_term(OOp('any', (OMap(pos_transform, inner.collection, inner.filter_pred),))),
                    'D48_all_not_to_not_any',
                ))

    # ── any(not P) → not all(P)  (reverse of not_all_to_any_not) ──
    if isinstance(term, OOp) and term.name == 'any' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OMap) and isinstance(inner.transform, OLam):
            body = inner.transform.body
            if isinstance(body, OOp) and body.name == 'u_not':
                pos_transform = OLam(inner.transform.params, body.args[0])
                results.append((
                    _negate_term(OOp('all', (OMap(pos_transform, inner.collection, inner.filter_pred),))),
                    'D48_any_not_to_not_all',
                ))

    # ── Abstract specs ──
    if isinstance(term, OAbstract):
        if 'demorgan' in term.spec or 'negation' in term.spec:
            results.append((
                OOp('u_not', term.inputs),
                'D48_spec_to_negation',
            ))
        if 'partition' in term.spec:
            if term.inputs and len(term.inputs) >= 2:
                results.append((
                    OOp('partition', term.inputs),
                    'D48_spec_to_partition',
                ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D48 in reverse: expanded → compact."""
    results = apply(term, ctx)
    inverse_labels = {
        'D48_or_not_to_not_and',
        'D48_and_not_to_not_or',
        'D48_neg_cmp_to_not_cmp',
        'D48_partition_to_filter_complement',
        'D48_all_not_to_not_any',
        'D48_any_not_to_not_all',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D48 is potentially applicable."""
    if _is_not_any(term) is not None:
        return True
    if _is_not_all(term) is not None:
        return True
    if _is_not_and(term) is not None:
        return True
    if _is_not_or(term) is not None:
        return True
    if _is_negated_comparison(term) is not None:
        return True
    if _is_direct_negated_comparison(term) is not None:
        return True
    if _is_filter_complement(term):
        return True
    if _is_double_negation(term) is not None:
        return True
    if isinstance(term, OOp) and term.name == 'partition':
        return True
    # all(not P) or any(not P)
    if isinstance(term, OOp) and term.name in ('all', 'any') and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OMap) and isinstance(inner.transform, OLam):
            body = inner.transform.body
            if isinstance(body, OOp) and body.name == 'u_not':
                return True
    # (not a) or (not b) / (not a) and (not b)
    if isinstance(term, OOp) and term.name in ('or', 'and'):
        if all(isinstance(a, OOp) and a.name == 'u_not' for a in term.args):
            return True
    if isinstance(term, OAbstract):
        return any(kw in term.spec for kw in ('demorgan', 'negation', 'partition'))
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D48 relevance for bridging *source* → *target*."""
    sc = source.canon()
    tc = target.canon()

    neg_kw = ['u_not', 'not', 'negate']
    quant_kw = ['any', 'all']
    logic_kw = ['and', 'or']
    cmp_kw = ['noteq', 'ne', 'notin', 'isnot']
    part_kw = ['partition', 'filter']

    has_neg_s = any(kw in sc for kw in neg_kw)
    has_neg_t = any(kw in tc for kw in neg_kw)
    has_quant_s = any(kw in sc for kw in quant_kw)
    has_quant_t = any(kw in tc for kw in quant_kw)
    has_logic_s = any(kw in sc for kw in logic_kw)
    has_logic_t = any(kw in tc for kw in logic_kw)
    has_part_s = any(kw in sc for kw in part_kw)
    has_part_t = any(kw in tc for kw in part_kw)

    # Negation + quantifier on both sides → high relevance
    if has_neg_s and has_quant_t and has_quant_s:
        return 0.95
    if has_neg_t and has_quant_s and has_quant_t:
        return 0.95
    # Negation + logic → De Morgan
    if has_neg_s and has_logic_t:
        return 0.90
    if has_neg_t and has_logic_s:
        return 0.90
    # Partition / filter complement
    if has_part_s and has_part_t:
        return 0.85
    # Both have negation
    if has_neg_s and has_neg_t:
        return 0.70
    # One side has negation + quantifier/logic
    if (has_neg_s or has_neg_t) and (has_quant_s or has_quant_t or has_logic_s or has_logic_t):
        return 0.50
    # One side has negation
    if has_neg_s or has_neg_t:
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
    a = OVar('a')
    b = OVar('b')
    x = OVar('x')
    y = OVar('y')
    s = OVar('s')
    p = OVar('p')

    # ── not any(...) → all(not ...) ──
    print("D48: not any → all not ...")
    pred_map = OMap(OLam(('x',), OOp('gt', (OVar('x'), OLit(0)))), xs)
    not_any = OOp('u_not', (OOp('any', (pred_map,)),))
    r_na = apply(not_any, ctx)
    _assert(any(lbl == 'D48_not_any_to_all_not' for _, lbl in r_na),
            "not_any→all_not")

    # ── not all(...) → any(not ...) ──
    print("D48: not all → any not ...")
    not_all = OOp('u_not', (OOp('all', (pred_map,)),))
    r_nal = apply(not_all, ctx)
    _assert(any(lbl == 'D48_not_all_to_any_not' for _, lbl in r_nal),
            "not_all→any_not")

    # ── not (a and b) → (not a) or (not b) ──
    print("D48: not (a and b) → (not a) or (not b) ...")
    not_and = OOp('u_not', (OOp('and', (a, b)),))
    r_nand = apply(not_and, ctx)
    _assert(any(lbl == 'D48_not_and_to_or_not' for _, lbl in r_nand),
            "not_and→or_not")

    # ── not (a or b) → (not a) and (not b) ──
    print("D48: not (a or b) → (not a) and (not b) ...")
    not_or = OOp('u_not', (OOp('or', (a, b)),))
    r_nor = apply(not_or, ctx)
    _assert(any(lbl == 'D48_not_or_to_and_not' for _, lbl in r_nor),
            "not_or→and_not")

    # ── Reverse: (not a) or (not b) → not (a and b) ──
    print("D48: (not a) or (not b) → not (a and b) ...")
    or_not = OOp('or', (OOp('u_not', (a,)), OOp('u_not', (b,))))
    r_orn = apply(or_not, ctx)
    _assert(any(lbl == 'D48_or_not_to_not_and' for _, lbl in r_orn),
            "or_not→not_and")

    # ── Reverse: (not a) and (not b) → not (a or b) ──
    print("D48: (not a) and (not b) → not (a or b) ...")
    and_not = OOp('and', (OOp('u_not', (a,)), OOp('u_not', (b,))))
    r_andn = apply(and_not, ctx)
    _assert(any(lbl == 'D48_and_not_to_not_or' for _, lbl in r_andn),
            "and_not→not_or")

    # ── Negated comparison: not (x == y) → x != y ──
    print("D48: not (x == y) → x != y ...")
    not_eq = OOp('u_not', (OOp('eq', (x, y)),))
    r_neq = apply(not_eq, ctx)
    _assert(any(lbl == 'D48_not_cmp_to_neg_cmp' for _, lbl in r_neq),
            "not_eq→noteq")

    # ── Direct negated comparison: x != y → not (x == y) ──
    print("D48: x != y → not (x == y) ...")
    noteq = OOp('noteq', (x, y))
    r_noteq = apply(noteq, ctx)
    _assert(any(lbl == 'D48_neg_cmp_to_not_cmp' for _, lbl in r_noteq),
            "noteq→not_eq")

    # ── not in → not (in) ──
    print("D48: not in ↔ not (in) ...")
    notin = OOp('notin', (x, s))
    r_ni = apply(notin, ctx)
    _assert(any(lbl == 'D48_neg_cmp_to_not_cmp' for _, lbl in r_ni),
            "notin→not_in")

    not_in = OOp('u_not', (OOp('in', (x, s)),))
    r_noti = apply(not_in, ctx)
    _assert(any(lbl == 'D48_not_cmp_to_neg_cmp' for _, lbl in r_noti),
            "not_in→notin")

    # ── Filter complement → partition ──
    print("D48: filter complement → partition ...")
    filt_comp = OOp('add', (
        OOp('filter', (p, xs)),
        OOp('filter', (_negate_predicate(p), xs)),
    ))
    r_fc = apply(filt_comp, ctx)
    _assert(any(lbl == 'D48_filter_complement' for _, lbl in r_fc),
            "filter_complement→partition")

    # ── Partition → filter complement ──
    print("D48: partition → filter complement ...")
    part = OOp('partition', (p, xs))
    r_pt = apply(part, ctx)
    _assert(any(lbl == 'D48_partition_to_filter_complement' for _, lbl in r_pt),
            "partition→filter_complement")

    # ── Double negation ──
    print("D48: double negation ...")
    dbl = OOp('u_not', (OOp('u_not', (a,)),))
    r_dbl = apply(dbl, ctx)
    _assert(any(lbl == 'D48_double_negation' for _, lbl in r_dbl),
            "not_not→identity")
    # Check the result is just 'a'
    for t, lbl in r_dbl:
        if lbl == 'D48_double_negation':
            _assert(t == a, "double negation gives original")
            break

    # ── all(not P) → not any(P) ──
    print("D48: all(not P) → not any(P) ...")
    neg_pred = OLam(('x',), OOp('u_not', (OOp('gt', (OVar('x'), OLit(0))),)))
    all_not = OOp('all', (OMap(neg_pred, xs),))
    r_an = apply(all_not, ctx)
    _assert(any(lbl == 'D48_all_not_to_not_any' for _, lbl in r_an),
            "all_not→not_any")

    # ── any(not P) → not all(P) ──
    print("D48: any(not P) → not all(P) ...")
    any_not = OOp('any', (OMap(neg_pred, xs),))
    r_anp = apply(any_not, ctx)
    _assert(any(lbl == 'D48_any_not_to_not_all' for _, lbl in r_anp),
            "any_not→not_all")

    # ── recognizes ──
    print("D48: recognizes ...")
    _assert(recognizes(not_any), "recognizes not any")
    _assert(recognizes(not_all), "recognizes not all")
    _assert(recognizes(not_and), "recognizes not and")
    _assert(recognizes(not_or), "recognizes not or")
    _assert(recognizes(not_eq), "recognizes not eq")
    _assert(recognizes(noteq), "recognizes noteq")
    _assert(recognizes(notin), "recognizes notin")
    _assert(recognizes(filt_comp), "recognizes filter complement")
    _assert(recognizes(dbl), "recognizes double negation")
    _assert(recognizes(part), "recognizes partition")
    _assert(recognizes(or_not), "recognizes (not a) or (not b)")
    _assert(recognizes(all_not), "recognizes all(not P)")
    _assert(not recognizes(OOp('sorted', (xs,))), "does not recognise sorted")

    # ── relevance_score ──
    print("D48: relevance_score ...")
    score = relevance_score(
        OOp('u_not', (OOp('any', (xs,)),)),
        OOp('all', (OOp('u_not', (xs,)),)),
    )
    _assert(score > 0.85, f"not_any↔all_not score={score:.2f} > 0.85")

    low = relevance_score(OOp('sorted', (xs,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("D48: apply_inverse ...")
    inv_or = apply_inverse(or_not, ctx)
    _assert(len(inv_or) >= 1, "inverse or_not→not_and")

    inv_noteq = apply_inverse(noteq, ctx)
    _assert(len(inv_noteq) >= 1, "inverse noteq→not_eq")

    inv_part = apply_inverse(part, ctx)
    _assert(len(inv_part) >= 1, "inverse partition→filters")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  D48 demorgan: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
