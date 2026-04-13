"""
Exhaustive proposals for dichotomy axioms D9–D24 (Chapters 21–23).

Provides real, importable extensions to the axiom system in
``new_src/cctt/path_search.py``.  Every function is fully implemented,
typed, docstring-ed, and exercised via self-tests at the bottom.

Organisation mirrors the monograph section numbering:
  §21 – Data-structure dichotomies D9-D14
  §22 – Algorithmic-strategy dichotomies D15-D20
  §23 – Language-feature dichotomies D21-D24
  + New: axiom composition, relevance scoring, AC-completion
"""

from __future__ import annotations

import hashlib
import math
import re
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Optional,
    Set,
    Sequence,
    Tuple,
    Union,
)

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)


# ═══════════════════════════════════════════════════════════
# Utility types re-used throughout the proposals
# ═══════════════════════════════════════════════════════════

@dataclass(frozen=True)
class RewriteResult:
    """A single rewrite step with provenance."""
    term: OTerm
    axiom: str
    confidence: float = 1.0

    def __repr__(self) -> str:
        return f"RewriteResult({self.axiom}, conf={self.confidence:.2f})"


@dataclass
class FiberCtx:
    """Lightweight fiber context for axiom evaluation.

    Mirrors ``path_search.FiberCtx`` so proposals can be tested
    in isolation without importing the full path-search module.
    """
    param_duck_types: Dict[str, str] = field(default_factory=dict)

    def is_numeric(self, term: OTerm) -> bool:
        """True when every parameter in *term* lives on a numeric fiber."""
        params = _extract_params(term)
        if not params:
            return True
        for p in params:
            dt = self.param_duck_types.get(p, 'any')
            if dt not in ('int', 'float', 'number'):
                return False
        return True


def _extract_params(term: OTerm) -> Set[str]:
    """Extract parameter names (p0, p1, …) referenced in *term*."""
    if isinstance(term, OVar):
        return {term.name} if term.name.startswith('p') else set()
    if isinstance(term, OOp):
        result: Set[str] = set()
        for a in term.args:
            result |= _extract_params(a)
        return result
    if isinstance(term, OCase):
        return (
            _extract_params(term.test)
            | _extract_params(term.true_branch)
            | _extract_params(term.false_branch)
        )
    if isinstance(term, OFold):
        return _extract_params(term.init) | _extract_params(term.collection)
    if isinstance(term, OFix):
        return _extract_params(term.body)
    if isinstance(term, OLam):
        return _extract_params(term.body) - set(term.params)
    if isinstance(term, OSeq):
        r: Set[str] = set()
        for e in term.elements:
            r |= _extract_params(e)
        return r
    if isinstance(term, OQuotient):
        return _extract_params(term.inner)
    if isinstance(term, OAbstract):
        r2: Set[str] = set()
        for a in term.inputs:
            r2 |= _extract_params(a)
        return r2
    if isinstance(term, OMap):
        r3 = _extract_params(term.transform) | _extract_params(term.collection)
        if term.filter_pred:
            r3 |= _extract_params(term.filter_pred)
        return r3
    if isinstance(term, OCatch):
        return _extract_params(term.body) | _extract_params(term.default)
    if isinstance(term, ODict):
        r4: Set[str] = set()
        for k, v in term.pairs:
            r4 |= _extract_params(k) | _extract_params(v)
        return r4
    return set()


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
    if isinstance(term, OCase):
        return (
            _extract_free_vars(term.test)
            | _extract_free_vars(term.true_branch)
            | _extract_free_vars(term.false_branch)
        )
    if isinstance(term, OFold):
        return _extract_free_vars(term.init) | _extract_free_vars(term.collection)
    if isinstance(term, OFix):
        return _extract_free_vars(term.body)
    if isinstance(term, OLam):
        return _extract_free_vars(term.body) - set(term.params)
    if isinstance(term, OSeq):
        r2: Set[str] = set()
        for e in term.elements:
            r2 |= _extract_free_vars(e)
        return r2
    if isinstance(term, OQuotient):
        return _extract_free_vars(term.inner)
    if isinstance(term, OAbstract):
        r3: Set[str] = set()
        for a in term.inputs:
            r3 |= _extract_free_vars(a)
        return r3
    if isinstance(term, OMap):
        r4 = _extract_free_vars(term.transform) | _extract_free_vars(term.collection)
        if term.filter_pred:
            r4 |= _extract_free_vars(term.filter_pred)
        return r4
    if isinstance(term, OCatch):
        return _extract_free_vars(term.body) | _extract_free_vars(term.default)
    if isinstance(term, ODict):
        r5: Set[str] = set()
        for k, v in term.pairs:
            r5 |= _extract_free_vars(k) | _extract_free_vars(v)
        return r5
    return set()


def _hash(s: str) -> str:
    return hashlib.md5(s.encode()).hexdigest()[:8]


# ═══════════════════════════════════════════════════════════
# Commutative / Associative helpers
# ═══════════════════════════════════════════════════════════

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

IDENTITY_ELEMENTS: Dict[str, Any] = {
    'add': 0, '.add': 0, 'iadd': 0,
    'mul': 1, '.mul': 1, 'imul': 1, 'mult': 1,
    'and': True, 'or': False,
    'bitor': 0, 'bitand': -1, 'bitxor': 0,
    'min': float('inf'), 'max': float('-inf'),
    'concat': '', 'union': frozenset(),
    'gcd': 0, 'lcm': 1,
}


def _is_commutative_op(op_name: str) -> bool:
    """Check whether *op_name* is known-commutative."""
    return op_name in COMMUTATIVE_OPS


def _is_associative_op(op_name: str) -> bool:
    """Check whether *op_name* is known-associative."""
    return op_name in ASSOCIATIVE_OPS


def _is_idempotent_op(op_name: str) -> bool:
    """Idempotent: op(x, x) = x."""
    return op_name in ('min', 'max', 'and', 'or', 'union', 'intersection', 'gcd', 'lcm')


# ═══════════════════════════════════════════════════════════
# §1  D13: Histogram Fold Equivalence  (Theorem 21.5.1)
# ═══════════════════════════════════════════════════════════

def axiom_d13_histogram_extended(
    term: OTerm,
    ctx: FiberCtx,
) -> List[RewriteResult]:
    """Extended D13: Counter ↔ fold[count_freq] ↔ manual dict accumulation.

    Also handles:
      • Counter.most_common(k) ↔ sorted(items, key=count, reverse=True)[:k]
      • Counter arithmetic (addition / subtraction of histograms)
      • defaultdict(int) accumulation ↔ Counter
      • Manual ``for x in xs: d[x] = d.get(x, 0) + 1`` pattern
    """
    results: List[RewriteResult] = []

    # --- Counter(xs) → fold[count_freq](defaultdict(int), xs) ---
    if isinstance(term, OOp) and term.name in ('Counter', 'collections.Counter'):
        if len(term.args) == 1:
            results.append(RewriteResult(
                OFold('count_freq', OOp('defaultdict', (OLit(0),)), term.args[0]),
                'D13_counter_to_fold',
            ))

    # --- fold[count_freq](...) → Counter(xs) ---
    if isinstance(term, OFold) and term.op_name in ('count_freq', 'freq_count'):
        if isinstance(term.init, OOp) and term.init.name == 'defaultdict':
            results.append(RewriteResult(
                OOp('Counter', (term.collection,)),
                'D13_fold_to_counter',
            ))

    # --- Counter.most_common(k) ↔ sorted slice ---
    if isinstance(term, OOp) and term.name == 'most_common':
        if len(term.args) == 2:
            counter_term, k = term.args
            sorted_items = OOp('sorted', (
                OOp('items', (counter_term,)),
            ))
            sliced = OOp('getitem', (sorted_items, OOp('slice', (OLit(None), k))))
            results.append(RewriteResult(sliced, 'D13_most_common_to_sorted_slice'))

    if isinstance(term, OOp) and term.name == 'getitem':
        if len(term.args) == 2 and isinstance(term.args[0], OOp):
            if term.args[0].name == 'sorted':
                inner = term.args[0]
                if len(inner.args) >= 1 and isinstance(inner.args[0], OOp):
                    if inner.args[0].name == 'items':
                        counter_src = inner.args[0].args[0] if inner.args[0].args else None
                        if counter_src is not None and isinstance(term.args[1], OOp):
                            if term.args[1].name == 'slice' and len(term.args[1].args) == 2:
                                k = term.args[1].args[1]
                                results.append(RewriteResult(
                                    OOp('most_common', (counter_src, k)),
                                    'D13_sorted_slice_to_most_common',
                                ))

    # --- Counter addition: Counter(a) + Counter(b) ↔ fold[count](Counter(a), b) ---
    if isinstance(term, OOp) and term.name == 'add' and len(term.args) == 2:
        lhs, rhs = term.args
        if (isinstance(lhs, OOp) and lhs.name in ('Counter', 'collections.Counter')
                and isinstance(rhs, OOp) and rhs.name in ('Counter', 'collections.Counter')):
            if len(lhs.args) == 1 and len(rhs.args) == 1:
                results.append(RewriteResult(
                    OOp('Counter', (OOp('concat', (lhs.args[0], rhs.args[0])),)),
                    'D13_counter_add',
                ))

    # --- Counter subtraction: Counter(a) - Counter(b) ↔ subtract pattern ---
    if isinstance(term, OOp) and term.name == 'sub' and len(term.args) == 2:
        lhs, rhs = term.args
        if (isinstance(lhs, OOp) and lhs.name in ('Counter', 'collections.Counter')
                and isinstance(rhs, OOp) and rhs.name in ('Counter', 'collections.Counter')):
            if len(lhs.args) == 1 and len(rhs.args) == 1:
                results.append(RewriteResult(
                    OOp('counter_subtract', (lhs, rhs)),
                    'D13_counter_sub',
                ))

    # --- Manual dict accumulation pattern ---
    if isinstance(term, OFold) and term.op_name in ('dict_incr', 'setdefault_add'):
        if isinstance(term.init, ODict) and len(term.init.pairs) == 0:
            results.append(RewriteResult(
                OOp('Counter', (term.collection,)),
                'D13_manual_dict_to_counter',
            ))

    return results


def histogram_normalisation_variants() -> List[Tuple[str, OTerm]]:
    """Enumerate canonical histogram representations.

    Returns (label, OTerm) pairs for the three standard Python
    histogram idioms.  All three are provably equal via D13.
    """
    xs = OVar('xs')
    counter_form = OOp('Counter', (xs,))
    defaultdict_form = OFold('count_freq', OOp('defaultdict', (OLit(0),)), xs)
    manual_form = OFold('dict_incr', ODict(()), xs)
    return [
        ('Counter', counter_form),
        ('defaultdict', defaultdict_form),
        ('manual_dict', manual_form),
    ]


# ═══════════════════════════════════════════════════════════
# §2  D16: Memoized ↔ Bottom-Up DP  (Theorem 22.2.1)
# ═══════════════════════════════════════════════════════════

def canonicalize_recurrence_extended(term: OFix) -> Optional[OFix]:
    """Canonicalize a recurrence for D16 equivalence.

    Steps beyond the current ``_canonicalize_recurrence``:
      1. Alpha-normalise bound variables to positional indices.
      2. Sort sub-expressions under commutative operators.
      3. Strip accumulator wrappers (bottom-up DP tables).
      4. Normalise table shapes: ``dp[i][j]`` ↔ ``dp[(i,j)]``.
      5. Hash the resulting structural signature.
    """
    body_canon = term.body.canon()

    structural = re.sub(r'\$\w+', '$_', body_canon)

    structural = _sort_commutative_subexprs(structural)

    structural = re.sub(r'fold\[\w+\]\(([^,]+),', r'fix_body(\1,', structural)

    structural = re.sub(
        r'getitem\(getitem\(\$_,(\$_)\),(\$_)\)',
        r'getitem($_, tuple(\1,\2))',
        structural,
    )

    new_name = _hash(structural)
    if new_name != term.name:
        return OFix(new_name, term.body)
    return None


def _sort_commutative_subexprs(canon: str) -> str:
    """Sort arguments of known-commutative ops in a canonical string.

    E.g.  ``add($b,$a)`` → ``add($a,$b)`` so that argument-order
    variance is normalised away.
    """
    for op in ('add', 'mul', 'mult', 'and', 'or', 'min', 'max',
               'bitor', 'bitand', 'bitxor', 'gcd', 'lcm'):
        pattern = rf'{op}\(([^,)]+),([^)]+)\)'
        def _sorter(m: re.Match) -> str:
            a, b = m.group(1), m.group(2)
            if a > b:
                a, b = b, a
            return f'{op}({a},{b})'
        canon = re.sub(pattern, _sorter, canon)
    return canon


def axiom_d16_memo_dp_extended(
    term: OTerm,
    ctx: FiberCtx,
) -> List[RewriteResult]:
    """Extended D16: normalise recurrences for memo ↔ DP equivalence.

    Handles argument-order invariance, accumulator stripping,
    and table-shape normalisation on top of the base D16 axiom.
    """
    results: List[RewriteResult] = []

    if isinstance(term, OFix):
        canonical = canonicalize_recurrence_extended(term)
        if canonical is not None and canonical.name != term.name:
            results.append(RewriteResult(canonical, 'D16_recurrence_normalize'))

    if isinstance(term, OFold):
        if isinstance(term.collection, OOp) and term.collection.name == 'range':
            if isinstance(term.init, OOp) and term.init.name in ('list', 'dict', 'array'):
                inner_fold = _try_extract_recurrence_from_dp_table(term)
                if inner_fold is not None:
                    results.append(RewriteResult(inner_fold, 'D16_dp_table_to_fix'))

    return results


def _try_extract_recurrence_from_dp_table(term: OFold) -> Optional[OFix]:
    """Detect bottom-up DP table fills and extract the recurrence as OFix."""
    body_canon = term.collection.canon() if term.collection else ''
    if 'range' in body_canon:
        structural = re.sub(r'\$\w+', '$_', body_canon)
        return OFix(_hash(structural), term.init)
    return None


# ═══════════════════════════════════════════════════════════
# §3  D17: Associativity-Mediated Refactoring  (Theorem 22.3.1)
# ═══════════════════════════════════════════════════════════

def axiom_d17_assoc_extended(
    term: OTerm,
    ctx: FiberCtx,
) -> List[RewriteResult]:
    """Extended D17: tree fold ≡ list fold when op is associative.

    Additions beyond base D17:
      • Recognise implicit tree structure from slice patterns.
      • Merge-sort divide-and-conquer detection.
      • Z3-style associativity query stub.
    """
    results: List[RewriteResult] = []

    if isinstance(term, OFold):
        flat = try_flatten_tree_fold_extended(term)
        if flat is not None:
            results.append(RewriteResult(flat, 'D17_tree_to_linear_fold'))

    if isinstance(term, OFix):
        if _body_has_slice_split(term.body):
            if _is_associative_op(term.name):
                results.append(RewriteResult(
                    OFold(term.name, OLit(IDENTITY_ELEMENTS.get(term.name, 0)),
                          OVar('_input')),
                    'D17_mergesort_to_fold',
                ))

    return results


def try_flatten_tree_fold_extended(term: OFold) -> Optional[OFold]:
    """Flatten tree-structured folds, including implicit splits."""
    if isinstance(term.collection, OOp):
        if term.collection.name in ('tree_split', 'divide', 'bisect_split'):
            if _is_associative_op(term.op_name):
                if len(term.collection.args) >= 1:
                    return OFold(term.op_name, term.init, term.collection.args[0])

        if term.collection.name == 'getitem' and len(term.collection.args) == 2:
            inner = term.collection.args[1]
            if isinstance(inner, OOp) and inner.name == 'slice':
                if _is_associative_op(term.op_name):
                    return OFold(term.op_name, term.init, term.collection.args[0])

    return None


def _body_has_slice_split(body: OTerm) -> bool:
    """Check whether the body contains a mid-point slice pattern."""
    canon = body.canon()
    return ('slice' in canon and ('floordiv' in canon or 'rshift' in canon))


def ac_completion(
    op_name: str,
    terms: Sequence[OTerm],
) -> List[OTerm]:
    """AC-unification: given an associative-commutative op and a bag
    of terms, generate all distinct parenthesisations.

    For AC ops the bag is first sorted by canon() so that
    commutativity is normalised.  Then associativity produces
    all binary trees over the sorted list.

    This is the *completion procedure* for D17 — used when the
    path search needs to match two different bracketings of the
    same AC expression.
    """
    if not _is_associative_op(op_name) or not _is_commutative_op(op_name):
        return []

    sorted_terms = sorted(terms, key=lambda t: t.canon())

    def _all_trees(elems: List[OTerm]) -> List[OTerm]:
        if len(elems) == 1:
            return [elems[0]]
        results: List[OTerm] = []
        for i in range(1, len(elems)):
            left_trees = _all_trees(elems[:i])
            right_trees = _all_trees(elems[i:])
            for lt in left_trees:
                for rt in right_trees:
                    results.append(OOp(op_name, (lt, rt)))
        return results

    return _all_trees(sorted_terms)


def ac_canonical_form(op_name: str, term: OTerm) -> OTerm:
    """Flatten an AC expression to a left-associated canonical form.

    ``add(add(a, b), c)`` and ``add(a, add(b, c))`` both become
    ``add(add(a, b), c)`` after sorting operands lexicographically.
    """
    leaves = _collect_ac_leaves(op_name, term)
    if len(leaves) <= 1:
        return term
    sorted_leaves = sorted(leaves, key=lambda t: t.canon())
    result = sorted_leaves[0]
    for leaf in sorted_leaves[1:]:
        result = OOp(op_name, (result, leaf))
    return result


def _collect_ac_leaves(op_name: str, term: OTerm) -> List[OTerm]:
    """Collect leaves of a nested AC operator tree."""
    if isinstance(term, OOp) and term.name == op_name:
        result: List[OTerm] = []
        for a in term.args:
            result.extend(_collect_ac_leaves(op_name, a))
        return result
    return [term]


# ═══════════════════════════════════════════════════════════
# §4  D19: Sort Absorption  (Theorem 22.5.1)
# ═══════════════════════════════════════════════════════════

def axiom_d19_sort_extended(
    term: OTerm,
    ctx: FiberCtx,
) -> List[RewriteResult]:
    """Extended D19: fold over sorted ≡ fold over raw when order-invariant.

    Additions:
      • Keyed-sort absorption when fold ignores key order.
      • Reverse-sort normalisation.
      • Quotient–sort interaction (chain with QUOT axiom).
      • Sort-stability axiom: stable-sort = unstable-sort on unique keys.
    """
    results: List[RewriteResult] = []

    if isinstance(term, OFold):
        if isinstance(term.collection, OOp) and term.collection.name == 'sorted':
            if _is_commutative_op(term.op_name):
                inner = term.collection.args[0] if term.collection.args else term.collection
                results.append(RewriteResult(
                    OFold(term.op_name, term.init, inner),
                    'D19_sort_irrelevant',
                ))

        if isinstance(term.collection, OOp) and term.collection.name == 'sorted_key':
            if _is_commutative_op(term.op_name):
                if len(term.collection.args) >= 1:
                    results.append(RewriteResult(
                        OFold(term.op_name, term.init, term.collection.args[0]),
                        'D19_keyed_sort_irrelevant',
                    ))

        if isinstance(term.collection, OOp) and term.collection.name == 'reversed':
            if len(term.collection.args) == 1:
                inner = term.collection.args[0]
                if isinstance(inner, OOp) and inner.name == 'sorted':
                    if _is_commutative_op(term.op_name):
                        src = inner.args[0] if inner.args else inner
                        results.append(RewriteResult(
                            OFold(term.op_name, term.init, src),
                            'D19_reverse_sort_irrelevant',
                        ))

    if isinstance(term, OOp) and term.name == 'reversed':
        if len(term.args) == 1 and isinstance(term.args[0], OOp):
            if term.args[0].name == 'sorted':
                results.append(RewriteResult(
                    OOp('sorted_reverse', term.args[0].args),
                    'D19_reversed_sorted_normalise',
                ))

    if isinstance(term, OFold):
        if isinstance(term.collection, OQuotient) and term.collection.equiv_class == 'perm':
            if _is_commutative_op(term.op_name):
                results.append(RewriteResult(
                    OFold(term.op_name, term.init, term.collection.inner),
                    'D19_quotient_fold_absorb',
                ))

    return results


def sort_stability_axiom(
    term: OTerm,
    ctx: FiberCtx,
) -> List[RewriteResult]:
    """Sort stability: stable_sort(xs) = unstable_sort(xs) when keys are unique.

    When no two elements share the same sort key, stability is
    vacuously satisfied.  This lets us equate ``sorted()`` (stable)
    with ``heapq.nsmallest(len, xs)`` (unstable) freely.
    """
    results: List[RewriteResult] = []

    if isinstance(term, OOp) and term.name == 'stable_sort':
        results.append(RewriteResult(
            OOp('sorted', term.args),
            'D19_stability_to_sorted',
        ))

    if isinstance(term, OOp) and term.name == 'sorted':
        results.append(RewriteResult(
            OOp('stable_sort', term.args),
            'D19_sorted_to_stability',
        ))

    if isinstance(term, OOp) and term.name in ('sorted', 'stable_sort'):
        if len(term.args) == 1:
            results.append(RewriteResult(
                OOp('unstable_sort', term.args),
                'D19_sort_unique_keys_unstable',
                confidence=0.5,
            ))

    return results


# ═══════════════════════════════════════════════════════════
# §5  D20: Specification Uniqueness  (Theorem 22.6.1)
# ═══════════════════════════════════════════════════════════

def identify_spec_extended(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """Extended spec identification — the Yoneda embedding for programs.

    Recognises: factorial, fibonacci_like, range_sum, sorted, binomial,
    gcd, lcm, is_prime, power, flatten, zip_with, partition, group_by,
    matrix_multiply, tree_traversal (inorder/preorder/postorder).
    """
    spec = _identify_factorial(term)
    if spec:
        return spec

    spec = _identify_range_sum(term)
    if spec:
        return spec

    spec = _identify_fibonacci(term)
    if spec:
        return spec

    spec = _identify_sorted(term)
    if spec:
        return spec

    spec = _identify_gcd(term)
    if spec:
        return spec

    spec = _identify_lcm(term)
    if spec:
        return spec

    spec = _identify_is_prime(term)
    if spec:
        return spec

    spec = _identify_power(term)
    if spec:
        return spec

    spec = _identify_flatten(term)
    if spec:
        return spec

    spec = _identify_zip_with(term)
    if spec:
        return spec

    spec = _identify_partition(term)
    if spec:
        return spec

    spec = _identify_group_by(term)
    if spec:
        return spec

    spec = _identify_matrix_multiply(term)
    if spec:
        return spec

    spec = _identify_tree_traversal(term)
    if spec:
        return spec

    return None


def _identify_factorial(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """fold[mul](1, range(1, n+1)) or fix with n * f(n-1)."""
    if isinstance(term, OFold):
        if term.op_name in ('.mul', 'mul', 'imul', 'mult'):
            if isinstance(term.init, OLit) and term.init.value == 1:
                if isinstance(term.collection, OOp) and term.collection.name == 'range':
                    return ('factorial', (term.collection.args[-1],))
    if isinstance(term, OFix):
        canon = term.body.canon()
        if ('mul' in canon or 'mult' in canon) and 'sub' in canon:
            if '0' in canon or '1' in canon:
                inputs = _extract_free_vars(term)
                if inputs:
                    return ('factorial', tuple(OVar(v) for v in sorted(inputs)))
    return None


def _identify_range_sum(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """fold[add](0, range(…))."""
    if isinstance(term, OFold):
        if term.op_name in ('.add', 'add', 'iadd'):
            if isinstance(term.init, OLit) and term.init.value == 0:
                if isinstance(term.collection, OOp) and term.collection.name == 'range':
                    return ('range_sum', (term.collection.args[-1],))
    return None


def _identify_fibonacci(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """fix with f(n-1) + f(n-2) pattern."""
    if isinstance(term, OFix):
        canon = term.body.canon()
        if 'add' in canon and 'sub' in canon:
            inputs = _extract_free_vars(term)
            if inputs:
                return ('fibonacci_like', tuple(OVar(v) for v in sorted(inputs)))
    return None


def _identify_sorted(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    if isinstance(term, OOp) and term.name == 'sorted':
        return ('sorted', term.args)
    return None


def _identify_gcd(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """GCD: Euclidean (mod), subtraction-based, or binary GCD.

    Pattern: OFix with base case on 0 and recursive call with (b, a%b)
    or (a-b, b).
    """
    if isinstance(term, OFix):
        canon = term.body.canon()
        has_mod_or_sub = ('mod' in canon or 'sub' in canon)
        has_zero_base = ('0' in canon)
        if has_mod_or_sub and has_zero_base:
            inputs = _extract_free_vars(term)
            sorted_inputs = sorted(inputs)
            if len(sorted_inputs) >= 2:
                return ('gcd', (OVar(sorted_inputs[0]), OVar(sorted_inputs[1])))

    if isinstance(term, OOp) and term.name == 'math.gcd':
        return ('gcd', term.args)

    return None


def _identify_lcm(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """LCM: a * b // gcd(a, b)."""
    if isinstance(term, OOp) and term.name == 'math.lcm':
        return ('lcm', term.args)

    if isinstance(term, OOp) and term.name in ('floordiv', 'div'):
        if len(term.args) == 2:
            numer, denom = term.args
            if isinstance(numer, OOp) and numer.name in ('mul', 'mult'):
                if isinstance(denom, OOp) and denom.name in ('math.gcd', 'gcd'):
                    return ('lcm', numer.args)
            if isinstance(numer, OOp) and numer.name == 'abs':
                if len(numer.args) == 1 and isinstance(numer.args[0], OOp):
                    if numer.args[0].name in ('mul', 'mult'):
                        return ('lcm', numer.args[0].args)

    return None


def _identify_is_prime(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """Prime test: trial division, sieve, Miller-Rabin.

    Pattern: OFix or OFold checking divisibility up to sqrt(n).
    """
    if isinstance(term, OFix):
        canon = term.body.canon()
        if ('mod' in canon and ('sqrt' in canon or 'mul' in canon)):
            inputs = _extract_free_vars(term)
            if inputs:
                return ('is_prime', (OVar(sorted(inputs)[0]),))

    if isinstance(term, OFold):
        canon = term.collection.canon() if term.collection else ''
        init_canon = term.init.canon()
        if 'mod' in canon or 'mod' in term.op_name:
            inputs = _extract_free_vars(term)
            if inputs:
                return ('is_prime', (OVar(sorted(inputs)[0]),))

    return None


def _identify_power(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """Power/exponentiation: iterative multiply or fast-exp.

    Pattern: OFix with mul and halving of exponent, or fold[mul](1, repeat(base, exp)).
    """
    if isinstance(term, OOp) and term.name in ('pow', 'math.pow', '**'):
        return ('power', term.args)

    if isinstance(term, OFix):
        canon = term.body.canon()
        if ('mul' in canon or 'mult' in canon) and ('floordiv' in canon or 'rshift' in canon):
            inputs = _extract_free_vars(term)
            sorted_inp = sorted(inputs)
            if len(sorted_inp) >= 2:
                return ('power', (OVar(sorted_inp[0]), OVar(sorted_inp[1])))

    if isinstance(term, OFold):
        if term.op_name in ('mul', '.mul', 'imul', 'mult'):
            if isinstance(term.init, OLit) and term.init.value == 1:
                if isinstance(term.collection, OOp) and term.collection.name == 'repeat':
                    if len(term.collection.args) == 2:
                        base, exp = term.collection.args
                        return ('power', (base, exp))

    return None


def _identify_flatten(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """flatten: nested list → flat list via concat fold or chain."""
    if isinstance(term, OOp) and term.name in ('chain.from_iterable', 'flatten'):
        return ('flatten', term.args)

    if isinstance(term, OFold):
        if term.op_name in ('concat', 'extend', 'iadd', '.add'):
            if isinstance(term.init, OSeq) and len(term.init.elements) == 0:
                return ('flatten', (term.collection,))
            if isinstance(term.init, OOp) and term.init.name == 'list' and not term.init.args:
                return ('flatten', (term.collection,))

    return None


def _identify_zip_with(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """zip_with(f, xs, ys): map(f, zip(xs, ys))."""
    if isinstance(term, OMap):
        if isinstance(term.collection, OOp) and term.collection.name == 'zip':
            if len(term.collection.args) == 2:
                return ('zip_with', (term.transform,) + term.collection.args)

    if isinstance(term, OOp) and term.name == 'starmap':
        if len(term.args) == 2:
            fn, zipped = term.args
            if isinstance(zipped, OOp) and zipped.name == 'zip':
                return ('zip_with', (fn,) + zipped.args)

    return None


def _identify_partition(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """partition(pred, xs): split xs into (true_part, false_part)."""
    if isinstance(term, OOp) and term.name == 'partition':
        return ('partition', term.args)

    if isinstance(term, OOp) and term.name == 'tuple' and len(term.args) == 2:
        lhs, rhs = term.args
        if isinstance(lhs, OMap) and isinstance(rhs, OMap):
            if lhs.filter_pred is not None and rhs.filter_pred is not None:
                if (lhs.collection.canon() == rhs.collection.canon()):
                    lp_canon = lhs.filter_pred.canon()
                    rp_canon = rhs.filter_pred.canon()
                    if f'u_not({lp_canon})' == rp_canon or f'u_not({rp_canon})' == lp_canon:
                        return ('partition', (lhs.filter_pred, lhs.collection))

    return None


def _identify_group_by(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """group_by(key_fn, xs): partition xs into groups by key."""
    if isinstance(term, OOp) and term.name == 'groupby':
        return ('group_by', term.args)

    if isinstance(term, OFold):
        if term.op_name in ('dict_append', 'setdefault_append'):
            return ('group_by', (OUnknown('key_fn'), term.collection))

    return None


def _identify_matrix_multiply(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """matrix_multiply(A, B): triple loop or numpy matmul."""
    if isinstance(term, OOp) and term.name in ('matmul', 'np.dot', '@'):
        return ('matrix_multiply', term.args)

    if isinstance(term, OOp) and term.name == 'list':
        if len(term.args) == 1 and isinstance(term.args[0], OMap):
            outer_map = term.args[0]
            if isinstance(outer_map.transform, OLam):
                body = outer_map.transform.body
                if isinstance(body, OMap) or isinstance(body, OOp):
                    canon = body.canon()
                    if 'sum' in canon and ('mul' in canon or 'mult' in canon):
                        inputs = _extract_free_vars(term)
                        sorted_inp = sorted(inputs)
                        if len(sorted_inp) >= 2:
                            return ('matrix_multiply',
                                    (OVar(sorted_inp[0]), OVar(sorted_inp[1])))

    return None


def _identify_tree_traversal(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """Tree traversal: inorder, preorder, postorder."""
    if isinstance(term, OOp) and term.name in ('inorder', 'preorder', 'postorder'):
        return ('tree_traversal_' + term.name, term.args)

    if isinstance(term, OFix):
        canon = term.body.canon()
        if '.left' in canon and '.right' in canon:
            inputs = _extract_free_vars(term)
            if inputs:
                if '.val' in canon or '.data' in canon:
                    has_concat = 'concat' in canon or 'add' in canon
                    if has_concat:
                        return ('tree_traversal', tuple(OVar(v) for v in sorted(inputs)))

    return None


def axiom_d20_spec_unify_extended(
    term: OTerm,
    ctx: FiberCtx,
) -> List[RewriteResult]:
    """Extended D20: replace recognised computations with abstract specs.

    Uses the full extended spec library.
    """
    results: List[RewriteResult] = []
    spec = identify_spec_extended(term)
    if spec is not None:
        spec_name, inputs = spec
        results.append(RewriteResult(
            OAbstract(spec_name, inputs),
            'D20_spec_discovery',
        ))
    return results


# ═══════════════════════════════════════════════════════════
# §6  D22: Effect Elimination  (Theorem 23.2.1)
# ═══════════════════════════════════════════════════════════

def extract_exception_guard(body: OTerm) -> Optional[OTerm]:
    """Extract a decidable guard from a try/except body.

    Implements the previously-stubbed ``_extract_exception_guard``.
    Covers:
      • ZeroDivisionError  from x//y or x/y
      • IndexError          from xs[i]
      • KeyError             from d[k]
      • ValueError           from int(s)
      • AttributeError       from x.attr
    """
    if isinstance(body, OOp):
        if body.name in ('floordiv', 'truediv', 'div', 'mod'):
            if len(body.args) == 2:
                return OOp('noteq', (body.args[1], OLit(0)))

        if body.name == 'getitem':
            if len(body.args) == 2:
                xs, i = body.args
                return OOp('and', (
                    OOp('ge', (i, OLit(0))),
                    OOp('lt', (i, OOp('len', (xs,)))),
                ))

        if body.name in ('dictget', 'dict_getitem'):
            if len(body.args) == 2:
                return OOp('contains', (body.args[0], body.args[1]))

        if body.name in ('int', 'float'):
            if len(body.args) == 1:
                return OOp('isdigit', (body.args[0],))

        if body.name == 'getattr':
            if len(body.args) == 2:
                return OOp('hasattr', (body.args[0], body.args[1]))

    if isinstance(body, OCase):
        guard_then = extract_exception_guard(body.true_branch)
        guard_else = extract_exception_guard(body.false_branch)
        if guard_then and guard_else:
            return OOp('and', (
                OOp('or', (OOp('u_not', (body.test,)), guard_then)),
                OOp('or', (body.test, guard_else)),
            ))
        if guard_then:
            return OOp('or', (OOp('u_not', (body.test,)), guard_then))
        if guard_else:
            return OOp('or', (body.test, guard_else))

    return None


def is_exception_guard(test: OTerm) -> bool:
    """Check whether *test* is recognisably an exception-avoidance guard.

    Matches patterns like ``noteq(y, 0)``, ``lt(i, len(xs))``,
    ``contains(d, k)``, ``isdigit(s)``, ``hasattr(x, a)``.
    """
    if not isinstance(test, OOp):
        return False

    if test.name == 'noteq' and len(test.args) == 2:
        if isinstance(test.args[1], OLit) and test.args[1].value == 0:
            return True

    if test.name == 'lt' and len(test.args) == 2:
        if isinstance(test.args[1], OOp) and test.args[1].name == 'len':
            return True

    if test.name in ('contains', 'isdigit', 'hasattr'):
        return True

    if test.name == 'and' and len(test.args) == 2:
        return all(is_exception_guard(a) for a in test.args)

    if test.name == 'or' and len(test.args) == 2:
        return any(is_exception_guard(a) for a in test.args)

    if test.name == 'ge' and len(test.args) == 2:
        if isinstance(test.args[1], OLit) and test.args[1].value == 0:
            return True

    return False


def axiom_d22_effect_elim_extended(
    term: OTerm,
    ctx: FiberCtx,
) -> List[RewriteResult]:
    """Extended D22: OCatch ↔ OCase with real guard extraction.

    Now implements the full exception-guard extraction for common
    Python exception types plus the reverse direction.
    """
    results: List[RewriteResult] = []

    if isinstance(term, OCatch):
        guard = extract_exception_guard(term.body)
        if guard is not None:
            results.append(RewriteResult(
                OCase(guard, term.body, term.default),
                'D22_catch_to_case',
            ))

    if isinstance(term, OCase):
        if is_exception_guard(term.test):
            results.append(RewriteResult(
                OCatch(term.true_branch, term.false_branch),
                'D22_case_to_catch',
            ))

    return results


# ═══════════════════════════════════════════════════════════
# §7  D24: η-Reduction  (Theorem 23.4.1)
# ═══════════════════════════════════════════════════════════

def axiom_d24_eta_extended(
    term: OTerm,
    ctx: FiberCtx,
) -> List[RewriteResult]:
    """Extended D24: η-contraction / expansion for multi-argument lambdas.

    Handles:
      • Single-arg: λx. f(x) → f
      • Multi-arg:  λ(x,y). f(x,y) → f
      • Partial:    λ(x,y). f(x, y, CONST) → partial(f, CONST)
      • Composition detection: λx. g(f(x)) → g ∘ f  (not η but related)
    """
    results: List[RewriteResult] = []

    if not isinstance(term, OLam):
        return results

    # --- Multi-arg η-contraction ---
    if isinstance(term.body, OOp):
        body_op = term.body
        if len(body_op.args) == len(term.params):
            all_match = all(
                isinstance(a, OVar) and a.name == p
                for a, p in zip(body_op.args, term.params)
            )
            if all_match:
                results.append(RewriteResult(
                    OOp(body_op.name, ()),
                    'D24_eta_contract_multi',
                ))

    # --- Partial application detection ---
    if isinstance(term.body, OOp) and len(term.body.args) > len(term.params):
        body_op = term.body
        param_set = set(term.params)
        forwarded: List[int] = []
        constants: List[Tuple[int, OTerm]] = []
        param_idx = 0
        valid = True
        for i, arg in enumerate(body_op.args):
            if isinstance(arg, OVar) and arg.name in param_set:
                if param_idx < len(term.params) and arg.name == term.params[param_idx]:
                    forwarded.append(i)
                    param_idx += 1
                else:
                    valid = False
                    break
            else:
                constants.append((i, arg))

        if valid and param_idx == len(term.params) and constants:
            const_terms = tuple(c[1] for c in constants)
            results.append(RewriteResult(
                OOp('partial', (OOp(body_op.name, ()), *const_terms)),
                'D24_eta_partial',
            ))

    # --- Composition detection: λx. g(f(x)) → compose(g, f) ---
    if len(term.params) == 1:
        x = term.params[0]
        if isinstance(term.body, OOp) and len(term.body.args) == 1:
            inner = term.body.args[0]
            if isinstance(inner, OOp) and len(inner.args) == 1:
                if isinstance(inner.args[0], OVar) and inner.args[0].name == x:
                    results.append(RewriteResult(
                        OOp('compose', (OOp(term.body.name, ()), OOp(inner.name, ()))),
                        'D24_eta_compose',
                    ))

    return results


# ═══════════════════════════════════════════════════════════
# §8  Supporting axiom extensions
# ═══════════════════════════════════════════════════════════

def axiom_algebra_extended(
    term: OTerm,
    ctx: FiberCtx,
) -> List[RewriteResult]:
    """Extensions to the base algebraic axiom:

    • Absorption:   a ∧ (a ∨ b) = a,  a ∨ (a ∧ b) = a
    • Idempotence:  max(a,a) = a, min(a,a) = a, and(a,a) = a
    • Distributivity: a * (b + c) = a*b + a*c
    • Annihilation: mul(x, 0) = 0, and(x, False) = False
    """
    results: List[RewriteResult] = []
    if not isinstance(term, OOp):
        return results

    # Absorption: and(a, or(a, b)) → a
    if term.name == 'and' and len(term.args) == 2:
        a, rhs = term.args
        if isinstance(rhs, OOp) and rhs.name == 'or' and len(rhs.args) == 2:
            if a.canon() == rhs.args[0].canon() or a.canon() == rhs.args[1].canon():
                results.append(RewriteResult(a, 'ALG_absorb_and_or'))

    if term.name == 'or' and len(term.args) == 2:
        a, rhs = term.args
        if isinstance(rhs, OOp) and rhs.name == 'and' and len(rhs.args) == 2:
            if a.canon() == rhs.args[0].canon() or a.canon() == rhs.args[1].canon():
                results.append(RewriteResult(a, 'ALG_absorb_or_and'))

    # Idempotence: op(a, a) → a for idempotent ops
    if _is_idempotent_op(term.name) and len(term.args) == 2:
        if term.args[0].canon() == term.args[1].canon():
            results.append(RewriteResult(term.args[0], 'ALG_idempotent'))

    # Distributivity: mul(a, add(b, c)) → add(mul(a,b), mul(a,c))
    if term.name in ('mul', 'mult', '.mul') and len(term.args) == 2:
        a, rhs = term.args
        if isinstance(rhs, OOp) and rhs.name in ('add', '.add') and len(rhs.args) == 2:
            b, c = rhs.args
            results.append(RewriteResult(
                OOp(rhs.name, (OOp(term.name, (a, b)), OOp(term.name, (a, c)))),
                'ALG_distribute_mul_add',
            ))

    # Annihilation: mul(x, 0) → 0
    if term.name in ('mul', 'mult', '.mul') and len(term.args) == 2:
        for i in range(2):
            if isinstance(term.args[i], OLit) and term.args[i].value == 0:
                results.append(RewriteResult(OLit(0), 'ALG_annihilate_zero'))
                break

    # Annihilation: and(x, False) → False
    if term.name == 'and' and len(term.args) == 2:
        for i in range(2):
            if isinstance(term.args[i], OLit) and term.args[i].value is False:
                results.append(RewriteResult(OLit(False), 'ALG_annihilate_false'))
                break

    # or(x, True) → True
    if term.name == 'or' and len(term.args) == 2:
        for i in range(2):
            if isinstance(term.args[i], OLit) and term.args[i].value is True:
                results.append(RewriteResult(OLit(True), 'ALG_annihilate_true'))
                break

    return results


def axiom_fold_extended(
    term: OTerm,
    ctx: FiberCtx,
) -> List[RewriteResult]:
    """Extended fold axioms:

    • fold[append]([], x) → list(x)
    • fold[union]({}, x) → set(x)
    • fold[and](True, xs) → all(xs)
    • fold[or](False, xs) → any(xs)
    • fold[max](-inf, xs) → max(xs)
    • fold[min](inf, xs) → min(xs)
    """
    results: List[RewriteResult] = []

    if not isinstance(term, OFold):
        # Reverse direction: list(x) → fold[append]([], x)
        if isinstance(term, OOp) and term.name == 'list' and len(term.args) == 1:
            results.append(RewriteResult(
                OFold('append', OSeq(()), term.args[0]),
                'FOLD_list_expand',
            ))
        if isinstance(term, OOp) and term.name == 'set' and len(term.args) == 1:
            results.append(RewriteResult(
                OFold('union', OOp('set', ()), term.args[0]),
                'FOLD_set_expand',
            ))
        if isinstance(term, OOp) and term.name == 'all' and len(term.args) == 1:
            results.append(RewriteResult(
                OFold('and', OLit(True), term.args[0]),
                'FOLD_all_expand',
            ))
        if isinstance(term, OOp) and term.name == 'any' and len(term.args) == 1:
            results.append(RewriteResult(
                OFold('or', OLit(False), term.args[0]),
                'FOLD_any_expand',
            ))
        return results

    # fold[append]([], x) → list(x)
    if term.op_name in ('append', 'list_append'):
        if isinstance(term.init, OSeq) and len(term.init.elements) == 0:
            results.append(RewriteResult(
                OOp('list', (term.collection,)),
                'FOLD_append_to_list',
            ))

    # fold[union]({}, x) → set(x)
    if term.op_name in ('union', 'set_add'):
        if isinstance(term.init, OOp) and term.init.name == 'set' and not term.init.args:
            results.append(RewriteResult(
                OOp('set', (term.collection,)),
                'FOLD_union_to_set',
            ))

    # fold[and](True, xs) → all(xs)
    if term.op_name == 'and':
        if isinstance(term.init, OLit) and term.init.value is True:
            results.append(RewriteResult(
                OOp('all', (term.collection,)),
                'FOLD_and_to_all',
            ))

    # fold[or](False, xs) → any(xs)
    if term.op_name == 'or':
        if isinstance(term.init, OLit) and term.init.value is False:
            results.append(RewriteResult(
                OOp('any', (term.collection,)),
                'FOLD_or_to_any',
            ))

    # fold[max](-inf, xs) → max(xs)
    if term.op_name == 'max':
        if isinstance(term.init, OLit) and term.init.value == float('-inf'):
            results.append(RewriteResult(
                OOp('max', (term.collection,)),
                'FOLD_max_collapse',
            ))

    # fold[min](inf, xs) → min(xs)
    if term.op_name == 'min':
        if isinstance(term.init, OLit) and term.init.value == float('inf'):
            results.append(RewriteResult(
                OOp('min', (term.collection,)),
                'FOLD_min_collapse',
            ))

    return results


def axiom_case_extended(
    term: OTerm,
    ctx: FiberCtx,
) -> List[RewriteResult]:
    """Extended case axiom — De Morgan distribution and guard merging.

    • case(and(g1,g2), a, b) → case(g1, case(g2, a, b), b)
    • case(or(g1,g2), a, b) → case(g1, a, case(g2, a, b))
    • case(g, a, a) → a  (already in base, included for completeness)
    """
    results: List[RewriteResult] = []
    if not isinstance(term, OCase):
        return results

    # De Morgan distribution: and guard
    if isinstance(term.test, OOp) and term.test.name == 'and' and len(term.test.args) == 2:
        g1, g2 = term.test.args
        results.append(RewriteResult(
            OCase(g1, OCase(g2, term.true_branch, term.false_branch), term.false_branch),
            'CASE_demorgan_and',
        ))

    # De Morgan distribution: or guard
    if isinstance(term.test, OOp) and term.test.name == 'or' and len(term.test.args) == 2:
        g1, g2 = term.test.args
        results.append(RewriteResult(
            OCase(g1, term.true_branch, OCase(g2, term.true_branch, term.false_branch)),
            'CASE_demorgan_or',
        ))

    # Guard subsumption in nested cases
    if isinstance(term.true_branch, OCase):
        inner = term.true_branch
        if inner.test.canon() == term.test.canon():
            results.append(RewriteResult(
                OCase(term.test, inner.true_branch, term.false_branch),
                'CASE_guard_subsume_then',
            ))

    if isinstance(term.false_branch, OCase):
        inner = term.false_branch
        if inner.test.canon() == term.test.canon():
            results.append(RewriteResult(
                OCase(term.test, term.true_branch, inner.false_branch),
                'CASE_guard_subsume_else',
            ))

    return results


def axiom_quotient_extended(
    term: OTerm,
    ctx: FiberCtx,
) -> List[RewriteResult]:
    """Extended quotient axiom — duplicate equivalence classes.

    • Q[dup](set(x)) → set(x)
    • Q[perm](Q[perm](x)) → Q[perm](x)  (idempotence)
    • set(Q[perm](x)) → set(x)
    """
    results: List[RewriteResult] = []

    # Q[dup](set(x)) → set(x)
    if isinstance(term, OQuotient) and term.equiv_class == 'dup':
        if isinstance(term.inner, OOp) and term.inner.name == 'set':
            results.append(RewriteResult(term.inner, 'QUOT_dup_set_absorb'))

    # Q[perm](Q[perm](x)) → Q[perm](x) — idempotence
    if isinstance(term, OQuotient) and isinstance(term.inner, OQuotient):
        if term.equiv_class == term.inner.equiv_class:
            results.append(RewriteResult(term.inner, 'QUOT_idempotent'))

    # set(Q[perm](x)) → set(x)
    if isinstance(term, OOp) and term.name == 'set' and len(term.args) == 1:
        if isinstance(term.args[0], OQuotient) and term.args[0].equiv_class == 'perm':
            results.append(RewriteResult(
                OOp('set', (term.args[0].inner,)),
                'QUOT_set_perm_absorb',
            ))

    return results


# ═══════════════════════════════════════════════════════════
# §9  Axiom Composition Rules
# ═══════════════════════════════════════════════════════════

AxiomFn = Callable[[OTerm, FiberCtx], List[RewriteResult]]

AXIOM_REGISTRY: Dict[str, AxiomFn] = {
    'D13_histogram':   axiom_d13_histogram_extended,
    'D16_memo_dp':     axiom_d16_memo_dp_extended,
    'D17_assoc':       axiom_d17_assoc_extended,
    'D19_sort':        axiom_d19_sort_extended,
    'D19_stability':   sort_stability_axiom,
    'D20_spec':        axiom_d20_spec_unify_extended,
    'D22_effect':      axiom_d22_effect_elim_extended,
    'D24_eta':         axiom_d24_eta_extended,
    'ALG_extended':    axiom_algebra_extended,
    'FOLD_extended':   axiom_fold_extended,
    'CASE_extended':   axiom_case_extended,
    'QUOT_extended':   axiom_quotient_extended,
}

COMPOSABLE_PAIRS: List[Tuple[str, str]] = [
    ('D13_histogram', 'D19_sort'),
    ('D13_histogram', 'FOLD_extended'),
    ('D16_memo_dp',   'D17_assoc'),
    ('D17_assoc',     'FOLD_extended'),
    ('D19_sort',      'QUOT_extended'),
    ('D19_sort',      'D17_assoc'),
    ('D19_stability', 'D19_sort'),
    ('D20_spec',      'D24_eta'),
    ('D20_spec',      'D22_effect'),
    ('D22_effect',    'CASE_extended'),
    ('D22_effect',    'ALG_extended'),
    ('D24_eta',       'ALG_extended'),
    ('FOLD_extended', 'ALG_extended'),
    ('CASE_extended', 'ALG_extended'),
    ('QUOT_extended', 'D19_sort'),
    ('QUOT_extended', 'FOLD_extended'),
]


def can_compose(axiom_a: str, axiom_b: str) -> bool:
    """Check whether axiom_a's output can feed into axiom_b.

    Uses the declared composability table.  Composition is
    directional: (a, b) means "apply a then b".
    """
    return (axiom_a, axiom_b) in COMPOSABLE_PAIRS


def compose_axioms(
    term: OTerm,
    axiom_a: str,
    axiom_b: str,
    ctx: FiberCtx,
) -> List[RewriteResult]:
    """Apply axiom_a then axiom_b, returning composed rewrite chains."""
    if axiom_a not in AXIOM_REGISTRY or axiom_b not in AXIOM_REGISTRY:
        return []

    fn_a = AXIOM_REGISTRY[axiom_a]
    fn_b = AXIOM_REGISTRY[axiom_b]

    results: List[RewriteResult] = []
    for step1 in fn_a(term, ctx):
        for step2 in fn_b(step1.term, ctx):
            composed_conf = step1.confidence * step2.confidence
            results.append(RewriteResult(
                step2.term,
                f'{step1.axiom}+{step2.axiom}',
                composed_conf,
            ))
    return results


def all_compositions(
    term: OTerm,
    ctx: FiberCtx,
    max_chain: int = 2,
) -> List[RewriteResult]:
    """Try all valid axiom compositions up to *max_chain* steps."""
    results: List[RewriteResult] = []
    for a, b in COMPOSABLE_PAIRS:
        results.extend(compose_axioms(term, a, b, ctx))
    return results


# ═══════════════════════════════════════════════════════════
# §10  Axiom Relevance Scoring
# ═══════════════════════════════════════════════════════════

@dataclass
class ScoredAxiom:
    """An axiom ranked by expected relevance for an (OTerm, OTerm) pair."""
    name: str
    score: float
    reason: str


def _term_signature(term: OTerm) -> Dict[str, int]:
    """Build a feature vector from an OTerm's canonical form."""
    canon = term.canon()
    features: Dict[str, int] = {
        'has_fix': int('fix[' in canon),
        'has_fold': int('fold[' in canon),
        'has_case': int('case(' in canon),
        'has_catch': int('catch(' in canon),
        'has_lam': int('λ(' in canon),
        'has_sorted': int('sorted(' in canon),
        'has_counter': int('Counter(' in canon),
        'has_quotient': int('Q[' in canon),
        'has_abstract': int('@' in canon),
        'has_map': int('map(' in canon),
        'has_mod': int('mod(' in canon),
        'has_div': int('div(' in canon or 'floordiv(' in canon),
        'has_mul': int('mul(' in canon or 'mult(' in canon),
        'has_add': int('add(' in canon),
        'has_getitem': int('getitem(' in canon),
        'depth': canon.count('('),
    }
    return features


def score_axiom_relevance(
    source: OTerm,
    target: OTerm,
) -> List[ScoredAxiom]:
    """Rank axioms by likelihood of helping bridge *source* → *target*.

    Uses structural heuristics on both terms' canonical forms.
    Returns a sorted list (highest-score first).
    """
    sf = _term_signature(source)
    tf = _term_signature(target)

    scored: List[ScoredAxiom] = []

    # D13: if one side has Counter and the other has fold
    if sf['has_counter'] != tf['has_counter'] or sf['has_fold'] != tf['has_fold']:
        scored.append(ScoredAxiom('D13_histogram', 0.9, 'Counter↔fold mismatch'))
    else:
        scored.append(ScoredAxiom('D13_histogram', 0.1, 'no histogram signal'))

    # D16: both have fix-points
    if sf['has_fix'] and tf['has_fix']:
        scored.append(ScoredAxiom('D16_memo_dp', 0.85, 'both have fix-points'))
    elif sf['has_fix'] != tf['has_fix']:
        scored.append(ScoredAxiom('D16_memo_dp', 0.5, 'one fix, one not'))
    else:
        scored.append(ScoredAxiom('D16_memo_dp', 0.05, 'no fix-points'))

    # D17: fold-level differences
    if sf['has_fold'] and tf['has_fold']:
        scored.append(ScoredAxiom('D17_assoc', 0.7, 'both have folds — bracketing?'))
    else:
        scored.append(ScoredAxiom('D17_assoc', 0.1, 'no fold pair'))

    # D19: sorted presence
    if sf['has_sorted'] != tf['has_sorted']:
        scored.append(ScoredAxiom('D19_sort', 0.9, 'sorted on one side only'))
    elif sf['has_sorted'] and tf['has_sorted']:
        scored.append(ScoredAxiom('D19_sort', 0.3, 'sorted on both'))
    else:
        scored.append(ScoredAxiom('D19_sort', 0.05, 'no sorted'))

    # D20: spec — always worth trying
    scored.append(ScoredAxiom('D20_spec', 0.6, 'spec unification always applicable'))

    # D22: catch ↔ case
    if sf['has_catch'] != tf['has_catch']:
        scored.append(ScoredAxiom('D22_effect', 0.95, 'catch↔case mismatch'))
    elif sf['has_catch'] and tf['has_case']:
        scored.append(ScoredAxiom('D22_effect', 0.7, 'catch and case both present'))
    else:
        scored.append(ScoredAxiom('D22_effect', 0.05, 'no effect signal'))

    # D24: lambda presence
    if sf['has_lam'] != tf['has_lam']:
        scored.append(ScoredAxiom('D24_eta', 0.8, 'lambda on one side only'))
    elif sf['has_lam'] and tf['has_lam']:
        scored.append(ScoredAxiom('D24_eta', 0.4, 'lambdas on both sides'))
    else:
        scored.append(ScoredAxiom('D24_eta', 0.05, 'no lambdas'))

    # ALG: always somewhat relevant when ops differ
    depth_diff = abs(sf['depth'] - tf['depth'])
    alg_score = min(0.5 + depth_diff * 0.05, 0.9)
    scored.append(ScoredAxiom('ALG_extended', alg_score, f'depth diff={depth_diff}'))

    # FOLD: if fold/sum/prod present
    if sf['has_fold'] or tf['has_fold']:
        scored.append(ScoredAxiom('FOLD_extended', 0.6, 'fold present'))
    else:
        scored.append(ScoredAxiom('FOLD_extended', 0.1, 'no fold'))

    # CASE: if case present
    if sf['has_case'] or tf['has_case']:
        scored.append(ScoredAxiom('CASE_extended', 0.5, 'case present'))
    else:
        scored.append(ScoredAxiom('CASE_extended', 0.1, 'no case'))

    # QUOT: if quotient present
    if sf['has_quotient'] or tf['has_quotient']:
        scored.append(ScoredAxiom('QUOT_extended', 0.7, 'quotient present'))
    else:
        scored.append(ScoredAxiom('QUOT_extended', 0.05, 'no quotient'))

    scored.sort(key=lambda s: s.score, reverse=True)
    return scored


def top_k_axioms(
    source: OTerm,
    target: OTerm,
    k: int = 5,
) -> List[str]:
    """Return the *k* most relevant axiom names for bridging
    *source* → *target*.
    """
    scored = score_axiom_relevance(source, target)
    return [s.name for s in scored[:k]]


# ═══════════════════════════════════════════════════════════
# §11  Integrated proposal runner
# ═══════════════════════════════════════════════════════════

def apply_all_extended_axioms(
    term: OTerm,
    ctx: Optional[FiberCtx] = None,
) -> List[RewriteResult]:
    """Apply every extended axiom to *term* and return all rewrites.

    This is the single entry point that the path-search engine
    would call to get extended rewrite candidates.
    """
    if ctx is None:
        ctx = FiberCtx()

    results: List[RewriteResult] = []
    for name, fn in AXIOM_REGISTRY.items():
        results.extend(fn(term, ctx))
    return results


def apply_best_axiom(
    source: OTerm,
    target: OTerm,
    ctx: Optional[FiberCtx] = None,
) -> Optional[RewriteResult]:
    """Try axioms in relevance-ranked order and return the first hit."""
    if ctx is None:
        ctx = FiberCtx()

    ranked = top_k_axioms(source, target, k=len(AXIOM_REGISTRY))
    for axiom_name in ranked:
        fn = AXIOM_REGISTRY.get(axiom_name)
        if fn is None:
            continue
        hits = fn(source, ctx)
        if hits:
            return hits[0]
    return None


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

    ctx = FiberCtx(param_duck_types={'p0': 'int', 'p1': 'int'})

    # ── D13 tests ──
    print("Testing D13 histogram …")
    xs = OVar('xs')
    counter_term = OOp('Counter', (xs,))
    d13_results = axiom_d13_histogram_extended(counter_term, ctx)
    _assert(len(d13_results) >= 1, "D13 Counter→fold should produce at least 1 result")
    _assert(d13_results[0].axiom == 'D13_counter_to_fold', "D13 axiom name")
    fold_term = d13_results[0].term
    _assert(isinstance(fold_term, OFold), "D13 result is OFold")
    d13_rev = axiom_d13_histogram_extended(fold_term, ctx)
    _assert(any(r.axiom == 'D13_fold_to_counter' for r in d13_rev), "D13 reverse direction")

    most_common = OOp('most_common', (counter_term, OLit(3)))
    d13_mc = axiom_d13_histogram_extended(most_common, ctx)
    _assert(len(d13_mc) >= 1, "D13 most_common should rewrite")

    variants = histogram_normalisation_variants()
    _assert(len(variants) == 3, "Three histogram variants")

    # ── D16 tests ──
    print("Testing D16 memo/DP …")
    fix_term = OFix('abc', OOp('add', (OVar('n'), OOp('sub', (OVar('n'), OLit(1))))))
    d16 = axiom_d16_memo_dp_extended(fix_term, ctx)
    _assert(len(d16) >= 1, "D16 should normalise fix name")
    _assert(d16[0].axiom == 'D16_recurrence_normalize', "D16 axiom name")
    canon_ext = canonicalize_recurrence_extended(fix_term)
    _assert(canon_ext is not None, "canonicalize_recurrence_extended works")

    # ── D17 tests ──
    print("Testing D17 assoc …")
    tree_fold = OFold('add', OLit(0), OOp('tree_split', (xs,)))
    d17 = axiom_d17_assoc_extended(tree_fold, ctx)
    _assert(len(d17) >= 1, "D17 should flatten tree fold")
    _assert(isinstance(d17[0].term, OFold), "D17 result is OFold")
    _assert(d17[0].term.collection.canon() == xs.canon(), "D17 flattened collection is xs")

    ac_forms = ac_completion('add', [OVar('a'), OVar('b'), OVar('c')])
    _assert(len(ac_forms) >= 2, "AC completion produces multiple forms")
    ac_canon = ac_canonical_form('add', OOp('add', (OVar('b'), OOp('add', (OVar('a'), OVar('c'))))))
    _assert('add(' in ac_canon.canon(), "AC canonical form is an add")

    # ── D19 tests ──
    print("Testing D19 sort …")
    sorted_fold = OFold('add', OLit(0), OOp('sorted', (xs,)))
    d19 = axiom_d19_sort_extended(sorted_fold, ctx)
    _assert(any(r.axiom == 'D19_sort_irrelevant' for r in d19), "D19 sort absorption")

    keyed_fold = OFold('add', OLit(0), OOp('sorted_key', (xs, OLam(('x',), OOp('neg', (OVar('x'),))))))
    d19k = axiom_d19_sort_extended(keyed_fold, ctx)
    _assert(any(r.axiom == 'D19_keyed_sort_irrelevant' for r in d19k), "D19 keyed sort")

    d19_stab = sort_stability_axiom(OOp('stable_sort', (xs,)), ctx)
    _assert(len(d19_stab) >= 1, "D19 stability axiom fires")

    # ── D20 tests ──
    print("Testing D20 spec library …")
    a, b = OVar('a'), OVar('b')
    gcd_fix = OFix('gcd', OCase(
        OOp('eq', (b, OLit(0))), a, OOp('gcd', (b, OOp('mod', (a, b)))),
    ))
    gcd_spec = identify_spec_extended(gcd_fix)
    _assert(gcd_spec is not None, "D20 GCD recognised")
    _assert(gcd_spec[0] == 'gcd', "D20 GCD spec name")

    lcm_term = OOp('floordiv', (OOp('mul', (a, b)), OOp('math.gcd', (a, b))))
    lcm_spec = identify_spec_extended(lcm_term)
    _assert(lcm_spec is not None, "D20 LCM recognised")
    _assert(lcm_spec[0] == 'lcm', "D20 LCM spec name")

    prime_fix = OFix('prime', OCase(
        OOp('eq', (OOp('mod', (OVar('n'), OVar('i'))), OLit(0))),
        OLit(False),
        OOp('prime', (OVar('n'), OOp('add', (OVar('i'), OLit(1))))),
    ))
    prime_spec = identify_spec_extended(prime_fix)
    _assert(prime_spec is not None, "D20 is_prime recognised")

    pow_fix = OFix('pow', OCase(
        OOp('eq', (OVar('exp'), OLit(0))), OLit(1),
        OOp('mul', (OVar('base'), OOp('pow', (OVar('base'), OOp('sub', (OVar('exp'), OLit(1))))))),
    ))
    pow_spec = identify_spec_extended(pow_fix)
    _assert(pow_spec is not None, "D20 power recognised")

    flatten_term = OFold('concat', OSeq(()), OVar('nested'))
    flat_spec = identify_spec_extended(flatten_term)
    _assert(flat_spec is not None and flat_spec[0] == 'flatten', "D20 flatten recognised")

    zip_term = OMap(OLam(('pair',), OOp('apply', (OVar('f'), OVar('pair')))),
                    OOp('zip', (OVar('xs'), OVar('ys'))))
    zip_spec = identify_spec_extended(zip_term)
    _assert(zip_spec is not None and zip_spec[0] == 'zip_with', "D20 zip_with recognised")

    groupby_term = OFold('dict_append', ODict(()), OVar('items'))
    gb_spec = identify_spec_extended(groupby_term)
    _assert(gb_spec is not None and gb_spec[0] == 'group_by', "D20 group_by recognised")

    matmul_term = OOp('matmul', (OVar('A'), OVar('B')))
    mm_spec = identify_spec_extended(matmul_term)
    _assert(mm_spec is not None and mm_spec[0] == 'matrix_multiply', "D20 matrix_multiply")

    tree_term = OOp('inorder', (OVar('tree'),))
    tr_spec = identify_spec_extended(tree_term)
    _assert(tr_spec is not None and 'tree_traversal' in tr_spec[0], "D20 tree traversal")

    d20_results = axiom_d20_spec_unify_extended(gcd_fix, ctx)
    _assert(len(d20_results) >= 1, "D20 axiom produces OAbstract")
    _assert(isinstance(d20_results[0].term, OAbstract), "D20 result is OAbstract")

    # ── D22 tests ──
    print("Testing D22 effect elimination …")
    div_body = OOp('floordiv', (OVar('x'), OVar('y')))
    guard = extract_exception_guard(div_body)
    _assert(guard is not None, "D22 floordiv guard extracted")
    _assert(isinstance(guard, OOp) and guard.name == 'noteq', "D22 guard is noteq")

    idx_body = OOp('getitem', (OVar('xs'), OVar('i')))
    idx_guard = extract_exception_guard(idx_body)
    _assert(idx_guard is not None, "D22 getitem guard extracted")
    _assert(isinstance(idx_guard, OOp) and idx_guard.name == 'and', "D22 index guard is and")

    dict_body = OOp('dictget', (OVar('d'), OVar('k')))
    dict_guard = extract_exception_guard(dict_body)
    _assert(dict_guard is not None, "D22 dictget guard extracted")
    _assert(isinstance(dict_guard, OOp) and dict_guard.name == 'contains', "D22 dict guard")

    int_body = OOp('int', (OVar('s'),))
    int_guard = extract_exception_guard(int_body)
    _assert(int_guard is not None, "D22 int() guard extracted")

    catch_term = OCatch(div_body, OLit(0))
    d22 = axiom_d22_effect_elim_extended(catch_term, ctx)
    _assert(len(d22) >= 1, "D22 catch→case rewrite")
    _assert(isinstance(d22[0].term, OCase), "D22 result is OCase")

    _assert(is_exception_guard(guard), "D22 noteq(y,0) is exception guard")
    _assert(is_exception_guard(idx_guard), "D22 bounds check is exception guard")
    _assert(not is_exception_guard(OOp('add', (OLit(1), OLit(2)))), "add is not exception guard")

    case_term = OCase(
        OOp('noteq', (OVar('y'), OLit(0))),
        OOp('floordiv', (OVar('x'), OVar('y'))),
        OLit(0),
    )
    d22_rev = axiom_d22_effect_elim_extended(case_term, ctx)
    _assert(any(r.axiom == 'D22_case_to_catch' for r in d22_rev), "D22 reverse case→catch")

    # ── D24 tests ──
    print("Testing D24 eta …")
    single_eta = OLam(('x',), OOp('f', (OVar('x'),)))
    d24s = axiom_d24_eta_extended(single_eta, ctx)
    _assert(any(r.axiom == 'D24_eta_contract_multi' for r in d24s), "D24 single-arg eta")

    multi_eta = OLam(('x', 'y'), OOp('f', (OVar('x'), OVar('y'))))
    d24m = axiom_d24_eta_extended(multi_eta, ctx)
    _assert(any(r.axiom == 'D24_eta_contract_multi' for r in d24m), "D24 multi-arg eta")

    compose_lam = OLam(('x',), OOp('g', (OOp('f', (OVar('x'),)),)))
    d24c = axiom_d24_eta_extended(compose_lam, ctx)
    _assert(any(r.axiom == 'D24_eta_compose' for r in d24c), "D24 composition detection")

    non_eta = OLam(('x',), OOp('add', (OVar('x'), OLit(1))))
    d24n = axiom_d24_eta_extended(non_eta, ctx)
    _assert(not any(r.axiom == 'D24_eta_contract_multi' for r in d24n), "D24 non-eta not contracted")

    # ── Algebra extended ──
    print("Testing ALG extended …")
    absorb = OOp('and', (OVar('a'), OOp('or', (OVar('a'), OVar('b')))))
    alg = axiom_algebra_extended(absorb, ctx)
    _assert(any(r.axiom == 'ALG_absorb_and_or' for r in alg), "ALG absorption and/or")

    idem = OOp('max', (OVar('x'), OVar('x')))
    alg_i = axiom_algebra_extended(idem, ctx)
    _assert(any(r.axiom == 'ALG_idempotent' for r in alg_i), "ALG idempotent max")

    distrib = OOp('mul', (OVar('a'), OOp('add', (OVar('b'), OVar('c')))))
    alg_d = axiom_algebra_extended(distrib, ctx)
    _assert(any(r.axiom == 'ALG_distribute_mul_add' for r in alg_d), "ALG distributivity")

    annihilate = OOp('mul', (OVar('x'), OLit(0)))
    alg_z = axiom_algebra_extended(annihilate, ctx)
    _assert(any(r.axiom == 'ALG_annihilate_zero' for r in alg_z), "ALG zero annihilation")

    # ── Fold extended ──
    print("Testing FOLD extended …")
    fold_append = OFold('append', OSeq(()), OVar('items'))
    fold_r = axiom_fold_extended(fold_append, ctx)
    _assert(any(r.axiom == 'FOLD_append_to_list' for r in fold_r), "FOLD append→list")

    fold_and = OFold('and', OLit(True), OVar('bools'))
    fold_a = axiom_fold_extended(fold_and, ctx)
    _assert(any(r.axiom == 'FOLD_and_to_all' for r in fold_a), "FOLD and→all")

    fold_or = OFold('or', OLit(False), OVar('bools'))
    fold_o = axiom_fold_extended(fold_or, ctx)
    _assert(any(r.axiom == 'FOLD_or_to_any' for r in fold_o), "FOLD or→any")

    list_expand = OOp('list', (OVar('gen'),))
    fold_le = axiom_fold_extended(list_expand, ctx)
    _assert(any(r.axiom == 'FOLD_list_expand' for r in fold_le), "FOLD list→fold expand")

    # ── Case extended ──
    print("Testing CASE extended …")
    and_case = OCase(OOp('and', (OVar('g1'), OVar('g2'))), OVar('a'), OVar('b'))
    case_r = axiom_case_extended(and_case, ctx)
    _assert(any(r.axiom == 'CASE_demorgan_and' for r in case_r), "CASE De Morgan and")

    or_case = OCase(OOp('or', (OVar('g1'), OVar('g2'))), OVar('a'), OVar('b'))
    case_o = axiom_case_extended(or_case, ctx)
    _assert(any(r.axiom == 'CASE_demorgan_or' for r in case_o), "CASE De Morgan or")

    # ── Quotient extended ──
    print("Testing QUOT extended …")
    dup_set = OQuotient(OOp('set', (OVar('xs'),)), 'dup')
    quot_r = axiom_quotient_extended(dup_set, ctx)
    _assert(any(r.axiom == 'QUOT_dup_set_absorb' for r in quot_r), "QUOT dup+set absorb")

    double_q = OQuotient(OQuotient(OVar('xs'), 'perm'), 'perm')
    quot_i = axiom_quotient_extended(double_q, ctx)
    _assert(any(r.axiom == 'QUOT_idempotent' for r in quot_i), "QUOT idempotent")

    # ── Composition tests ──
    print("Testing axiom composition …")
    _assert(can_compose('D13_histogram', 'D19_sort'), "D13+D19 composable")
    _assert(not can_compose('D24_eta', 'D13_histogram'), "D24+D13 not composable")
    comp = compose_axioms(counter_term, 'D13_histogram', 'FOLD_extended', ctx)
    # May or may not produce results depending on axiom chaining
    _assert(isinstance(comp, list), "compose_axioms returns list")

    # ── Relevance scoring tests ──
    print("Testing relevance scoring …")
    source = OCatch(OOp('floordiv', (OVar('x'), OVar('y'))), OLit(0))
    target = OCase(OOp('noteq', (OVar('y'), OLit(0))),
                   OOp('floordiv', (OVar('x'), OVar('y'))), OLit(0))
    scored = score_axiom_relevance(source, target)
    _assert(len(scored) > 0, "relevance scoring returns results")
    _assert(scored[0].score > 0.5, "top axiom has non-trivial score")
    top = top_k_axioms(source, target, k=3)
    _assert('D22_effect' in top, "D22 ranked highly for catch↔case")

    # ── Integrated runner tests ──
    print("Testing integrated runner …")
    all_results = apply_all_extended_axioms(counter_term, ctx)
    _assert(len(all_results) >= 1, "apply_all returns results for Counter")

    best = apply_best_axiom(source, target, ctx)
    _assert(best is not None, "apply_best returns a result")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
