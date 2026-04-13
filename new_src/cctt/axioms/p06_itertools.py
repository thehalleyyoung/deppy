"""P6: Itertools Equivalences (Theorem P.6.1).

itertools combinators ↔ list comprehension / fold / recursive expansions.

Mathematical foundation:
  The itertools module provides lazy stream combinators that correspond to
  well-known categorical constructions:

  • chain(a, b) is the coproduct injection  a + b  in the category of
    finite sequences.
  • chain.from_iterable(xss) is the counit of the List monad (flatten / μ).
  • product(xs, ys) is the cartesian product  xs × ys  in Set, lifted
    to List via the monoidal structure.
  • combinations(xs, 2) is the 2-element subset functor  (xs choose 2).
  • permutations(xs) is the symmetric group action  S_n · xs.
  • groupby(sorted(xs, key=f), key=f) is the kernel of f, i.e. the
    equivalence relation induced by f, computed on the sorted carrier.
  • accumulate(xs, op) is the scan (prefix-fold) over the free monoid.
  • starmap(f, pairs) is fmap over the uncurried application functor.

  Each equivalence is a natural isomorphism in the presheaf category
  between the lazy iterator representation and the eager list form.

Covers:
  • itertools.chain(a, b) ↔ a + b
  • itertools.chain.from_iterable(xss) ↔ flatten
  • itertools.product(xs, ys) ↔ nested comprehension
  • itertools.combinations(xs, 2) ↔ nested index loop
  • itertools.permutations(xs) ↔ recursive permutation
  • itertools.groupby(sorted(xs, key=f), key=f) ↔ defaultdict grouping
  • itertools.accumulate(xs, op) ↔ prefix folds
  • itertools.starmap(f, pairs) ↔ [f(*p) for p in pairs]
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

AXIOM_NAME = 'P6_itertools'
AXIOM_CATEGORY = 'python_idiom'

SOUNDNESS_PROOF = """
Theorem P.6.1 (Itertools Equivalences):
  For lists a, b, xs, ys, xss and function f:
    (i)   list(itertools.chain(a, b))  ≡  a + b
    (ii)  list(chain.from_iterable(xss))  ≡  [x for xs in xss for x in xs]
    (iii) list(itertools.product(xs, ys))  ≡  [(x,y) for x in xs for y in ys]
    (iv)  list(itertools.combinations(xs, 2))
            ≡  [(xs[i], xs[j]) for i in range(n) for j in range(i+1, n)]
    (v)   list(itertools.permutations(xs))  ≡  perm(xs) (recursive)
    (vi)  dict(itertools.groupby(sorted(xs, key=f), key=f))
            ≡  fold[group_collect](defaultdict(list), xs)
    (vii) list(itertools.accumulate(xs, op))
            ≡  [reduce(op, xs[:i+1]) for i in range(len(xs))]
    (viii) list(itertools.starmap(f, pairs))  ≡  [f(*p) for p in pairs]

Proof sketch:
  Each equivalence follows from the definition of the respective
  itertools combinator and the universality of fold/map in List.
  (i) chain yields elements of a then b — same as concatenation.
  (ii) chain.from_iterable is the monadic join μ: List(List(X)) → List(X).
  (iii) product is the cartesian product enumerated row-major.
  (iv) combinations(2) enumerates 2-subsets in lexicographic order.
  (v) permutations enumerates all n! orderings.
  (vi) groupby on sorted input partitions by consecutive equal keys.
  (vii) accumulate is the left-scan (prefix sums) of the monoid.
  (viii) starmap applies f with tuple unpacking — fmap of uncurry.  ∎
"""

COMPOSES_WITH = ['P5_sort_variants', 'D01_fold_unfold', 'D05_fold_universal', 'D04_comp_fusion']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'chain to add',
        'before': "itertools.chain(a, b)",
        'after': "a + b",
        'axiom': 'P6_chain_to_add',
    },
    {
        'name': 'chain.from_iterable to flatten',
        'before': "itertools.chain.from_iterable(xss)",
        'after': "[x for xs in xss for x in xs]",
        'axiom': 'P6_chain_from_iterable_to_flatten',
    },
    {
        'name': 'product to nested comprehension',
        'before': "itertools.product(xs, ys)",
        'after': "[(x,y) for x in xs for y in ys]",
        'axiom': 'P6_product_to_nested_comp',
    },
    {
        'name': 'combinations(2) to index loop',
        'before': "itertools.combinations(xs, 2)",
        'after': "[(xs[i], xs[j]) for i in range(n) for j in range(i+1,n)]",
        'axiom': 'P6_combinations2_to_index_loop',
    },
    {
        'name': 'permutations to recursive',
        'before': "itertools.permutations(xs)",
        'after': "perm_rec(xs)",
        'axiom': 'P6_permutations_to_fix',
    },
    {
        'name': 'groupby to fold',
        'before': "itertools.groupby(sorted(xs, key=f), key=f)",
        'after': "fold[group_collect](defaultdict(list), xs)",
        'axiom': 'P6_groupby_to_fold',
    },
    {
        'name': 'accumulate to prefix folds',
        'before': "itertools.accumulate(xs, op)",
        'after': "[reduce(op, xs[:i+1]) for i in range(len(xs))]",
        'axiom': 'P6_accumulate_to_prefix_folds',
    },
    {
        'name': 'starmap to map',
        'before': "itertools.starmap(f, pairs)",
        'after': "[f(*p) for p in pairs]",
        'axiom': 'P6_starmap_to_map',
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
    """Apply P6 itertools equivalences to *term*.

    Returns list of (rewritten_term, axiom_label) pairs.
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── itertools.chain(a, b) → a + b ──
    if isinstance(term, OOp) and term.name == 'itertools.chain' and len(term.args) == 2:
        a, b = term.args
        results.append((OOp('add', (a, b)), 'P6_chain_to_add'))

    # ── a + b → itertools.chain(a, b) ──
    if isinstance(term, OOp) and term.name == 'add' and len(term.args) == 2:
        a, b = term.args
        results.append((OOp('itertools.chain', (a, b)), 'P6_add_to_chain'))

    # ── itertools.chain.from_iterable(xss) → flatten ──
    if isinstance(term, OOp) and term.name == 'itertools.chain.from_iterable' and len(term.args) == 1:
        xss = term.args[0]
        flat = OMap(
            OLam(('x',), OVar('x')),
            OOp('flatten', (xss,)),
        )
        results.append((flat, 'P6_chain_from_iterable_to_flatten'))

    # ── flatten → itertools.chain.from_iterable ──
    if isinstance(term, OOp) and term.name == 'flatten' and len(term.args) == 1:
        xss = term.args[0]
        results.append((
            OOp('itertools.chain.from_iterable', (xss,)),
            'P6_flatten_to_chain_from_iterable',
        ))

    # ── itertools.product(xs, ys) → nested comprehension map ──
    if isinstance(term, OOp) and term.name == 'itertools.product' and len(term.args) == 2:
        xs, ys = term.args
        # [(x, y) for x in xs for y in ys]
        inner_map = OMap(
            OLam(('y',), OSeq((OVar('x'), OVar('y')))),
            ys,
        )
        outer_map = OMap(
            OLam(('x',), inner_map),
            xs,
        )
        nested = OOp('flatten', (outer_map,))
        results.append((nested, 'P6_product_to_nested_comp'))

    # ── itertools.combinations(xs, 2) → nested index loop ──
    if isinstance(term, OOp) and term.name == 'itertools.combinations' and len(term.args) == 2:
        xs, k_term = term.args
        if isinstance(k_term, OLit) and k_term.value == 2:
            # [(xs[i], xs[j]) for i in range(n) for j in range(i+1, n)]
            index_loop = OOp('combinations_index_loop', (xs, OLit(2)))
            results.append((index_loop, 'P6_combinations2_to_index_loop'))

    # ── combinations_index_loop → itertools.combinations ──
    if isinstance(term, OOp) and term.name == 'combinations_index_loop' and len(term.args) == 2:
        xs, k_term = term.args
        results.append((
            OOp('itertools.combinations', (xs, k_term)),
            'P6_index_loop_to_combinations',
        ))

    # ── itertools.permutations(xs) → recursive permutation (OFix) ──
    if isinstance(term, OOp) and term.name == 'itertools.permutations' and len(term.args) == 1:
        xs = term.args[0]
        # Recursive permutation generator:
        #   fix perm. λxs. if len(xs) ≤ 1 then [xs]
        #                   else flatten([map(λp. [x] + p, perm(remove(xs, x))) for x in xs])
        perm_body = OCase(
            OOp('le', (OOp('len', (OVar('xs'),)), OLit(1))),
            OSeq((OVar('xs'),)),
            OOp('flatten', (
                OMap(
                    OLam(('x',), OMap(
                        OLam(('p',), OOp('add', (OSeq((OVar('x'),)), OVar('p')))),
                        OOp('apply', (OVar('perm'), OOp('remove', (OVar('xs'), OVar('x'))))),
                    )),
                    OVar('xs'),
                ),
            )),
        )
        perm_fix = OFix('perm', OLam(('xs',), perm_body))
        results.append((OOp('apply', (perm_fix, xs)), 'P6_permutations_to_fix'))

    # ── OFix('perm', ...) applied → itertools.permutations ──
    if isinstance(term, OOp) and term.name == 'apply' and len(term.args) == 2:
        fn, arg = term.args
        if isinstance(fn, OFix) and fn.name == 'perm':
            results.append((
                OOp('itertools.permutations', (arg,)),
                'P6_fix_to_permutations',
            ))

    # ── itertools.groupby(sorted(xs, key=f), key=f) → fold grouping ──
    if isinstance(term, OOp) and term.name == 'itertools.groupby' and len(term.args) == 2:
        sorted_xs, f = term.args
        if isinstance(sorted_xs, OOp) and sorted_xs.name == 'sorted_key' and len(sorted_xs.args) == 2:
            xs = sorted_xs.args[0]
            # fold[group_collect](defaultdict(list), xs) using key f
            fold_group = OFold(
                'group_collect',
                OOp('defaultdict_list', (f,)),
                xs,
            )
            results.append((fold_group, 'P6_groupby_to_fold'))

    # ── fold[group_collect] → itertools.groupby(sorted(...)) ──
    if isinstance(term, OFold) and term.op_name == 'group_collect':
        if isinstance(term.init, OOp) and term.init.name == 'defaultdict_list' and len(term.init.args) == 1:
            f = term.init.args[0]
            xs = term.collection
            sorted_xs = OOp('sorted_key', (xs, f))
            results.append((
                OOp('itertools.groupby', (sorted_xs, f)),
                'P6_fold_to_groupby',
            ))

    # ── itertools.accumulate(xs, op) → prefix folds ──
    if isinstance(term, OOp) and term.name == 'itertools.accumulate' and len(term.args) == 2:
        xs, op = term.args
        # [reduce(op, xs[:i+1]) for i in range(len(xs))]
        prefix_folds = OMap(
            OLam(('i',), OFold(
                'reduce_op',
                OOp('apply', (op, OOp('getitem', (xs, OLit(0))))),
                OOp('getitem', (xs, OOp('slice', (OLit(1), OOp('add', (OVar('i'), OLit(1))))))),
            )),
            OOp('range', (OOp('len', (xs,)),)),
        )
        results.append((prefix_folds, 'P6_accumulate_to_prefix_folds'))

    # ── itertools.starmap(f, pairs) → [f(*p) for p in pairs] ──
    if isinstance(term, OOp) and term.name == 'itertools.starmap' and len(term.args) == 2:
        f, pairs = term.args
        mapped = OMap(
            OLam(('p',), OOp('apply_star', (f, OVar('p')))),
            pairs,
        )
        results.append((mapped, 'P6_starmap_to_map'))

    # ── OMap with apply_star → itertools.starmap ──
    if isinstance(term, OMap) and isinstance(term.transform, OLam):
        lam = term.transform
        if (isinstance(lam.body, OOp) and lam.body.name == 'apply_star'
                and len(lam.body.args) == 2):
            f = lam.body.args[0]
            pairs = term.collection
            results.append((
                OOp('itertools.starmap', (f, pairs)),
                'P6_map_to_starmap',
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse axiom
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply P6 in reverse: expanded forms → itertools calls.

    Inverse rewrites are already embedded in apply() as bidirectional
    rules; this function filters for only the reverse direction.
    """
    results = apply(term, ctx)
    inverse_labels = {
        'P6_add_to_chain',
        'P6_flatten_to_chain_from_iterable',
        'P6_index_loop_to_combinations',
        'P6_fix_to_permutations',
        'P6_fold_to_groupby',
        'P6_map_to_starmap',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if P6 is potentially applicable to *term*."""
    if isinstance(term, OOp):
        if term.name in ('itertools.chain', 'itertools.chain.from_iterable',
                         'itertools.product', 'itertools.combinations',
                         'itertools.permutations', 'itertools.groupby',
                         'itertools.accumulate', 'itertools.starmap',
                         'combinations_index_loop', 'flatten'):
            return True
        # add can be chain inverse
        if term.name == 'add' and len(term.args) == 2:
            return True
        # apply(OFix('perm', ...), ...) pattern
        if term.name == 'apply' and len(term.args) == 2:
            if isinstance(term.args[0], OFix) and term.args[0].name == 'perm':
                return True
    if isinstance(term, OFold) and term.op_name == 'group_collect':
        return True
    # OMap with apply_star → starmap
    if isinstance(term, OMap) and isinstance(term.transform, OLam):
        if isinstance(term.transform.body, OOp) and term.transform.body.name == 'apply_star':
            return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score how relevant P6 is for bridging *source* → *target*.

    Returns a float in [0, 1].
    """
    sc = source.canon()
    tc = target.canon()

    itertools_kws = ('itertools.chain', 'itertools.product',
                     'itertools.combinations', 'itertools.permutations',
                     'itertools.groupby', 'itertools.accumulate',
                     'itertools.starmap', 'chain.from_iterable')
    expanded_kws = ('flatten', 'combinations_index_loop', 'group_collect',
                    'apply_star', 'perm')

    has_itertools_s = any(kw in sc for kw in itertools_kws)
    has_itertools_t = any(kw in tc for kw in itertools_kws)
    has_expanded_s = any(kw in sc for kw in expanded_kws)
    has_expanded_t = any(kw in tc for kw in expanded_kws)

    # One side itertools, other side expanded → high relevance
    if has_itertools_s and has_expanded_t:
        return 0.95
    if has_itertools_t and has_expanded_s:
        return 0.95

    # Both sides have itertools or expanded → moderate
    if has_itertools_s != has_itertools_t:
        return 0.85
    if has_expanded_s != has_expanded_t:
        return 0.80

    # Some itertools signal on at least one side
    if has_itertools_s or has_itertools_t:
        return 0.50
    if has_expanded_s or has_expanded_t:
        return 0.40

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
    ys = OVar('ys')
    xss = OVar('xss')
    f = OVar('f')
    op = OVar('op')
    pairs = OVar('pairs')
    a = OVar('a')
    b = OVar('b')

    # ── chain(a, b) → a + b ──
    print("P6: chain(a, b) → add ...")
    chain_term = OOp('itertools.chain', (a, b))
    r = apply(chain_term, ctx)
    _assert(any(lbl == 'P6_chain_to_add' for _, lbl in r), "chain→add")
    add_result = [t for t, l in r if l == 'P6_chain_to_add'][0]
    _assert(isinstance(add_result, OOp) and add_result.name == 'add', "result is add")

    # ── a + b → chain(a, b) ──
    print("P6: add → chain ...")
    add_term = OOp('add', (a, b))
    r2 = apply(add_term, ctx)
    _assert(any(lbl == 'P6_add_to_chain' for _, lbl in r2), "add→chain")

    # ── chain.from_iterable → flatten ──
    print("P6: chain.from_iterable → flatten ...")
    cfi_term = OOp('itertools.chain.from_iterable', (xss,))
    r3 = apply(cfi_term, ctx)
    _assert(any(lbl == 'P6_chain_from_iterable_to_flatten' for _, lbl in r3),
            "chain.from_iterable→flatten")

    # ── flatten → chain.from_iterable ──
    print("P6: flatten → chain.from_iterable ...")
    flat_term = OOp('flatten', (xss,))
    r4 = apply(flat_term, ctx)
    _assert(any(lbl == 'P6_flatten_to_chain_from_iterable' for _, lbl in r4),
            "flatten→chain.from_iterable")

    # ── product(xs, ys) → nested comp ──
    print("P6: product → nested comprehension ...")
    prod_term = OOp('itertools.product', (xs, ys))
    r5 = apply(prod_term, ctx)
    _assert(any(lbl == 'P6_product_to_nested_comp' for _, lbl in r5),
            "product→nested comp")

    # ── combinations(xs, 2) → index loop ──
    print("P6: combinations(xs, 2) → index loop ...")
    comb_term = OOp('itertools.combinations', (xs, OLit(2)))
    r6 = apply(comb_term, ctx)
    _assert(any(lbl == 'P6_combinations2_to_index_loop' for _, lbl in r6),
            "combinations(2)→index loop")

    # ── index loop → combinations ──
    print("P6: index_loop → combinations ...")
    idx_term = OOp('combinations_index_loop', (xs, OLit(2)))
    r7 = apply(idx_term, ctx)
    _assert(any(lbl == 'P6_index_loop_to_combinations' for _, lbl in r7),
            "index loop→combinations")

    # ── permutations → fix ──
    print("P6: permutations → fix ...")
    perm_term = OOp('itertools.permutations', (xs,))
    r8 = apply(perm_term, ctx)
    _assert(any(lbl == 'P6_permutations_to_fix' for _, lbl in r8),
            "permutations→fix")

    # ── fix(perm) → permutations ──
    print("P6: fix(perm) → permutations ...")
    perm_results = [(t, l) for t, l in r8 if l == 'P6_permutations_to_fix']
    if perm_results:
        fix_applied = perm_results[0][0]
        r8b = apply(fix_applied, ctx)
        _assert(any(lbl == 'P6_fix_to_permutations' for _, lbl in r8b),
                "fix(perm)→permutations roundtrip")

    # ── groupby(sorted_key(xs, f), f) → fold ──
    print("P6: groupby → fold ...")
    groupby_term = OOp('itertools.groupby', (OOp('sorted_key', (xs, f)), f))
    r9 = apply(groupby_term, ctx)
    _assert(any(lbl == 'P6_groupby_to_fold' for _, lbl in r9),
            "groupby→fold")

    # ── fold[group_collect] → groupby ──
    print("P6: fold[group_collect] → groupby ...")
    fold_group = OFold('group_collect', OOp('defaultdict_list', (f,)), xs)
    r10 = apply(fold_group, ctx)
    _assert(any(lbl == 'P6_fold_to_groupby' for _, lbl in r10),
            "fold→groupby")

    # ── accumulate(xs, op) → prefix folds ──
    print("P6: accumulate → prefix folds ...")
    acc_term = OOp('itertools.accumulate', (xs, op))
    r11 = apply(acc_term, ctx)
    _assert(any(lbl == 'P6_accumulate_to_prefix_folds' for _, lbl in r11),
            "accumulate→prefix folds")

    # ── starmap(f, pairs) → map ──
    print("P6: starmap → map ...")
    starmap_term = OOp('itertools.starmap', (f, pairs))
    r12 = apply(starmap_term, ctx)
    _assert(any(lbl == 'P6_starmap_to_map' for _, lbl in r12),
            "starmap→map")

    # ── map(apply_star) → starmap ──
    print("P6: map(apply_star) → starmap ...")
    map_star = OMap(
        OLam(('p',), OOp('apply_star', (f, OVar('p')))),
        pairs,
    )
    r13 = apply(map_star, ctx)
    _assert(any(lbl == 'P6_map_to_starmap' for _, lbl in r13),
            "map(apply_star)→starmap")

    # ── recognizes() ──
    print("P6: recognizes ...")
    _assert(recognizes(chain_term), "recognizes chain")
    _assert(recognizes(cfi_term), "recognizes chain.from_iterable")
    _assert(recognizes(prod_term), "recognizes product")
    _assert(recognizes(comb_term), "recognizes combinations")
    _assert(recognizes(perm_term), "recognizes permutations")
    _assert(recognizes(groupby_term), "recognizes groupby")
    _assert(recognizes(acc_term), "recognizes accumulate")
    _assert(recognizes(starmap_term), "recognizes starmap")
    _assert(recognizes(flat_term), "recognizes flatten")
    _assert(recognizes(idx_term), "recognizes combinations_index_loop")
    _assert(recognizes(map_star), "recognizes map(apply_star)")
    _assert(not recognizes(OOp('Counter', (xs,))), "does not recognise Counter")

    # ── relevance_score ──
    print("P6: relevance_score ...")
    score = relevance_score(chain_term, add_term)
    _assert(score > 0.8, f"chain↔add score={score:.2f} > 0.8")
    score2 = relevance_score(starmap_term, map_star)
    _assert(score2 > 0.4, f"starmap↔map score={score2:.2f} > 0.4")
    low = relevance_score(OOp('Counter', (xs,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("P6: apply_inverse ...")
    inv = apply_inverse(add_term, ctx)
    _assert(len(inv) >= 1, "inverse of add produces chain")
    _assert(inv[0][1] == 'P6_add_to_chain', "inverse label")
    inv2 = apply_inverse(map_star, ctx)
    _assert(any(lbl == 'P6_map_to_starmap' for _, lbl in inv2), "map→starmap inverse")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  P6 itertools: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
