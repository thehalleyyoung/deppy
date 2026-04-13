"""D16: Memoization / DP Equivalences (Theorem 22.2.1).

Naive recursive → memoized → bottom-up DP → space-optimised.

Mathematical foundation:
  All four strategies compute the same fixed point of a recurrence
  equation  f = Φ(f).  By the Knaster–Tarski theorem, the least
  fixed point lfp(Φ) is unique.  The strategies differ only in
  *evaluation order* and *caching strategy*:

    • Naive recursive: evaluate lfp(Φ) lazily, recomputing sub-problems.
    • Memoized (top-down): evaluate lfp(Φ) lazily, cache results.
    • Bottom-up DP: evaluate lfp(Φ) eagerly in dependency order.
    • Space-optimised: bottom-up with sliding window over the table.

  Two OFix terms with the same structural recurrence (after
  canonicalisation) compute the same lfp and are thus equal.

Covers:
  • Recurrence canonicalisation: alpha-normalise, sort commutative args,
    strip accumulator wrappers, normalise table shapes
  • OFix ↔ OFold (bottom-up table fill)
  • Space-optimised sliding window detection
  • Fibonacci-style recurrence normalisation
"""
from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple, Union

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)


# ═══════════════════════════════════════════════════════════
# Axiom metadata
# ═══════════════════════════════════════════════════════════

AXIOM_NAME = 'D16_memo_dp'
AXIOM_CATEGORY = 'algorithm_strategy'  # §22

SOUNDNESS_PROOF = """
Theorem 22.2.1 (Evaluation-Order Independence):
  Let Φ : (X → Y) → (X → Y) be a monotone endofunctor on the
  lattice of partial functions X ⇀ Y.  Then:
    lfp(Φ) computed top-down with memo  =  lfp(Φ) computed bottom-up

Proof:
  By Knaster–Tarski, lfp(Φ) is the unique least fixed point.
  Both top-down memo and bottom-up DP compute iterates
  Φ⁰(⊥) ⊑ Φ¹(⊥) ⊑ ... converging to lfp(Φ).
  Top-down evaluates on demand (lazy); bottom-up evaluates
  in topological order (eager).  Both converge to the same
  fixed point since Φ is monotone on a CPO.  ∎

Corollary: Space-optimised DP (sliding window) is also correct
  when the recurrence depends only on a bounded window of
  previous values.
"""

COMPOSES_WITH = ['D17_assoc', 'D1_fold_unfold', 'D20_spec']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'Recurrence normalisation',
        'before': "fix[abc](add($n, sub($n, 1)))",
        'after': "fix[<hash>](add($n, sub($n, 1)))",
        'axiom': 'D16_recurrence_normalize',
    },
    {
        'name': 'DP table to fix-point',
        'before': "fold[update_table](list(), range(n))",
        'after': "fix[<hash>](list())",
        'axiom': 'D16_dp_table_to_fix',
    },
    {
        'name': 'Fix-point to bottom-up fold',
        'before': "fix[fib](case(...))",
        'after': "fold[fib_step](init, range(n))",
        'axiom': 'D16_fix_to_dp_fold',
    },
    {
        'name': 'Space optimisation',
        'before': "fold[update_row](table, range(n))",
        'after': "fold[update_window](window, range(n))",
        'axiom': 'D16_space_optimise',
    },
]

# ── Commutative operations (for argument-order normalisation) ──
COMMUTATIVE_OPS: FrozenSet[str] = frozenset({
    'add', '.add', 'iadd', 'mul', '.mul', 'imul', 'mult',
    'and', 'or', 'bitor', 'bitand', 'bitxor',
    'min', 'max', 'gcd', 'lcm',
})


# ═══════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════

@dataclass
class FiberCtx:
    """Lightweight fiber context for standalone axiom evaluation."""
    param_duck_types: Dict[str, str] = field(default_factory=dict)


def _hash(s: str) -> str:
    return hashlib.md5(s.encode()).hexdigest()[:8]


def _sort_commutative_subexprs(canon: str) -> str:
    """Sort arguments of known-commutative ops in a canonical string."""
    for op in ('add', 'mul', 'mult', 'and', 'or', 'min', 'max',
               'bitor', 'bitand', 'bitxor', 'gcd', 'lcm'):
        pattern = rf'{op}\(([^,)]+),([^)]+)\)'
        def _sorter(m: re.Match, _op: str = op) -> str:
            a, b = m.group(1), m.group(2)
            if a > b:
                a, b = b, a
            return f'{_op}({a},{b})'
        canon = re.sub(pattern, _sorter, canon)
    return canon


def _contains_var(term: OTerm, name: str) -> bool:
    """Check whether *term* references a variable named *name*."""
    if isinstance(term, OVar):
        return term.name == name
    if isinstance(term, OOp):
        return any(_contains_var(a, name) for a in term.args)
    if isinstance(term, OCase):
        return (_contains_var(term.test, name)
                or _contains_var(term.true_branch, name)
                or _contains_var(term.false_branch, name))
    if isinstance(term, OFold):
        return _contains_var(term.init, name) or _contains_var(term.collection, name)
    if isinstance(term, OFix):
        return _contains_var(term.body, name)
    if isinstance(term, OLam):
        return name not in term.params and _contains_var(term.body, name)
    if isinstance(term, OSeq):
        return any(_contains_var(e, name) for e in term.elements)
    if isinstance(term, OMap):
        r = _contains_var(term.transform, name) or _contains_var(term.collection, name)
        if term.filter_pred:
            r = r or _contains_var(term.filter_pred, name)
        return r
    if isinstance(term, OCatch):
        return _contains_var(term.body, name) or _contains_var(term.default, name)
    if isinstance(term, OQuotient):
        return _contains_var(term.inner, name)
    if isinstance(term, ODict):
        return any(_contains_var(k, name) or _contains_var(v, name)
                   for k, v in term.pairs)
    if isinstance(term, OAbstract):
        return any(_contains_var(a, name) for a in term.inputs)
    return False


# ═══════════════════════════════════════════════════════════
# Recurrence canonicalisation
# ═══════════════════════════════════════════════════════════

def canonicalize_recurrence(term: OFix) -> Optional[OFix]:
    """Canonicalize a recurrence for D16 equivalence.

    Steps:
      1. Alpha-normalise bound variables to positional indices.
      2. Sort sub-expressions under commutative operators.
      3. Strip accumulator wrappers (bottom-up DP tables).
      4. Normalise table shapes: dp[i][j] ↔ dp[(i,j)].
      5. Hash the resulting structural signature.
    """
    body_canon = term.body.canon()

    # Step 1: alpha-normalise
    structural = re.sub(r'\$\w+', '$_', body_canon)

    # Step 2: sort commutative subexprs
    structural = _sort_commutative_subexprs(structural)

    # Step 3: strip accumulator wrappers
    structural = re.sub(r'fold\[\w+\]\(([^,]+),', r'fix_body(\1,', structural)

    # Step 4: normalise table shapes
    structural = re.sub(
        r'getitem\(getitem\(\$_,(\$_)\),(\$_)\)',
        r'getitem($_, tuple(\1,\2))',
        structural,
    )

    new_name = _hash(structural)
    if new_name != term.name:
        return OFix(new_name, term.body)
    return None


def _extract_recurrence_depth(term: OFix) -> int:
    """Estimate recurrence depth (number of recursive call levels)."""
    canon = term.body.canon()
    return canon.count(f'fix[{term.name}]')


def _has_sliding_window_shape(term: OFold) -> bool:
    """Detect if a fold is a sliding-window DP pattern.

    Pattern: fold body references only a fixed number of previous
    values (e.g., dp[i-1], dp[i-2] but not dp[0]).
    """
    canon = term.collection.canon() if term.collection else ''
    init_canon = term.init.canon() if term.init else ''
    # Heuristic: window patterns have getitem with subtraction indices
    has_sub_index = bool(re.search(r'getitem\([^,]+,sub\(', canon + init_canon))
    has_range = 'range' in canon
    return has_sub_index and has_range


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D16 memo/DP equivalences to *term*."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── Recurrence normalisation on OFix ──
    if isinstance(term, OFix):
        canonical = canonicalize_recurrence(term)
        if canonical is not None and canonical.name != term.name:
            results.append((canonical, 'D16_recurrence_normalize'))

    # ── OFix → OFold (fix-point to bottom-up DP) ──
    if isinstance(term, OFix):
        if isinstance(term.body, OCase):
            # fix[f](case(guard, base, step))
            # → fold[f_step](base, range(n)) where n is from the guard
            guard = term.body.test
            base = term.body.true_branch
            range_bound = _extract_range_bound(guard)
            if range_bound is not None:
                results.append((
                    OFold(f'{term.name}_step', base,
                          OOp('range', (range_bound,))),
                    'D16_fix_to_dp_fold',
                ))

    # ── OFold (bottom-up DP table fill) → OFix ──
    if isinstance(term, OFold):
        if isinstance(term.collection, OOp) and term.collection.name == 'range':
            if isinstance(term.init, OOp) and term.init.name in (
                'list', 'dict', 'array', 'defaultdict',
            ):
                structural = re.sub(r'\$\w+', '$_', term.collection.canon())
                results.append((
                    OFix(_hash(structural), term.init),
                    'D16_dp_table_to_fix',
                ))

    # ── Space optimisation: full table → sliding window ──
    if isinstance(term, OFold) and _has_sliding_window_shape(term):
        window_init = OOp('deque', (term.init, OLit(2)))
        results.append((
            OFold(term.op_name + '_window', window_init, term.collection),
            'D16_space_optimise',
        ))

    # ── Memoised OFix → same OFix (memo is semantically invisible) ──
    if isinstance(term, OOp) and term.name == 'lru_cache':
        if len(term.args) == 1 and isinstance(term.args[0], OFix):
            results.append((term.args[0], 'D16_strip_memo'))

    # ── functools.cache / functools.lru_cache wrapping ──
    if isinstance(term, OOp) and term.name in ('cache', 'functools.cache',
                                                 'functools.lru_cache'):
        if len(term.args) >= 1:
            results.append((term.args[0], 'D16_strip_cache_decorator'))

    # ── Two OFix with same recurrence structure → equate names ──
    # This is the core of D16: if two fix-points have the same
    # canonical body, they compute the same function.
    # (Handled by canonicalize_recurrence above.)

    # ── Fibonacci-style recurrence: detect and normalise ──
    if isinstance(term, OFix) and isinstance(term.body, OCase):
        body = term.body
        if _is_fibonacci_recurrence(body, term.name):
            results.append((
                OFold('fib_step', OSeq((OLit(0), OLit(1))),
                      OOp('range', (OVar('n'),))),
                'D16_fibonacci_to_dp',
            ))

    return results


def _extract_range_bound(guard: OTerm) -> Optional[OTerm]:
    """Extract a range bound from a recursion guard."""
    if not isinstance(guard, OOp) or len(guard.args) != 2:
        return None
    a, b = guard.args
    if guard.name in ('le', 'lte', 'eq'):
        if isinstance(b, OLit) and b.value == 0:
            return a
        return b
    if guard.name in ('lt',):
        return b
    if guard.name in ('gt', 'gte'):
        if isinstance(b, OLit) and b.value == 0:
            return a
    return None


def _is_fibonacci_recurrence(body: OCase, fix_name: str) -> bool:
    """Detect f(n) = f(n-1) + f(n-2) pattern."""
    canon = body.canon()
    # Must have two recursive calls with offsets -1 and -2
    if canon.count(f'fix[{fix_name}]') >= 2:
        if 'sub' in canon and 'add' in canon:
            if '1' in canon and '2' in canon:
                return True
    return False


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D16 in reverse direction."""
    results = apply(term, ctx)
    inverse_labels = {
        'D16_dp_table_to_fix',
        'D16_strip_memo',
        'D16_strip_cache_decorator',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D16 is potentially applicable."""
    if isinstance(term, OFix):
        return True
    if isinstance(term, OFold):
        if isinstance(term.collection, OOp) and term.collection.name == 'range':
            return True
    if isinstance(term, OOp):
        if term.name in ('lru_cache', 'cache', 'functools.cache',
                         'functools.lru_cache'):
            return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D16 relevance for bridging *source* → *target*."""
    sc = source.canon()
    tc = target.canon()

    has_fix_s = 'fix[' in sc
    has_fix_t = 'fix[' in tc
    has_fold_s = 'fold[' in sc
    has_fold_t = 'fold[' in tc
    has_memo_s = 'lru_cache' in sc or 'cache(' in sc
    has_memo_t = 'lru_cache' in tc or 'cache(' in tc

    # Both fix-points → high relevance (recurrence normalisation)
    if has_fix_s and has_fix_t:
        return 0.90
    # One fix, one fold → very high (memo↔DP)
    if (has_fix_s and has_fold_t) or (has_fold_s and has_fix_t):
        return 0.95
    # Memo wrapping
    if has_memo_s or has_memo_t:
        return 0.80
    # One has fix, other doesn't
    if has_fix_s != has_fix_t:
        return 0.50
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

    # ── Recurrence normalisation ──
    print("D16: recurrence normalisation ...")
    fix1 = OFix('abc', OOp('add', (OVar('n'), OOp('sub', (OVar('n'), OLit(1))))))
    r = apply(fix1, ctx)
    _assert(any(lbl == 'D16_recurrence_normalize' for _, lbl in r),
            "normalises fix name")
    if r:
        norm = r[0][0]
        _assert(isinstance(norm, OFix), "result is OFix")
        _assert(norm.name != 'abc', "name changed")

    # ── Two different names, same structure → same canonical name ──
    print("D16: structural equivalence ...")
    fix2 = OFix('xyz', OOp('add', (OVar('n'), OOp('sub', (OVar('n'), OLit(1))))))
    r2 = apply(fix2, ctx)
    _assert(len(r2) >= 1, "second fix also normalises")
    if r and r2:
        _assert(r[0][0].canon() == r2[0][0].canon(),
                "same structure → same canonical form")

    # ── Fix → DP fold ──
    print("D16: fix → DP fold ...")
    fix3 = OFix('f', OCase(
        OOp('le', (OVar('n'), OLit(0))),
        OLit(1),
        OOp('mul', (OVar('n'), OFix('f', OOp('sub', (OVar('n'), OLit(1)))))),
    ))
    r3 = apply(fix3, ctx)
    _assert(any(lbl == 'D16_fix_to_dp_fold' for _, lbl in r3), "fix→DP fold")

    # ── DP table → fix ──
    print("D16: DP table → fix ...")
    dp_fold = OFold('update', OOp('list', ()), OOp('range', (OVar('n'),)))
    r4 = apply(dp_fold, ctx)
    _assert(any(lbl == 'D16_dp_table_to_fix' for _, lbl in r4), "DP→fix")

    # ── Strip memo ──
    print("D16: strip memo ...")
    memo_fix = OOp('lru_cache', (fix1,))
    r5 = apply(memo_fix, ctx)
    _assert(any(lbl == 'D16_strip_memo' for _, lbl in r5), "strip memo")

    # ── Strip cache decorator ──
    print("D16: strip cache ...")
    cache_fix = OOp('functools.cache', (fix1,))
    r6 = apply(cache_fix, ctx)
    _assert(any(lbl == 'D16_strip_cache_decorator' for _, lbl in r6), "strip cache")

    # ── Fibonacci detection ──
    print("D16: fibonacci detection ...")
    fib_fix = OFix('fib', OCase(
        OOp('le', (OVar('n'), OLit(1))),
        OVar('n'),
        OOp('add', (
            OFix('fib', OOp('sub', (OVar('n'), OLit(1)))),
            OFix('fib', OOp('sub', (OVar('n'), OLit(2)))),
        )),
    ))
    r7 = apply(fib_fix, ctx)
    _assert(any(lbl == 'D16_fibonacci_to_dp' for _, lbl in r7),
            "fibonacci detected")

    # ── Canonicalise commutative subexprs ──
    print("D16: commutative normalisation ...")
    s1 = _sort_commutative_subexprs('add($b,$a)')
    _assert(s1 == 'add($a,$b)', f"sorted: {s1}")

    s2 = _sort_commutative_subexprs('mul($z,$a)')
    _assert(s2 == 'mul($a,$z)', f"sorted mul: {s2}")

    # ── recognizes ──
    print("D16: recognizes ...")
    _assert(recognizes(fix1), "recognizes OFix")
    _assert(recognizes(dp_fold), "recognizes DP fold")
    _assert(recognizes(memo_fix), "recognizes memo-wrapped")
    _assert(not recognizes(OOp('sorted', (OVar('xs'),))), "does not recognise sorted")

    # ── relevance_score ──
    print("D16: relevance_score ...")
    score = relevance_score(fix1, dp_fold)
    _assert(score > 0.8, f"fix↔fold score={score:.2f} > 0.8")
    low = relevance_score(OOp('sorted', (OVar('xs'),)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("D16: apply_inverse ...")
    inv = apply_inverse(dp_fold, ctx)
    _assert(len(inv) >= 1, "inverse dp→fix")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  D16 memo_dp: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
