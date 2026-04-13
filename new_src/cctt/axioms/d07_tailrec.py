"""D7 Axiom: Tail Recursion Elimination & Dead Code Elimination.

Transforms OFix terms in tail position into OFold with accumulators,
and eliminates dead code (constant guards, identity operations,
unreachable branches, unused lambda parameters).

Mathematical basis: A tail-recursive function
    fix[h](case(guard, acc, h(step(n), op(acc, elem))))
is isomorphic to
    fold[op](init, range)
because the recursive call is in tail position — the continuation
is the identity, so the call stack can be collapsed to a single
accumulator frame.  This is the CPS/defunctionalization adjunction
restricted to the identity continuation (§10, Definition 4.9).

Dead code elimination follows from the observation that if a
sub-expression cannot affect the denotation (e.g. a branch guarded
by a constant False), removing it preserves the Čech cohomology
class of the program — i.e. the bug-equivalence class is unchanged.
"""
from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)
from cctt.path_search import FiberCtx

# ═══════════════════════════════════════════════════════════
# Constants
# ═══════════════════════════════════════════════════════════

AXIOM_NAME = "D7_tailrec"
AXIOM_CATEGORY = "control_flow"

COMPOSES_WITH = ["D1_fold_unfold", "D2_beta", "D5_fold_universal", "D8_section_merge"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (D7 Tail Recursion Elimination).

Let f = fix[h](case(g, acc, h(step(n), op(acc, elem))))
be a tail-recursive function with accumulator.

Claim:  f ≡ fold[op](init, collection)  in the denotation category.

Proof sketch:
  1. The recursive call h(step(n), op(acc, elem)) is in tail position:
     the continuation after the call is the identity function.
  2. By the CPS theorem (§10.3), when the continuation is id,
     the fix-point is equivalent to a left fold over the iteration
     domain with the accumulator threaded through op.
  3. The base case (guard = True → acc) provides the initial value.
  4. The step (guard = False → h(step(n), op(acc, elem))) provides
     the fold body: apply op to acc and the current element.
  5. By the universal property of folds (Theorem 4.8), this is the
     unique catamorphism fold[op](init, collection).

Dead code soundness:
  - case(True, A, B) → A : denotation of case with constant True
    test is defined as the denotation of A (by case semantics).
  - add(x, 0) → x : 0 is the identity of (ℤ, +).
  - mul(x, 1) → x : 1 is the identity of (ℤ, ×).
  - mul(x, 0) → 0 : absorption law of (ℤ, ×).
  □
"""

EXAMPLES = [
    {
        "name": "factorial_tailrec",
        "before": "fix[fact](case(le(n,0), acc, fact(sub(n,1), mul(acc,n))))",
        "after": "fold[mul](1, range(n))",
        "benchmark": "demo_factorial_iter.py",
    },
    {
        "name": "sum_tailrec",
        "before": "fix[s](case(le(n,0), acc, s(sub(n,1), add(acc,n))))",
        "after": "fold[add](0, range(n))",
        "benchmark": "demo_sum.py",
    },
    {
        "name": "dce_constant_branch",
        "before": "case(True, $x, $y)",
        "after": "$x",
        "benchmark": None,
    },
    {
        "name": "dce_mul_zero",
        "before": "mul($x, 0)",
        "after": "0",
        "benchmark": None,
    },
]


# ═══════════════════════════════════════════════════════════
# OTerm helpers
# ═══════════════════════════════════════════════════════════

def _contains_var(term: OTerm, name: str) -> bool:
    """Check whether *term* references variable *name*."""
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
        if name in term.params:
            return False
        return _contains_var(term.body, name)
    if isinstance(term, OMap):
        r = _contains_var(term.transform, name) or _contains_var(term.collection, name)
        if term.filter_pred is not None:
            r = r or _contains_var(term.filter_pred, name)
        return r
    if isinstance(term, OSeq):
        return any(_contains_var(e, name) for e in term.elements)
    if isinstance(term, OCatch):
        return _contains_var(term.body, name) or _contains_var(term.default, name)
    if isinstance(term, OQuotient):
        return _contains_var(term.inner, name)
    if isinstance(term, OAbstract):
        return any(_contains_var(a, name) for a in term.inputs)
    if isinstance(term, ODict):
        return any(_contains_var(k, name) or _contains_var(v, name)
                   for k, v in term.pairs)
    return False


def _extract_free_vars(term: OTerm) -> Set[str]:
    """All free variable names in *term*."""
    if isinstance(term, OVar):
        return {term.name}
    if isinstance(term, (OLit, OUnknown)):
        return set()
    if isinstance(term, OOp):
        r: Set[str] = set()
        for a in term.args:
            r |= _extract_free_vars(a)
        return r
    if isinstance(term, OCase):
        return (_extract_free_vars(term.test)
                | _extract_free_vars(term.true_branch)
                | _extract_free_vars(term.false_branch))
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
    if isinstance(term, OMap):
        r3 = _extract_free_vars(term.transform) | _extract_free_vars(term.collection)
        if term.filter_pred:
            r3 |= _extract_free_vars(term.filter_pred)
        return r3
    if isinstance(term, OCatch):
        return _extract_free_vars(term.body) | _extract_free_vars(term.default)
    if isinstance(term, OQuotient):
        return _extract_free_vars(term.inner)
    if isinstance(term, OAbstract):
        r4: Set[str] = set()
        for a in term.inputs:
            r4 |= _extract_free_vars(a)
        return r4
    if isinstance(term, ODict):
        r5: Set[str] = set()
        for k, v in term.pairs:
            r5 |= _extract_free_vars(k) | _extract_free_vars(v)
        return r5
    return set()


def _term_size(term: OTerm) -> int:
    """Number of nodes in *term*."""
    if isinstance(term, (OVar, OLit, OUnknown)):
        return 1
    if isinstance(term, OOp):
        return 1 + sum(_term_size(a) for a in term.args)
    if isinstance(term, OCase):
        return 1 + _term_size(term.test) + _term_size(term.true_branch) + _term_size(term.false_branch)
    if isinstance(term, OFold):
        return 1 + _term_size(term.init) + _term_size(term.collection)
    if isinstance(term, OFix):
        return 1 + _term_size(term.body)
    if isinstance(term, OLam):
        return 1 + _term_size(term.body)
    if isinstance(term, OMap):
        s = 1 + _term_size(term.transform) + _term_size(term.collection)
        if term.filter_pred is not None:
            s += _term_size(term.filter_pred)
        return s
    if isinstance(term, OSeq):
        return 1 + sum(_term_size(e) for e in term.elements)
    if isinstance(term, OCatch):
        return 1 + _term_size(term.body) + _term_size(term.default)
    if isinstance(term, OQuotient):
        return 1 + _term_size(term.inner)
    if isinstance(term, OAbstract):
        return 1 + sum(_term_size(a) for a in term.inputs)
    if isinstance(term, ODict):
        return 1 + sum(_term_size(k) + _term_size(v) for k, v in term.pairs)
    return 1


def _extract_range_from_guard(guard: OTerm) -> Optional[OTerm]:
    """Derive a range(...) from a loop guard."""
    if not isinstance(guard, OOp) or len(guard.args) != 2:
        return None
    a, b = guard.args
    if guard.name in ('le', 'lte'):
        if isinstance(b, OLit) and b.value == 0:
            return OOp('range', (a,))
    if guard.name in ('lt',):
        return OOp('range', (b,))
    if guard.name in ('gt', 'gte'):
        if isinstance(b, OLit) and b.value == 0:
            return OOp('range', (a,))
    if guard.name in ('eq',):
        if isinstance(b, OLit) and b.value == 0:
            return OOp('range', (a,))
    return None


# ═══════════════════════════════════════════════════════════
# Tail recursion detection
# ═══════════════════════════════════════════════════════════

def _is_tail_recursive(term: OFix) -> bool:
    """Check whether the OFix body has its recursive call in tail position.

    A call is in tail position when it is the last operation —
    no further computation wraps the recursive invocation.
    """
    body = term.body
    if not isinstance(body, OCase):
        return False
    step = body.false_branch
    # Direct tail call: step = h(args...)
    if isinstance(step, OOp) and step.name == term.name:
        return True
    # Tail call inside another case
    if isinstance(step, OCase):
        return (_is_tail_call(step.true_branch, term.name) and
                _is_tail_call(step.false_branch, term.name))
    return False


def _is_tail_call(term: OTerm, fix_name: str) -> bool:
    """Check if *term* is a direct call to *fix_name* (tail position)."""
    if isinstance(term, OOp) and term.name == fix_name:
        return True
    if isinstance(term, OVar) and term.name == fix_name:
        return True
    if not _contains_var(term, fix_name):
        return True  # base case — no recursive call at all
    return False


def _try_extract_fold_from_tailrec(term: OFix) -> Optional[OTerm]:
    """Extract OFold from a tail-recursive OFix with accumulator.

    Pattern:
        fix[h](case(guard, acc, h(step(n), op(acc, elem))))
        → fold[op](init, collection)

    Also handles:
        fix[h](case(guard, base, op(x, h(sub(x,1)))))
        fix[h](case(guard, base, h(sub(n,1), op(acc, elem))))
        fix[h](case(guard, acc, h(rest)))  (generic tail call)
    """
    if not isinstance(term, OFix):
        return None
    body = term.body
    if not isinstance(body, OCase):
        return None

    guard = body.test
    base_val = body.true_branch
    step = body.false_branch

    collection = _extract_range_from_guard(guard)
    if collection is None:
        collection = OVar('$p0')

    # Pattern A: step = op(non_rec, rec_call) or op(rec_call, non_rec)
    if isinstance(step, OOp) and len(step.args) == 2:
        a, b = step.args
        has_rec_a = _contains_var(a, term.name)
        has_rec_b = _contains_var(b, term.name)
        if has_rec_a != has_rec_b:
            return OFold(step.name, base_val, collection)

    # Pattern B: step = h(step_arg, op(acc, elem))
    if isinstance(step, OOp) and step.name == term.name:
        for arg in step.args:
            if isinstance(arg, OOp) and len(arg.args) == 2:
                return OFold(arg.name, base_val, collection)

    # Pattern C: step is just the fix variable (trivial tail)
    if isinstance(step, OVar) and step.name == term.name:
        return OFold(term.name, base_val, collection)

    return None


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D7: Tail recursion elimination and dead code elimination.

    Handles:
      1. OFix in tail position → OFold with accumulator
      2. case(True, A, B) → A, case(False, A, B) → B
      3. case(g, x, x) → x  (identical branches)
      4. Redundant nested guard elimination
      5. Identity elimination: add(x,0)→x, mul(x,1)→x, mul(x,0)→0
      6. Unused lambda parameter elimination
      7. Duplicate sequence element deduplication
    """
    results: List[Tuple[OTerm, str]] = []

    # ── Tail recursion → fold ──
    if isinstance(term, OFix):
        fold = _try_extract_fold_from_tailrec(term)
        if fold is not None:
            results.append((fold, 'D7_tailrec_to_fold'))

    # ── Dead code in case expressions ──
    if isinstance(term, OCase):
        # Constant guard
        if isinstance(term.test, OLit):
            if term.test.value is True:
                results.append((term.true_branch, 'D7_dce_true'))
            elif term.test.value is False:
                results.append((term.false_branch, 'D7_dce_false'))
        # Identical branches
        if term.true_branch.canon() == term.false_branch.canon():
            results.append((term.true_branch, 'D7_dce_identical'))
        # Redundant nested guard: case(g, A, case(g, B, C)) → case(g, A, C)
        if isinstance(term.false_branch, OCase):
            inner = term.false_branch
            if inner.test.canon() == term.test.canon():
                results.append((
                    OCase(term.test, term.true_branch, inner.false_branch),
                    'D7_dce_redundant_guard',
                ))
        # Nested constant: case(g, A, case(True, B, C)) → case(g, A, B)
        if isinstance(term.false_branch, OCase):
            inner = term.false_branch
            if isinstance(inner.test, OLit) and inner.test.value is True:
                results.append((
                    OCase(term.test, term.true_branch, inner.true_branch),
                    'D7_dce_inner_true',
                ))

    # ── Identity operations ──
    if isinstance(term, OOp):
        # Additive identity
        if term.name in ('add', 'iadd') and len(term.args) == 2:
            if isinstance(term.args[1], OLit) and term.args[1].value == 0:
                results.append((term.args[0], 'D7_dce_add_zero'))
            if isinstance(term.args[0], OLit) and term.args[0].value == 0:
                results.append((term.args[1], 'D7_dce_zero_add'))
        # Multiplicative identity / absorption
        if term.name in ('mul', 'imul', 'mult') and len(term.args) == 2:
            if isinstance(term.args[1], OLit) and term.args[1].value == 1:
                results.append((term.args[0], 'D7_dce_mul_one'))
            if isinstance(term.args[0], OLit) and term.args[0].value == 1:
                results.append((term.args[1], 'D7_dce_one_mul'))
            if isinstance(term.args[1], OLit) and term.args[1].value == 0:
                results.append((OLit(0), 'D7_dce_mul_zero'))
            if isinstance(term.args[0], OLit) and term.args[0].value == 0:
                results.append((OLit(0), 'D7_dce_zero_mul'))
        # Boolean identity
        if term.name == 'and' and len(term.args) == 2:
            if isinstance(term.args[0], OLit) and term.args[0].value is True:
                results.append((term.args[1], 'D7_dce_and_true'))
            if isinstance(term.args[1], OLit) and term.args[1].value is True:
                results.append((term.args[0], 'D7_dce_true_and'))
        if term.name == 'or' and len(term.args) == 2:
            if isinstance(term.args[0], OLit) and term.args[0].value is False:
                results.append((term.args[1], 'D7_dce_or_false'))
            if isinstance(term.args[1], OLit) and term.args[1].value is False:
                results.append((term.args[0], 'D7_dce_false_or'))
        # Subtraction of zero
        if term.name in ('sub', 'isub') and len(term.args) == 2:
            if isinstance(term.args[1], OLit) and term.args[1].value == 0:
                results.append((term.args[0], 'D7_dce_sub_zero'))

    # ── Unused lambda parameters ──
    if isinstance(term, OLam):
        used = _extract_free_vars(term.body)
        dead_params = [p for p in term.params if p not in used]
        if dead_params and len(dead_params) < len(term.params):
            live = tuple(p for p in term.params if p in used)
            results.append((OLam(live, term.body), 'D7_dce_unused_param'))

    # ── Duplicate elements in sequences ──
    if isinstance(term, OSeq):
        deduped: List[OTerm] = []
        seen: Set[str] = set()
        changed = False
        for e in term.elements:
            c = e.canon()
            if c not in seen:
                seen.add(c)
                deduped.append(e)
            else:
                changed = True
        if changed:
            results.append((OSeq(tuple(deduped)), 'D7_dce_seq_dedup'))

    return results


# ═══════════════════════════════════════════════════════════
# Recognizer & scoring
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could D7 apply to this term?"""
    if isinstance(term, OFix):
        return True
    if isinstance(term, OCase):
        return True
    if isinstance(term, OOp) and term.name in (
        'add', 'iadd', 'mul', 'imul', 'mult', 'sub', 'isub',
        'and', 'or',
    ):
        return len(term.args) == 2
    if isinstance(term, OLam):
        return True
    if isinstance(term, OSeq):
        return len(term.elements) >= 2
    return False


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Heuristic 0.0–1.0 for how likely D7 helps bridge term→other."""
    score = 0.0
    # Tail-rec → fold is a strong signal
    if isinstance(term, OFix) and isinstance(other, OFold):
        if _is_tail_recursive(term):
            score = max(score, 0.95)
        else:
            score = max(score, 0.6)
    # DCE reduces term size — helpful when target is smaller
    if _term_size(term) > _term_size(other):
        ratio = _term_size(other) / max(_term_size(term), 1)
        score = max(score, 0.5 * (1.0 - ratio))
    # Constant guard in case
    if isinstance(term, OCase) and isinstance(term.test, OLit):
        score = max(score, 0.9)
    # Identity op
    if isinstance(term, OOp) and len(term.args) == 2:
        for a in term.args:
            if isinstance(a, OLit) and a.value in (0, 1, True, False):
                score = max(score, 0.8)
    return min(score, 1.0)


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Reverse D7: introduce dead code or expand fold to tail-recursive fix.

    The inverse of DCE re-introduces identity elements or wraps
    terms in trivially-true case guards. The inverse of tail-rec
    elimination constructs a tail-recursive OFix from an OFold.
    """
    results: List[Tuple[OTerm, str]] = []

    # fold → tail-recursive fix
    if isinstance(term, OFold):
        rec_var = OVar(term.op_name)
        guard = OOp('le', (OVar('$n'), OLit(0)))
        step_body = OOp(term.op_name, (OVar('$n'), rec_var))
        fix_body = OCase(guard, term.init, step_body)
        results.append((OFix(term.op_name, fix_body), 'D7_inv_fold_to_tailrec'))

    # Introduce identity: x → add(x, 0)
    if isinstance(term, OOp) and term.name in ('add', 'iadd') and len(term.args) >= 1:
        pass  # too noisy; only reverse when explicitly requested
    elif not isinstance(term, (OLit, OUnknown)):
        # Wrap in trivially-true guard: x → case(True, x, ⊥)
        wrapped = OCase(OLit(True), term, OUnknown('_dead'))
        results.append((wrapped, 'D7_inv_introduce_dead_branch'))

    return results


# ═══════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════

if __name__ == '__main__':
    ctx = FiberCtx(param_duck_types={'p0': 'int'})

    # Test 1: tail-recursive factorial → fold
    tail_fact = OFix('fact', OCase(
        OOp('le', (OVar('n'), OLit(0))),
        OVar('acc'),
        OOp('fact', (OOp('sub', (OVar('n'), OLit(1))),
                      OOp('mul', (OVar('acc'), OVar('n')))))
    ))
    rewrites = apply(tail_fact, ctx)
    assert any('D7_tailrec_to_fold' in ax for _, ax in rewrites), \
        f"Expected tail-rec elimination, got {rewrites}"
    print("✓ tail-rec factorial → fold")

    # Test 2: case(True, A, B) → A
    dce_true = OCase(OLit(True), OVar('a'), OVar('b'))
    rewrites = apply(dce_true, ctx)
    assert any(t.canon() == '$a' and 'dce_true' in ax for t, ax in rewrites)
    print("✓ case(True, a, b) → a")

    # Test 3: case(False, A, B) → B
    dce_false = OCase(OLit(False), OVar('a'), OVar('b'))
    rewrites = apply(dce_false, ctx)
    assert any(t.canon() == '$b' and 'dce_false' in ax for t, ax in rewrites)
    print("✓ case(False, a, b) → b")

    # Test 4: identical branches
    dce_ident = OCase(OVar('g'), OVar('x'), OVar('x'))
    rewrites = apply(dce_ident, ctx)
    assert any('dce_identical' in ax for _, ax in rewrites)
    print("✓ case(g, x, x) → x")

    # Test 5: add(x, 0) → x
    add_zero = OOp('add', (OVar('x'), OLit(0)))
    rewrites = apply(add_zero, ctx)
    assert any(t.canon() == '$x' and 'add_zero' in ax for t, ax in rewrites)
    print("✓ add(x, 0) → x")

    # Test 6: mul(x, 0) → 0
    mul_zero = OOp('mul', (OVar('x'), OLit(0)))
    rewrites = apply(mul_zero, ctx)
    assert any(t.canon() == '0' and 'mul_zero' in ax for t, ax in rewrites)
    print("✓ mul(x, 0) → 0")

    # Test 7: unused lambda param
    lam_unused = OLam(('x', 'y'), OVar('x'))
    rewrites = apply(lam_unused, ctx)
    assert any('unused_param' in ax for _, ax in rewrites)
    print("✓ λ(x,y).x → λ(x).x (drop unused y)")

    # Test 8: recognizes
    assert recognizes(tail_fact)
    assert recognizes(dce_true)
    assert recognizes(add_zero)
    assert not recognizes(OLit(42))
    print("✓ recognizes()")

    # Test 9: relevance_score
    fold_target = OFold('mul', OLit(1), OOp('range', (OVar('n'),)))
    score = relevance_score(tail_fact, fold_target)
    assert score >= 0.5, f"Expected high relevance, got {score}"
    print(f"✓ relevance_score(tailrec, fold) = {score:.2f}")

    # Test 10: inverse
    inv = apply_inverse(fold_target, ctx)
    assert any('fold_to_tailrec' in ax for _, ax in inv)
    print("✓ apply_inverse(fold) → tailrec fix")

    print("\nAll D7 self-tests passed ✓")
