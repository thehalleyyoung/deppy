"""D9 Axiom: Stack-Based Recursion (Defunctionalization).

Transforms recursive traversals into explicit-stack iterations
and vice versa.  Both forms compile to OFix — equivalence is
established by showing that the fix-point bodies encode the
same recurrence structure modulo the representation of the
"work remaining" (call stack vs. explicit stack data structure).

Mathematical basis: The CPS transform turns a recursive call
    f(x) = ... f(y) ...
into a continuation-passing form where the continuation captures
what remains to be done after f(y) returns.  Defunctionalization
then represents the set of continuations as a data type — typically
a list (stack) of frames.  The resulting iterative loop processes
one frame at a time from the stack.

By the defunctionalization theorem (Reynolds, 1972; §21.1), the
CPS-transformed + defunctionalized program has the same denotation
as the original recursive program.  In OTerm language:

    OFix[f](case(g, base, op(elem, f(sub_args))))
    ≡
    OFix[loop](case(empty(stack), acc, loop(push(stack, sub), op(acc, elem))))

Both compute the same fold over the implicit traversal order.
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

AXIOM_NAME = "D9_stack_rec"
AXIOM_CATEGORY = "data_structure"

COMPOSES_WITH = ["D1_fold_unfold", "D7_tailrec", "D15_traversal"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (D9 Stack ↔ Recursion Equivalence).

Let f_rec = fix[f](case(g, base, op(elem, f(children))))
be a recursive traversal.

Let f_stack = fix[loop](case(empty(stack), acc,
    let (node, rest) = pop(stack)
    in loop(push_all(rest, children(node)), op(acc, elem(node)))))
be the corresponding stack-based traversal.

Claim:  f_rec(root) ≡ f_stack([root])

Proof sketch:
  1. By CPS transformation, convert f_rec to continuation-passing:
     f_cps(x, k) = if g(x) then k(base) else f_cps(children(x), λr. k(op(elem(x), r)))
  2. The set of continuations {λr. k(op(elem(x), r))} is finite
     and can be defunctionalized as stack frames (node, k_index).
  3. The defunctionalized loop is exactly f_stack, with the explicit
     stack representing the chain of pending continuations.
  4. By the adequacy theorem for defunctionalization (Danvy & Nielsen, 2001),
     f_cps and f_stack compute the same function.
  5. By CPS adequacy, f_rec and f_cps compute the same function.
  6. Transitivity gives f_rec ≡ f_stack.
  □
"""

EXAMPLES = [
    {
        "name": "tree_dfs_recursive_vs_stack",
        "before": "fix[dfs](case(is_none(node), [], concat(dfs(left(node)), [val(node)], dfs(right(node)))))",
        "after": "fix[loop](case(empty(stack), acc, loop(push(push(rest, right(top)), left(top)), append(acc, val(top)))))",
        "benchmark": "benchmarks/tree_traversal.py",
    },
    {
        "name": "flatten_recursive_vs_iterative",
        "before": "fix[flat](case(is_atom(x), [x], fold[concat]([], map(flat, x))))",
        "after": "fix[loop](case(empty(stack), acc, loop(extend(rest, top), append(acc, top))))",
        "benchmark": None,
    },
    {
        "name": "recursive_sum_vs_stack",
        "before": "fix[sum_tree](case(is_leaf(t), val(t), add(sum_tree(left(t)), sum_tree(right(t)))))",
        "after": "fold[add](0, traverse(t))",
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
        return False if name in term.params else _contains_var(term.body, name)
    if isinstance(term, OMap):
        r = _contains_var(term.transform, name) or _contains_var(term.collection, name)
        if term.filter_pred:
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


def _count_recursive_calls(term: OTerm, fix_name: str) -> int:
    """Count how many times *fix_name* is referenced in *term*."""
    if isinstance(term, OVar):
        return 1 if term.name == fix_name else 0
    if isinstance(term, OOp):
        if term.name == fix_name:
            return 1 + sum(_count_recursive_calls(a, fix_name) for a in term.args)
        return sum(_count_recursive_calls(a, fix_name) for a in term.args)
    if isinstance(term, OCase):
        return (_count_recursive_calls(term.test, fix_name)
                + _count_recursive_calls(term.true_branch, fix_name)
                + _count_recursive_calls(term.false_branch, fix_name))
    if isinstance(term, OFold):
        return (_count_recursive_calls(term.init, fix_name)
                + _count_recursive_calls(term.collection, fix_name))
    if isinstance(term, OFix):
        return _count_recursive_calls(term.body, fix_name)
    if isinstance(term, OLam):
        return _count_recursive_calls(term.body, fix_name)
    if isinstance(term, OMap):
        r = _count_recursive_calls(term.transform, fix_name) + _count_recursive_calls(term.collection, fix_name)
        if term.filter_pred:
            r += _count_recursive_calls(term.filter_pred, fix_name)
        return r
    if isinstance(term, OSeq):
        return sum(_count_recursive_calls(e, fix_name) for e in term.elements)
    if isinstance(term, OCatch):
        return (_count_recursive_calls(term.body, fix_name)
                + _count_recursive_calls(term.default, fix_name))
    return 0


def _alpha_normalize(body: OTerm, fix_name: str) -> str:
    """Alpha-normalize: replace fix variable with canonical _rec."""
    import re
    canon = body.canon()
    canon = canon.replace(fix_name, '_rec')
    # Normalize all variable names to positional
    canon = re.sub(r'\$\w+', '$_', canon)
    return canon


def _canon_hash(s: str) -> str:
    return hashlib.md5(s.encode()).hexdigest()[:8]


# ═══════════════════════════════════════════════════════════
# Stack pattern recognition
# ═══════════════════════════════════════════════════════════

_STACK_OPS = frozenset({
    'push', 'pop', 'append', 'extend', 'push_all',
    'stack_push', 'stack_pop', 'deque_append', 'deque_popleft',
})

_EMPTY_CHECKS = frozenset({
    'empty', 'is_empty', 'not_', 'len_eq_0',
})


def _is_stack_based_fix(term: OFix) -> bool:
    """Check if a fix-point body uses explicit stack operations."""
    canon = term.body.canon()
    for op in _STACK_OPS:
        if op in canon:
            return True
    return False


def _is_recursive_traversal(term: OFix) -> bool:
    """Check if a fix-point is a multi-branch recursive traversal.

    A recursive traversal calls itself on sub-structures (children),
    typically with 2+ recursive calls (binary tree) or a map over
    children (n-ary tree).
    """
    if not isinstance(term.body, OCase):
        return False
    step = term.body.false_branch
    n_calls = _count_recursive_calls(step, term.name)
    if n_calls >= 2:
        return True
    # map(self, children) pattern
    if isinstance(step, OFold) or isinstance(step, OMap):
        if _contains_var(step, term.name):
            return True
    # Nested in an op: op(elem, self(child))
    if isinstance(step, OOp) and _contains_var(step, term.name):
        return True
    return False


def _extract_combiner_op(step: OTerm, fix_name: str) -> Optional[str]:
    """Extract the combining operation from a recursive step.

    In op(elem, f(child)), the combiner is 'op'.
    In concat(f(left), f(right)), the combiner is 'concat'.
    """
    if isinstance(step, OOp):
        if step.name != fix_name:
            return step.name
        # step is f(args) — look inside args for the combiner
        for arg in step.args:
            if isinstance(arg, OOp) and arg.name != fix_name:
                return arg.name
    return None


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D9: Stack-based recursion ↔ recursive traversal.

    Handles:
      1. Recursive traversal → explicit stack loop
         fix[f](case(g, base, op(f(left), f(right))))
         → fix[loop](case(empty(stack), acc, loop(push(rest,right,left), op(acc,elem))))
      2. Stack-based loop → fold over traversal
         fix[loop](case(empty(stack), acc, ...push/pop...))
         → fold[op](base, traverse(input))
      3. Structural equivalence: two OFix with same recurrence structure
         but different stack/recursion encoding
      4. Recursive with map over children → fold over flatten
    """
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OFix):
        return results

    body = term.body
    if not isinstance(body, OCase):
        return results

    base_val = body.true_branch
    step = body.false_branch

    # Direction 1: recursive traversal → stack-based loop
    if _is_recursive_traversal(term) and not _is_stack_based_fix(term):
        combiner = _extract_combiner_op(step, term.name)
        if combiner is None:
            combiner = 'combine'

        # Build stack-based equivalent
        stack_guard = OOp('empty', (OVar('_stack'),))
        pop_node = OOp('pop', (OVar('_stack'),))
        push_children = OOp('push_all', (OVar('_rest'), OVar('_children')))
        stack_step = OOp('loop', (push_children,
                                  OOp(combiner, (OVar('_acc'), OVar('_elem')))))
        stack_body = OCase(stack_guard, OVar('_acc'), stack_step)
        stack_fix = OFix('loop', stack_body)
        results.append((stack_fix, 'D9_rec_to_stack'))

        # Also offer fold form when combiner is known
        fold_form = OFold(combiner, base_val, OOp('traverse', (OVar('$p0'),)))
        results.append((fold_form, 'D9_rec_to_fold'))

    # Direction 2: stack-based loop → fold
    if _is_stack_based_fix(term):
        combiner = _extract_combiner_op(step, term.name)
        if combiner is None:
            combiner = 'combine'
        fold_form = OFold(combiner, base_val, OOp('traverse', (OVar('$p0'),)))
        results.append((fold_form, 'D9_stack_to_fold'))

    # Direction 3: structural equivalence via alpha-normalized hash
    normalized = _alpha_normalize(body, term.name)
    norm_hash = _canon_hash(normalized)
    if norm_hash != term.name and len(term.name) == 8:
        results.append((OFix(norm_hash, body), 'D9_structural_normalize'))

    return results


# ═══════════════════════════════════════════════════════════
# Recognizer & scoring
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could D9 apply to this term?"""
    if not isinstance(term, OFix):
        return False
    if not isinstance(term.body, OCase):
        return False
    # Either a recursive traversal or stack-based
    return _is_recursive_traversal(term) or _is_stack_based_fix(term)


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Heuristic 0.0–1.0 for how likely D9 helps bridge term→other."""
    if not isinstance(term, OFix):
        return 0.0
    score = 0.0
    # Recursive → stack or vice versa
    if isinstance(other, OFix):
        t_is_stack = _is_stack_based_fix(term)
        o_is_stack = _is_stack_based_fix(other)
        if t_is_stack != o_is_stack:
            score = max(score, 0.9)
        elif t_is_stack == o_is_stack:
            # Same style — maybe structural normalization helps
            score = max(score, 0.4)
    # Recursive → fold
    if isinstance(other, OFold) and _is_recursive_traversal(term):
        score = max(score, 0.85)
    # Stack → fold
    if isinstance(other, OFold) and _is_stack_based_fix(term):
        score = max(score, 0.85)
    return min(score, 1.0)


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Reverse D9: convert fold/stack to recursive form.

    fold[op](base, traverse(root))
    → fix[f](case(is_leaf(node), base, op(f(left(node)), f(right(node)))))
    """
    results: List[Tuple[OTerm, str]] = []

    # fold → recursive traversal
    if isinstance(term, OFold):
        if isinstance(term.collection, OOp) and term.collection.name == 'traverse':
            guard = OOp('is_leaf', (OVar('_node'),))
            rec_left = OOp('_rec', (OOp('left', (OVar('_node'),)),))
            rec_right = OOp('_rec', (OOp('right', (OVar('_node'),)),))
            step = OOp(term.op_name, (rec_left, rec_right))
            fix_body = OCase(guard, term.init, step)
            results.append((OFix('_rec', fix_body), 'D9_inv_fold_to_rec'))

    # Stack-based → recursive
    if isinstance(term, OFix) and _is_stack_based_fix(term):
        if isinstance(term.body, OCase):
            base_val = term.body.true_branch
            combiner = _extract_combiner_op(term.body.false_branch, term.name)
            if combiner:
                guard = OOp('is_leaf', (OVar('_node'),))
                rec_left = OOp('_rec', (OOp('left', (OVar('_node'),)),))
                rec_right = OOp('_rec', (OOp('right', (OVar('_node'),)),))
                step = OOp(combiner, (rec_left, rec_right))
                fix_body = OCase(guard, base_val, step)
                results.append((OFix('_rec', fix_body), 'D9_inv_stack_to_rec'))

    return results


# ═══════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════

if __name__ == '__main__':
    ctx = FiberCtx(param_duck_types={})

    # Test 1: recursive binary tree traversal → stack/fold
    tree_rec = OFix('dfs', OCase(
        OOp('is_none', (OVar('node'),)),
        OSeq(()),
        OOp('concat', (
            OOp('dfs', (OOp('left', (OVar('node'),)),)),
            OSeq((OOp('val', (OVar('node'),)),)),
            OOp('dfs', (OOp('right', (OVar('node'),)),)),
        )),
    ))
    rewrites = apply(tree_rec, ctx)
    assert any('D9_rec_to_stack' in ax for _, ax in rewrites), \
        f"Expected rec→stack, got {[ax for _, ax in rewrites]}"
    assert any('D9_rec_to_fold' in ax for _, ax in rewrites), \
        f"Expected rec→fold, got {[ax for _, ax in rewrites]}"
    print("✓ recursive traversal → stack + fold")

    # Test 2: stack-based loop → fold
    stack_loop = OFix('loop', OCase(
        OOp('empty', (OVar('stack'),)),
        OVar('acc'),
        OOp('loop', (
            OOp('push', (OVar('rest'), OOp('right', (OVar('top'),)))),
            OOp('add', (OVar('acc'), OOp('val', (OVar('top'),)))),
        )),
    ))
    rewrites = apply(stack_loop, ctx)
    assert any('D9_stack_to_fold' in ax for _, ax in rewrites), \
        f"Expected stack→fold, got {[ax for _, ax in rewrites]}"
    print("✓ stack-based loop → fold")

    # Test 3: recognizes
    assert recognizes(tree_rec)
    assert recognizes(stack_loop)
    assert not recognizes(OVar('x'))
    assert not recognizes(OFix('f', OVar('body')))
    print("✓ recognizes()")

    # Test 4: relevance_score
    fold_target = OFold('concat', OSeq(()), OOp('traverse', (OVar('root'),)))
    score = relevance_score(tree_rec, fold_target)
    assert score >= 0.8, f"Expected high relevance, got {score}"
    print(f"✓ relevance_score(rec, fold) = {score:.2f}")

    # Test 5: inverse fold → rec
    fold_term = OFold('add', OLit(0), OOp('traverse', (OVar('root'),)))
    inv = apply_inverse(fold_term, ctx)
    assert any('D9_inv_fold_to_rec' in ax for _, ax in inv)
    print("✓ apply_inverse(fold) → recursive")

    # Test 6: inverse stack → rec
    inv2 = apply_inverse(stack_loop, ctx)
    assert any('D9_inv_stack_to_rec' in ax for _, ax in inv2)
    print("✓ apply_inverse(stack) → recursive")

    # Test 7: cross-direction relevance
    score2 = relevance_score(stack_loop, tree_rec)
    assert score2 >= 0.5, f"Expected decent relevance, got {score2}"
    print(f"✓ relevance_score(stack, rec) = {score2:.2f}")

    print("\nAll D9 self-tests passed ✓")
