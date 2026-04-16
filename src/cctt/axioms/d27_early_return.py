"""D27: Early Return / Guard Clause — Nested Conditionals ↔ Flat Guards.

§25.3 of the CCTT monograph.  Theorem 25.3.1:
Deeply nested if/else chains are isomorphic to flat sequences of
guard clauses with early returns.

Key rewrites:
  • OCase(g1, OCase(g2, body, e2), e1) ↔ OCase(not g1, e1, OCase(not g2, e2, body))
  • Nested-to-flat: extract guard clauses from deeply nested conditionals
  • Flat-to-nested: roll guard clauses back into nested if/else
  • Guard negation: if not cond: return default; <rest>
    ↔ if cond: <rest> else: return default
  • Single-arm simplification: case(g, body, ⊥) → guarded body
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "D27_early_return"
AXIOM_CATEGORY = "control_flow"

SOUNDNESS_PROOF = r"""
Theorem 25.3.1 (Guard Clause Extraction).
Let t = case(g₁, case(g₂, body, e₂), e₁).
Then:
    t = case(¬g₁, e₁, case(¬g₂, e₂, body))

Proof by case analysis on (g₁, g₂):
  (T, T) → body = body                 ✓
  (T, F) → e₂   = e₂                  ✓
  (F, T) → e₁   = e₁                  ✓
  (F, F) → e₁   = e₁                  ✓

The transformation preserves denotation because in both forms,
each (g₁, g₂) valuation selects the same branch.

Guard negation: case(g, A, B) = case(¬g, B, A) is immediate from
the symmetry of case analysis.  □
"""

COMPOSES_WITH = ["D3_guard_reorder", "D7_tailrec", "D26_short_circuit"]
REQUIRES: List[str] = []

EXAMPLES = [
    {
        "name": "nested_to_guard",
        "before": "case(g1, case(g2, body, e2), e1)",
        "after": "case(not g1, e1, case(not g2, e2, body))",
        "benchmark": None,
    },
    {
        "name": "guard_negate",
        "before": "case(g, body, default)",
        "after": "case(not g, default, body)",
        "benchmark": None,
    },
    {
        "name": "flatten_triple",
        "before": "case(g1, case(g2, case(g3, body, e3), e2), e1)",
        "after": "case(not g1, e1, case(not g2, e2, case(not g3, e3, body)))",
        "benchmark": None,
    },
]


@dataclass
class FiberCtx:
    param_duck_types: Dict[str, str] = field(default_factory=dict)

    def is_numeric(self, term: OTerm) -> bool:
        return True


def _negate(term: OTerm) -> OTerm:
    """Negate a Boolean term, with double-negation elimination."""
    if isinstance(term, OOp) and term.name == 'u_not' and len(term.args) == 1:
        return term.args[0]
    if isinstance(term, OLit) and isinstance(term.value, bool):
        return OLit(not term.value)
    return OOp('u_not', (term,))


def _nesting_depth(term: OTerm) -> int:
    """Measure depth of nested OCase on the true-branch side."""
    if isinstance(term, OCase):
        return 1 + _nesting_depth(term.true_branch)
    return 0


def _guard_depth(term: OTerm) -> int:
    """Measure depth of guard-style nesting on the false-branch side."""
    if isinstance(term, OCase):
        return 1 + _guard_depth(term.false_branch)
    return 0


def _extract_guards(term: OTerm) -> List[Tuple[OTerm, OTerm]]:
    """Extract guard clauses from guard-style nesting.

    Guard style: case(¬g, early_return, rest)
    Returns list of (guard, early_return) pairs, plus the final body.
    """
    guards: List[Tuple[OTerm, OTerm]] = []
    current = term
    while isinstance(current, OCase):
        guards.append((current.test, current.true_branch))
        current = current.false_branch
    return guards


def _is_early_return_form(term: OTerm) -> bool:
    """Check if term is in guard-clause form: case(g, simple, complex)."""
    if not isinstance(term, OCase):
        return False
    # Guard clause: false branch is more complex than true branch
    return (_guard_depth(term) >= 2 or
            (isinstance(term.true_branch, (OLit, OVar, OUnknown)) and
             isinstance(term.false_branch, OCase)))


def _is_nested_form(term: OTerm) -> bool:
    """Check if term has nesting on the true-branch side."""
    if not isinstance(term, OCase):
        return False
    return isinstance(term.true_branch, OCase)


# ═══════════════════════════════════════════════════════════
# Core axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D27 early-return / guard-clause rewrites to *term*.

    Handles:
      1. Nested-to-guard: case(g1, case(g2, body, e2), e1)
         → case(¬g1, e1, case(¬g2, e2, body))
      2. Guard-to-nested: reverse of (1)
      3. Guard negation: case(g, A, B) ↔ case(¬g, B, A)
      4. Flatten deeply nested: recursive application of (1)
      5. Simplify constant guards within nested structure
      6. Remove trivial guards: case(True, A, B) → A (defer to D7)
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OCase):
        return results

    # ── 1. Nested-to-guard: case(g1, case(g2, body, e2), e1) ──
    #    → case(¬g1, e1, case(¬g2, e2, body))
    if isinstance(term.true_branch, OCase):
        inner = term.true_branch
        results.append((
            OCase(_negate(term.test), term.false_branch,
                  OCase(_negate(inner.test), inner.false_branch, inner.true_branch)),
            'D27_nested_to_guard',
        ))

    # ── 2. Guard-to-nested: case(¬g1, e1, case(¬g2, e2, body)) ──
    #    → case(g1, case(g2, body, e2), e1)
    if isinstance(term.false_branch, OCase):
        inner = term.false_branch
        results.append((
            OCase(_negate(term.test),
                  OCase(_negate(inner.test), inner.false_branch, inner.true_branch),
                  term.true_branch),
            'D27_guard_to_nested',
        ))

    # ── 3. Guard negation: case(g, A, B) ↔ case(¬g, B, A) ──
    results.append((
        OCase(_negate(term.test), term.false_branch, term.true_branch),
        'D27_negate_guard',
    ))

    # ── 4. Deep flatten: if depth ≥ 3 on true side, flatten all ──
    if _nesting_depth(term) >= 3:
        guards_and_defaults: List[Tuple[OTerm, OTerm]] = []
        current: OTerm = term
        while isinstance(current, OCase) and isinstance(current.true_branch, OCase):
            guards_and_defaults.append((current.test, current.false_branch))
            current = current.true_branch
        if isinstance(current, OCase):
            guards_and_defaults.append((current.test, current.false_branch))
            body = current.true_branch
        else:
            body = current

        # Build flattened guard chain
        result: OTerm = body
        for guard, default in reversed(guards_and_defaults):
            result = OCase(_negate(guard), default, result)
        if result.canon() != term.canon():
            results.append((result, 'D27_deep_flatten'))

    # ── 5. Merge identical consecutive guards ──
    if isinstance(term.true_branch, OCase):
        inner = term.true_branch
        if term.test.canon() == inner.test.canon():
            results.append((
                OCase(term.test, inner.true_branch, term.false_branch),
                'D27_merge_identical_guard',
            ))

    # ── 6. Lift inner false branch when outer false matches ──
    if isinstance(term.true_branch, OCase):
        inner = term.true_branch
        if term.false_branch.canon() == inner.false_branch.canon():
            combined_test = OOp('and', (term.test, inner.test))
            results.append((
                OCase(combined_test, inner.true_branch, term.false_branch),
                'D27_combine_guards',
            ))

    return results


def recognizes(term: OTerm) -> bool:
    """Quick check: could D27 apply to this term?"""
    if not isinstance(term, OCase):
        return False
    if isinstance(term.true_branch, OCase):
        return True
    if isinstance(term.false_branch, OCase):
        return True
    return True  # guard negation always applies to OCase


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D27's relevance for bridging source → target."""
    s_depth = _nesting_depth(source)
    t_depth = _nesting_depth(target)
    s_gdepth = _guard_depth(source)
    t_gdepth = _guard_depth(target)

    # One nested, other guard-style → high
    if s_depth >= 2 and t_gdepth >= 2:
        return 0.9
    if s_gdepth >= 2 and t_depth >= 2:
        return 0.9
    # One has deeper nesting than other
    if abs(s_depth - t_depth) >= 2:
        return 0.7
    # Both are OCase
    if isinstance(source, OCase) and isinstance(target, OCase):
        return 0.4
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse of D27: guard-to-nested and negate-guard."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OCase):
        return results

    # Guard-to-nested: case(¬g1, e1, case(¬g2, e2, body))
    # → case(g1, case(g2, body, e2), e1)
    if isinstance(term.false_branch, OCase):
        inner = term.false_branch
        results.append((
            OCase(_negate(term.test),
                  OCase(_negate(inner.test), inner.false_branch, inner.true_branch),
                  term.true_branch),
            'D27_inv_guard_to_nested',
        ))

    # Nested-to-guard (inverse of flatten)
    if isinstance(term.true_branch, OCase):
        inner = term.true_branch
        results.append((
            OCase(_negate(term.test), term.false_branch,
                  OCase(_negate(inner.test), inner.false_branch, inner.true_branch)),
            'D27_inv_nested_to_guard',
        ))

    # Negate guard (self-inverse)
    results.append((
        OCase(_negate(term.test), term.false_branch, term.true_branch),
        'D27_inv_negate_guard',
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
    g1, g2, g3 = OVar('g1'), OVar('g2'), OVar('g3')
    body = OVar('body')
    e1, e2, e3 = OVar('e1'), OVar('e2'), OVar('e3')
    a, b = OVar('a'), OVar('b')

    # 1. Nested-to-guard: case(g1, case(g2, body, e2), e1)
    nested = OCase(g1, OCase(g2, body, e2), e1)
    r1 = apply(nested, ctx)
    _assert(any(lbl == 'D27_nested_to_guard' for _, lbl in r1), "nested → guard")
    guard_form = [t for t, lbl in r1 if lbl == 'D27_nested_to_guard'][0]
    _assert(isinstance(guard_form, OCase), "result is OCase")
    # The guard form should have ¬g1 as the test
    _assert(isinstance(guard_form.test, OOp) and guard_form.test.name == 'u_not',
            "guard has negated test")

    # 2. Guard-to-nested: reverse direction
    guard_style = OCase(_negate(g1), e1, OCase(_negate(g2), e2, body))
    r2 = apply(guard_style, ctx)
    _assert(any(lbl == 'D27_guard_to_nested' for _, lbl in r2), "guard → nested")

    # 3. Guard negation: case(g, A, B) → case(¬g, B, A)
    simple = OCase(g1, a, b)
    r3 = apply(simple, ctx)
    _assert(any(lbl == 'D27_negate_guard' for _, lbl in r3), "guard negation")
    negated = [t for t, lbl in r3 if lbl == 'D27_negate_guard'][0]
    _assert(isinstance(negated, OCase) and negated.true_branch.canon() == b.canon(),
            "negated branches swapped")

    # 4. Double negation in guard: case(¬g, A, B) → case(g, B, A)
    neg_guard = OCase(OOp('u_not', (g1,)), a, b)
    r4 = apply(neg_guard, ctx)
    negate_r = [t for t, lbl in r4 if lbl == 'D27_negate_guard'][0]
    # ¬(¬g1) = g1
    _assert(isinstance(negate_r, OCase) and negate_r.test.canon() == g1.canon(),
            "double neg eliminated in guard")

    # 5. Deep flatten: case(g1, case(g2, case(g3, body, e3), e2), e1)
    deep = OCase(g1, OCase(g2, OCase(g3, body, e3), e2), e1)
    r5 = apply(deep, ctx)
    _assert(any(lbl == 'D27_deep_flatten' for _, lbl in r5), "deep flatten")

    # 6. Merge identical guards: case(g, case(g, body, e2), e1)
    dup_guard = OCase(g1, OCase(g1, body, e2), e1)
    r6 = apply(dup_guard, ctx)
    _assert(any(lbl == 'D27_merge_identical_guard' for _, lbl in r6), "merge identical")

    # 7. Combine guards when false branches match
    shared_fb = OCase(g1, OCase(g2, body, e1), e1)
    r7 = apply(shared_fb, ctx)
    _assert(any(lbl == 'D27_combine_guards' for _, lbl in r7), "combine guards")
    combined = [t for t, lbl in r7 if lbl == 'D27_combine_guards'][0]
    _assert(isinstance(combined.test, OOp) and combined.test.name == 'and',
            "combined test is and")

    # 8. Recognizes
    _assert(recognizes(nested), "recognizes nested")
    _assert(recognizes(simple), "recognizes simple case")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # 9. Relevance
    _assert(relevance_score(nested, guard_style) > 0.5,
            "high relevance nested↔guard")

    # 10. Inverse: guard → nested
    r10 = apply_inverse(guard_style, ctx)
    _assert(any(lbl == 'D27_inv_guard_to_nested' for _, lbl in r10), "inv guard → nested")

    # 11. Inverse: nested → guard
    r11 = apply_inverse(nested, ctx)
    _assert(any(lbl == 'D27_inv_nested_to_guard' for _, lbl in r11), "inv nested → guard")

    # 12. Inverse: negate guard (self-inverse)
    r12 = apply_inverse(simple, ctx)
    _assert(any(lbl == 'D27_inv_negate_guard' for _, lbl in r12), "inv negate guard")

    print(f"D27 early-return: {_pass} passed, {_fail} failed")
