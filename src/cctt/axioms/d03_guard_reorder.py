from __future__ import annotations
"""D3: Guard Reordering — permute disjoint case branches.

Mathematical basis: case-split independence.
When two guards g1, g2 are *disjoint* (g1 ∧ g2 = ⊥), the order
in which they are tested does not affect the result:

    case(g1, v1, case(g2, v2, else))  ≡  case(g2, v2, case(g1, v1, else))

This also handles:
  - Complementary guard merging: case(g, A, case(¬g, B, C)) → case(g, A, B)
  - Full permutation of n-way case chains when all guards are pairwise disjoint
  - Rotation of long case chains for partial reordering

HIT path:  d3 : OCase(g1, v1, OCase(g2, v2, e)) = OCase(g2, v2, OCase(g1, v1, e))
Monograph: Chapter 20, §20.3
"""

from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Set, Tuple

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
    _subst, normalize,
)
from cctt.path_search import FiberCtx

# ═══════════════════════════════════════════════════════════════
# Constants
# ═══════════════════════════════════════════════════════════════

AXIOM_NAME = "d3_guard_reorder"
AXIOM_CATEGORY = "control"

# ═══════════════════════════════════════════════════════════════
# Guard analysis helpers
# ═══════════════════════════════════════════════════════════════

# Pairs of comparison operators that are complements
_COMP_COMPLEMENTS = frozenset({
    ('lt', 'gte'), ('gte', 'lt'), ('gt', 'lte'), ('lte', 'gt'),
    ('eq', 'noteq'), ('noteq', 'eq'), ('ne', 'eq'), ('eq', 'ne'),
    ('le', 'gt'), ('gt', 'le'), ('ge', 'lt'), ('lt', 'ge'),
})

# Pairs of comparison operators that are disjoint (g1 ∧ g2 = ⊥)
_COMP_DISJOINT = frozenset({
    ('lt', 'gte'), ('gt', 'lte'), ('lte', 'gt'), ('gte', 'lt'),
    ('lt', 'gt'), ('gt', 'lt'),
})


def _guards_complementary(g1: OTerm, g2: OTerm) -> bool:
    """Check if two guards are complementary: g1 ≡ ¬g2."""
    # Explicit negation: g1 = not(g2) or g2 = not(g1)
    if isinstance(g1, OOp) and g1.name == 'u_not' and len(g1.args) == 1:
        return g1.args[0].canon() == g2.canon()
    if isinstance(g2, OOp) and g2.name == 'u_not' and len(g2.args) == 1:
        return g2.args[0].canon() == g1.canon()
    # Comparison complements: lt(x,y) ↔ gte(x,y)
    if (isinstance(g1, OOp) and isinstance(g2, OOp)
            and len(g1.args) == 2 and len(g2.args) == 2
            and (g1.name, g2.name) in _COMP_COMPLEMENTS
            and g1.args[0].canon() == g2.args[0].canon()
            and g1.args[1].canon() == g2.args[1].canon()):
        return True
    return False


def _guards_disjoint(g1: OTerm, g2: OTerm) -> bool:
    """Conservative disjointness check for two guards.

    Two guards are disjoint when g1 ∧ g2 = ⊥.  We check:
      1. Complementary:  g1 = ¬g2
      2. Range-disjoint: ``lt(x,a)`` vs ``gte(x,a)``
      3. Equality-based: ``eq(x,a)`` vs ``eq(x,b)`` with a ≠ b
    """
    if _guards_complementary(g1, g2):
        return True
    if isinstance(g1, OOp) and isinstance(g2, OOp):
        if (g1.name, g2.name) in _COMP_DISJOINT:
            if len(g1.args) == 2 and len(g2.args) == 2:
                if (g1.args[0].canon() == g2.args[0].canon()
                        and g1.args[1].canon() == g2.args[1].canon()):
                    return True
        # eq(x, a) vs eq(x, b) with a ≠ b
        if g1.name == 'eq' and g2.name == 'eq':
            if len(g1.args) == 2 and len(g2.args) == 2:
                if g1.args[0].canon() == g2.args[0].canon():
                    if (isinstance(g1.args[1], OLit) and isinstance(g2.args[1], OLit)
                            and g1.args[1].value != g2.args[1].value):
                        return True
    return False


# ═══════════════════════════════════════════════════════════════
# Case-chain utilities
# ═══════════════════════════════════════════════════════════════

def _collect_case_chain(term: OTerm) -> List[Tuple[OTerm, OTerm]]:
    """Flatten a right-nested OCase chain into (guard, value) pairs.

    The final fallback becomes ``(OLit(True), fallback_val)``.

    Example::

        case(g1, v1, case(g2, v2, v3))
        → [(g1, v1), (g2, v2), (True, v3)]
    """
    chain: List[Tuple[OTerm, OTerm]] = []
    cur = term
    while isinstance(cur, OCase):
        chain.append((cur.test, cur.true_branch))
        cur = cur.false_branch
    chain.append((OLit(True), cur))
    return chain


def _build_case_chain(chain: List[Tuple[OTerm, OTerm]]) -> OTerm:
    """Reconstruct a right-nested OCase from a chain list."""
    if len(chain) == 1:
        return chain[0][1]
    guard, val = chain[0]
    rest = _build_case_chain(chain[1:])
    return OCase(guard, val, rest)


def _all_pairwise_disjoint(guards: List[OTerm]) -> bool:
    """Check if all guards in the list are pairwise disjoint."""
    for i in range(len(guards)):
        for j in range(i + 1, len(guards)):
            if not _guards_disjoint(guards[i], guards[j]):
                return False
    return True


# ═══════════════════════════════════════════════════════════════
# Main apply function
# ═══════════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply D3 axiom: reorder disjoint guards in case chains.

    Produces:
      - D3_guard_swap: swap two adjacent disjoint guards
      - D3_guard_rotate: rotate a 3+-element disjoint chain
      - D3_guard_merge: merge complementary guards
    """
    results: List[Tuple[OTerm, str]] = []
    if not isinstance(term, OCase):
        return results
    if not isinstance(term.false_branch, OCase):
        # Single case — check for complementary merge only
        return results

    inner = term.false_branch

    # ── Complementary guard merging ──
    # case(g, A, case(¬g, B, C)) → case(g, A, B)
    if _guards_complementary(term.test, inner.test):
        merged = OCase(term.test, term.true_branch, inner.true_branch)
        results.append((merged, 'D3_guard_merge'))

    # ── Chain analysis ──
    chain = _collect_case_chain(term)
    guards = [g for g, _ in chain[:-1]]  # exclude the fallback

    # Check pairwise disjointness
    all_disjoint = _all_pairwise_disjoint(guards)

    # Even if not all pairwise disjoint, check adjacent pair
    if not all_disjoint and len(guards) >= 2:
        if _guards_disjoint(guards[0], guards[1]):
            # Swap just the first two
            swapped = [chain[1], chain[0]] + chain[2:]
            rebuilt = _build_case_chain(swapped)
            if rebuilt.canon() != term.canon():
                results.append((rebuilt, 'D3_guard_swap'))
            return results  # only adjacent swap
        return results

    if not all_disjoint:
        return results

    # ── All guards are pairwise disjoint ──
    if len(chain) == 3:  # 2 guards + fallback
        swapped = [chain[1], chain[0], chain[2]]
        rebuilt = _build_case_chain(swapped)
        if rebuilt.canon() != term.canon():
            results.append((rebuilt, 'D3_guard_swap'))

    elif len(chain) > 3:  # 3+ guards + fallback
        # Emit the adjacent swap
        swapped = [chain[1], chain[0]] + chain[2:]
        rebuilt = _build_case_chain(swapped)
        if rebuilt.canon() != term.canon():
            results.append((rebuilt, 'D3_guard_swap'))

        # Emit a rotation: move first guard to end of guard section
        rotated = chain[1:len(chain) - 1] + [chain[0]] + [chain[-1]]
        rebuilt_rot = _build_case_chain(rotated)
        if rebuilt_rot.canon() != term.canon():
            results.append((rebuilt_rot, 'D3_guard_rotate'))

    return results


# ═══════════════════════════════════════════════════════════════
# Recognition and relevance
# ═══════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could D3 apply to this term?

    Returns ``True`` for nested OCase terms (case chains).
    """
    return (isinstance(term, OCase)
            and isinstance(term.false_branch, OCase))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """How likely is D3 to help prove ``term ≡ other``?

    Returns a score in [0.0, 1.0]:
      0.9 — both are case chains with same guards in different order
      0.5 — both are case chains
      0.2 — at least one is a case chain
      0.0 — neither is a case
    """
    t_case = isinstance(term, OCase) and isinstance(term.false_branch, OCase)
    o_case = isinstance(other, OCase) and isinstance(other.false_branch, OCase)
    if not t_case and not o_case:
        return 0.0
    if not t_case or not o_case:
        return 0.2
    # Both are case chains — check if they have the same guard set
    t_chain = _collect_case_chain(term)
    o_chain = _collect_case_chain(other)
    t_guards = sorted(g.canon() for g, _ in t_chain[:-1])
    o_guards = sorted(g.canon() for g, _ in o_chain[:-1])
    if t_guards == o_guards:
        return 0.9
    return 0.5


# ═══════════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply D3 in reverse: same as forward (guard reorder is its own inverse)."""
    return [(t, lbl.replace('D3_', 'D3_inv_')) for t, lbl in apply(term, ctx)]


# ═══════════════════════════════════════════════════════════════
# Composability metadata
# ═══════════════════════════════════════════════════════════════

COMPOSES_WITH = ["d7_tailrec", "d8_section_merge"]
REQUIRES: List[str] = []

# ═══════════════════════════════════════════════════════════════
# Soundness justification
# ═══════════════════════════════════════════════════════════════

SOUNDNESS_PROOF = """
Theorem (D3 Soundness): If D3 transforms t to t', then ⟦t⟧ = ⟦t'⟧.

Proof: By case analysis and disjointness.

Given  case(g1, v1, case(g2, v2, e))  where g1 ∧ g2 = ⊥:

For any input x:
  - If g1(x) = True:  both orderings return v1 (g1 fires first)
  - If g2(x) = True:  both orderings return v2 (g2 fires first)
  - If neither:       both orderings return e (fallback)

Since g1 ∧ g2 = ⊥, at most one of g1, g2 is true, so the
swap cannot change which branch fires.  ∎

For complementary merge:
  case(g, A, case(¬g, B, C))
In the else-branch of g, ¬g is always True, so case(¬g, B, C) = B.
Hence  case(g, A, case(¬g, B, C)) = case(g, A, B).  ∎
"""

# ═══════════════════════════════════════════════════════════════
# Examples
# ═══════════════════════════════════════════════════════════════

EXAMPLES = [
    {
        "name": "swap_disjoint",
        "before": "OCase(OOp('lt',(OVar('x'),OLit(0))), OLit(1), OCase(OOp('gte',(OVar('x'),OLit(0))), OLit(2), OLit(3)))",
        "after": "OCase(OOp('gte',(OVar('x'),OLit(0))), OLit(2), OCase(OOp('lt',(OVar('x'),OLit(0))), OLit(1), OLit(3)))",
        "benchmark": "guard01",
        "description": "Swap lt(x,0) and gte(x,0) guards",
    },
    {
        "name": "merge_complementary",
        "before": "OCase(g, OLit(10), OCase(OOp('u_not',(g,)), OLit(20), OLit(30)))",
        "after": "OCase(g, OLit(10), OLit(20))",
        "benchmark": "guard02",
        "description": "Merge case(g, A, case(¬g, B, C)) → case(g, A, B)",
    },
    {
        "name": "rotate_triple",
        "before": "OCase(g1, v1, OCase(g2, v2, OCase(g3, v3, v4)))",
        "after": "OCase(g2, v2, OCase(g3, v3, OCase(g1, v1, v4)))",
        "benchmark": "guard03",
        "description": "Rotate three pairwise-disjoint guards",
    },
    {
        "name": "three_way_eq",
        "before": "OCase(OOp('eq',(x,OLit(1))), v1, OCase(OOp('eq',(x,OLit(2))), v2, OCase(OOp('eq',(x,OLit(3))), v3, v4)))",
        "after": "OCase(OOp('eq',(x,OLit(2))), v2, OCase(OOp('eq',(x,OLit(3))), v3, OCase(OOp('eq',(x,OLit(1))), v1, v4)))",
        "benchmark": "guard04",
        "description": "Rotate equality-disjoint guards eq(x,1)/eq(x,2)/eq(x,3)",
    },
]

# ═══════════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════════

if __name__ == '__main__':
    import sys
    _passed = 0
    _failed = 0

    def _assert(cond: bool, msg: str) -> None:
        global _passed, _failed
        if cond:
            _passed += 1
            print(f'  ✓ {msg}')
        else:
            _failed += 1
            print(f'  ✗ FAIL: {msg}')

    ctx = FiberCtx(param_duck_types={'p0': 'int', 'p1': 'int'})

    # Test disjoint guard swap
    print('▶ D3 disjoint guard swap')
    g1 = OOp('lt', (OVar('x'), OLit(0)))
    g2 = OOp('gte', (OVar('x'), OLit(0)))
    chain_case = OCase(g1, OLit(1), OCase(g2, OLit(2), OLit(3)))
    results = apply(chain_case, ctx)
    _assert(any(lbl == 'D3_guard_swap' for _, lbl in results),
            'D3 fires on disjoint guards')
    swapped = [t for t, lbl in results if lbl == 'D3_guard_swap'][0]
    _assert(isinstance(swapped, OCase), 'result is OCase')
    _assert(swapped.test.canon() == g2.canon(), 'outer guard is now g2')

    # Test complementary merge
    print('▶ D3 complementary merge')
    g_neg = OOp('u_not', (g1,))
    comp_case = OCase(g1, OLit(10), OCase(g_neg, OLit(20), OLit(30)))
    results = apply(comp_case, ctx)
    _assert(any(lbl == 'D3_guard_merge' for _, lbl in results),
            'D3 merge fires on complementary guards')
    merged = [t for t, lbl in results if lbl == 'D3_guard_merge'][0]
    _assert(isinstance(merged, OCase), 'merged is OCase')
    # After merge: case(g1, 10, 20)
    _assert(merged.false_branch == OLit(20), 'merged else is 20')

    # Test 3-guard rotation
    print('▶ D3 3-guard rotation')
    g3 = OOp('eq', (OVar('x'), OLit(1)))
    g4 = OOp('eq', (OVar('x'), OLit(2)))
    g5 = OOp('eq', (OVar('x'), OLit(3)))
    triple = OCase(g3, OLit(10), OCase(g4, OLit(20), OCase(g5, OLit(30), OLit(40))))
    results = apply(triple, ctx)
    has_swap = any(lbl == 'D3_guard_swap' for _, lbl in results)
    has_rotate = any(lbl == 'D3_guard_rotate' for _, lbl in results)
    _assert(has_swap or has_rotate, 'D3 fires on 3-guard chain')

    # Test recognizes
    print('▶ D3 recognizes()')
    _assert(recognizes(chain_case), 'nested OCase recognised')
    _assert(not recognizes(OCase(OVar('g'), OLit(1), OLit(2))),
            'single OCase not recognised')
    _assert(not recognizes(OLit(42)), 'literal not recognised')

    # Test relevance_score
    print('▶ D3 relevance_score()')
    _assert(relevance_score(chain_case, comp_case) > 0.4,
            'two case chains → high relevance')
    _assert(relevance_score(OLit(1), OLit(2)) == 0.0,
            'no cases → 0.0')

    # Test non-disjoint guards (should not fire)
    print('▶ D3 non-disjoint guards')
    nd1 = OOp('lt', (OVar('x'), OLit(5)))
    nd2 = OOp('lt', (OVar('x'), OLit(10)))
    nd_case = OCase(nd1, OLit(1), OCase(nd2, OLit(2), OLit(3)))
    results = apply(nd_case, ctx)
    _assert(len(results) == 0, 'non-disjoint guards → no rewrites')

    # Test inverse
    print('▶ D3 apply_inverse()')
    inv_results = apply_inverse(chain_case, ctx)
    _assert(any('inv' in lbl for _, lbl in inv_results), 'inverse fires')

    # Edge cases
    print('▶ D3 edge cases')
    _assert(apply(OLit(3), ctx) == [], 'D3 on literal is empty')
    single = OCase(OVar('g'), OLit(1), OLit(2))
    _assert(apply(single, ctx) == [], 'D3 on single case is empty')

    print(f'\n{"═" * 50}')
    print(f'  D3: {_passed} passed, {_failed} failed')
    print(f'{"═" * 50}')
    sys.exit(1 if _failed > 0 else 0)
