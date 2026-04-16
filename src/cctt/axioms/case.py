"""Case/Guard Rewrite Axioms — Guard Simplification, Case Splitting, De Morgan.

Rewrites for OCase (conditional/branch) terms.  These handle
guard simplification, constant folding, nested case normalisation,
and De Morgan distribution of compound guards.

Key rewrites:
  • case(True, a, b) → a
  • case(False, a, b) → b
  • case(g, x, x) → x                    [identical branches]
  • case(not(g), a, b) → case(g, b, a)   [negation flip]
  • case(g, case(g, a, b), c) → case(g, a, c)  [guard subsumption]
  • case(and(g1,g2), a, b) → case(g1, case(g2, a, b), b)  [De Morgan and]
  • case(or(g1,g2), a, b) → case(g1, a, case(g2, a, b))   [De Morgan or]
  • Nested case merging / flattening
  • Guard complement detection
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "CASE_case"
AXIOM_CATEGORY = "utility"

SOUNDNESS_PROOF = """
Case identities follow from the universal property of coproducts:

case(True, a, b) = a: the constant True guard selects the first branch.
case(False, a, b) = b: dually.
case(g, x, x) = x: both branches are the same.

De Morgan distribution:
  case(g1 ∧ g2, a, b) = case(g1, case(g2, a, b), b)
  because g1 ∧ g2 = True iff both g1=True and g2=True.

Guard subsumption:
  case(g, case(g, a, b), c) = case(g, a, c)
  because in the then-branch of outer case, g=True, so inner case
  takes its then-branch = a.
"""

COMPOSES_WITH = ["ALG", "D22_effect_elim", "FOLD", "D24_eta"]
REQUIRES: List[str] = []

EXAMPLES = [
    ("case(True, a, b)", "a", "CASE_true"),
    ("case(False, a, b)", "b", "CASE_false"),
    ("case(g, x, x)", "x", "CASE_identical"),
    ("case(not(g), a, b)", "case(g, b, a)", "CASE_not_flip"),
    ("case(and(g1,g2), a, b)", "case(g1, case(g2, a, b), b)", "CASE_demorgan_and"),
]


@dataclass
class FiberCtx:
    param_duck_types: Dict[str, str] = field(default_factory=dict)

    def is_numeric(self, term: OTerm) -> bool:
        return True


def _guards_complementary(g1: OTerm, g2: OTerm) -> bool:
    """Check if g1 and g2 are logical complements: g1 ≡ ¬g2."""
    if isinstance(g1, OOp) and g1.name == 'u_not' and len(g1.args) == 1:
        return g1.args[0].canon() == g2.canon()
    if isinstance(g2, OOp) and g2.name == 'u_not' and len(g2.args) == 1:
        return g2.args[0].canon() == g1.canon()
    comp_complements = {
        ('lt', 'gte'), ('gte', 'lt'), ('gt', 'lte'), ('lte', 'gt'),
        ('eq', 'noteq'), ('noteq', 'eq'), ('ne', 'eq'), ('eq', 'ne'),
        ('le', 'gt'), ('gt', 'le'), ('ge', 'lt'), ('lt', 'ge'),
    }
    if (isinstance(g1, OOp) and isinstance(g2, OOp)
            and len(g1.args) == 2 and len(g2.args) == 2
            and (g1.name, g2.name) in comp_complements
            and g1.args[0].canon() == g2.args[0].canon()
            and g1.args[1].canon() == g2.args[1].canon()):
        return True
    return False


def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply case/guard rewrite rules."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OCase):
        return results

    # ── 1. case(True, a, b) → a ──
    if isinstance(term.test, OLit) and term.test.value is True:
        results.append((term.true_branch, 'CASE_true'))

    # ── 2. case(False, a, b) → b ──
    if isinstance(term.test, OLit) and term.test.value is False:
        results.append((term.false_branch, 'CASE_false'))

    # ── 3. case(g, x, x) → x  [identical branches] ──
    if term.true_branch.canon() == term.false_branch.canon():
        results.append((term.true_branch, 'CASE_identical'))

    # ── 4. case(not(g), a, b) → case(g, b, a) ──
    if isinstance(term.test, OOp) and term.test.name == 'u_not' and len(term.test.args) == 1:
        results.append((
            OCase(term.test.args[0], term.false_branch, term.true_branch),
            'CASE_not_flip',
        ))

    # ── 5. Guard subsumption (then-branch): case(g, case(g, a, b), c) → case(g, a, c) ──
    if isinstance(term.true_branch, OCase):
        if term.true_branch.test.canon() == term.test.canon():
            results.append((
                OCase(term.test, term.true_branch.true_branch, term.false_branch),
                'CASE_guard_subsume_then',
            ))

    # ── 6. Guard subsumption (else-branch): case(g, c, case(g, a, b)) → case(g, c, b) ──
    if isinstance(term.false_branch, OCase):
        if term.false_branch.test.canon() == term.test.canon():
            results.append((
                OCase(term.test, term.true_branch, term.false_branch.false_branch),
                'CASE_guard_subsume_else',
            ))

    # ── 7. De Morgan distribution (and): case(and(g1,g2), a, b) → case(g1, case(g2, a, b), b) ──
    if isinstance(term.test, OOp) and term.test.name == 'and' and len(term.test.args) == 2:
        g1, g2 = term.test.args
        results.append((
            OCase(g1, OCase(g2, term.true_branch, term.false_branch), term.false_branch),
            'CASE_demorgan_and',
        ))

    # ── 8. De Morgan distribution (or): case(or(g1,g2), a, b) → case(g1, a, case(g2, a, b)) ──
    if isinstance(term.test, OOp) and term.test.name == 'or' and len(term.test.args) == 2:
        g1, g2 = term.test.args
        results.append((
            OCase(g1, term.true_branch, OCase(g2, term.true_branch, term.false_branch)),
            'CASE_demorgan_or',
        ))

    # ── 9. Complementary guard merge: case(g, a, case(¬g, b, c)) → case(g, a, b) ──
    if isinstance(term.false_branch, OCase):
        if _guards_complementary(term.test, term.false_branch.test):
            results.append((
                OCase(term.test, term.true_branch, term.false_branch.true_branch),
                'CASE_complement_merge',
            ))

    # ── 10. case(g, True, False) → g  [guard is already the boolean] ──
    if (isinstance(term.true_branch, OLit) and term.true_branch.value is True
            and isinstance(term.false_branch, OLit) and term.false_branch.value is False):
        results.append((term.test, 'CASE_bool_collapse'))

    # ── 11. case(g, False, True) → not(g) ──
    if (isinstance(term.true_branch, OLit) and term.true_branch.value is False
            and isinstance(term.false_branch, OLit) and term.false_branch.value is True):
        results.append((OOp('u_not', (term.test,)), 'CASE_bool_negate'))

    # ── 12. case(g, a, case(h, a, b)) → case(or(g, h), a, b) ──
    if isinstance(term.false_branch, OCase):
        if term.true_branch.canon() == term.false_branch.true_branch.canon():
            results.append((
                OCase(OOp('or', (term.test, term.false_branch.test)),
                      term.true_branch, term.false_branch.false_branch),
                'CASE_or_merge',
            ))

    # ── 13. case(g, case(h, a, b), b) → case(and(g, h), a, b) ──
    if isinstance(term.true_branch, OCase):
        if term.false_branch.canon() == term.true_branch.false_branch.canon():
            results.append((
                OCase(OOp('and', (term.test, term.true_branch.test)),
                      term.true_branch.true_branch, term.false_branch),
                'CASE_and_merge',
            ))

    # ── 14. Nested case with same branches: case(g1, case(g2, a, b), case(g3, a, b))
    #         → case(g2 if g1 else g3, a, b)  [when same a,b] ──
    if isinstance(term.true_branch, OCase) and isinstance(term.false_branch, OCase):
        if (term.true_branch.true_branch.canon() == term.false_branch.true_branch.canon()
                and term.true_branch.false_branch.canon() == term.false_branch.false_branch.canon()):
            merged_guard = OCase(term.test, term.true_branch.test, term.false_branch.test)
            results.append((
                OCase(merged_guard,
                      term.true_branch.true_branch,
                      term.true_branch.false_branch),
                'CASE_nested_same_branches',
            ))

    # ── 15. case(eq(x, lit), lit, x) → x  [identity case] ──
    if isinstance(term.test, OOp) and term.test.name == 'eq' and len(term.test.args) == 2:
        x_arg, lit_arg = term.test.args
        if (isinstance(lit_arg, OLit)
                and isinstance(term.true_branch, OLit)
                and term.true_branch.value == lit_arg.value
                and term.false_branch.canon() == x_arg.canon()):
            results.append((x_arg, 'CASE_eq_identity'))

    return results


def recognizes(term: OTerm) -> bool:
    """Return True if case axioms can potentially rewrite *term*."""
    return isinstance(term, OCase)


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score CASE's relevance."""
    sc = source.canon()
    tc = target.canon()
    s_case = 'case(' in sc
    t_case = 'case(' in tc
    if s_case and not t_case:
        return 0.7
    if s_case and t_case:
        return 0.5
    return 0.1


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse: expand guard expressions or wrap in case."""
    results: List[Tuple[OTerm, str]] = []

    # g → case(g, True, False)
    if isinstance(term, OOp) and term.name in ('lt', 'gt', 'lte', 'gte',
                                                 'eq', 'noteq', 'ne',
                                                 'isinstance', 'contains',
                                                 'hasattr', 'and', 'or'):
        results.append((
            OCase(term, OLit(True), OLit(False)),
            'CASE_bool_expand',
        ))

    # not(g) → case(g, False, True)
    if isinstance(term, OOp) and term.name == 'u_not' and len(term.args) == 1:
        results.append((
            OCase(term.args[0], OLit(False), OLit(True)),
            'CASE_not_expand',
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
    a, b, g = OVar('a'), OVar('b'), OVar('g')
    g1, g2 = OVar('g1'), OVar('g2')

    # case(True, a, b) → a
    t1 = OCase(OLit(True), a, b)
    r1 = apply(t1, ctx)
    _assert(any(ax == 'CASE_true' for _, ax in r1), "case true")

    # case(False, a, b) → b
    t2 = OCase(OLit(False), a, b)
    r2 = apply(t2, ctx)
    _assert(any(ax == 'CASE_false' for _, ax in r2), "case false")

    # case(g, x, x) → x
    t3 = OCase(g, a, a)
    r3 = apply(t3, ctx)
    _assert(any(ax == 'CASE_identical' for _, ax in r3), "case identical")

    # case(not(g), a, b) → case(g, b, a)
    t4 = OCase(OOp('u_not', (g,)), a, b)
    r4 = apply(t4, ctx)
    _assert(any(ax == 'CASE_not_flip' for _, ax in r4), "case not flip")

    # Guard subsumption (then)
    t5 = OCase(g, OCase(g, a, b), OVar('c'))
    r5 = apply(t5, ctx)
    _assert(any(ax == 'CASE_guard_subsume_then' for _, ax in r5), "guard subsume then")

    # Guard subsumption (else)
    t6 = OCase(g, OVar('c'), OCase(g, a, b))
    r6 = apply(t6, ctx)
    _assert(any(ax == 'CASE_guard_subsume_else' for _, ax in r6), "guard subsume else")

    # De Morgan and
    t7 = OCase(OOp('and', (g1, g2)), a, b)
    r7 = apply(t7, ctx)
    _assert(any(ax == 'CASE_demorgan_and' for _, ax in r7), "De Morgan and")

    # De Morgan or
    t8 = OCase(OOp('or', (g1, g2)), a, b)
    r8 = apply(t8, ctx)
    _assert(any(ax == 'CASE_demorgan_or' for _, ax in r8), "De Morgan or")

    # Bool collapse: case(g, True, False) → g
    t9 = OCase(g, OLit(True), OLit(False))
    r9 = apply(t9, ctx)
    _assert(any(ax == 'CASE_bool_collapse' for _, ax in r9), "bool collapse")

    # Bool negate: case(g, False, True) → not(g)
    t10 = OCase(g, OLit(False), OLit(True))
    r10 = apply(t10, ctx)
    _assert(any(ax == 'CASE_bool_negate' for _, ax in r10), "bool negate")

    # or merge: case(g, a, case(h, a, b)) → case(or(g,h), a, b)
    h = OVar('h')
    t11 = OCase(g, a, OCase(h, a, b))
    r11 = apply(t11, ctx)
    _assert(any(ax == 'CASE_or_merge' for _, ax in r11), "or merge")

    # and merge: case(g, case(h, a, b), b) → case(and(g,h), a, b)
    t12 = OCase(g, OCase(h, a, b), b)
    r12 = apply(t12, ctx)
    _assert(any(ax == 'CASE_and_merge' for _, ax in r12), "and merge")

    # Complement merge
    t13 = OCase(OOp('lt', (a, b)), OVar('x'),
                OCase(OOp('gte', (a, b)), OVar('y'), OVar('z')))
    r13 = apply(t13, ctx)
    _assert(any(ax == 'CASE_complement_merge' for _, ax in r13), "complement merge")

    # recognizes
    _assert(recognizes(t1), "recognizes OCase")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # inverse
    t14 = OOp('lt', (a, b))
    r14 = apply_inverse(t14, ctx)
    _assert(any(ax == 'CASE_bool_expand' for _, ax in r14), "bool expand")

    # eq identity: case(eq(x, 5), 5, x) → x
    x = OVar('x')
    t15 = OCase(OOp('eq', (x, OLit(5))), OLit(5), x)
    r15 = apply(t15, ctx)
    _assert(any(ax == 'CASE_eq_identity' for _, ax in r15), "eq identity")

    print(f"CASE case: {_pass} passed, {_fail} failed")
