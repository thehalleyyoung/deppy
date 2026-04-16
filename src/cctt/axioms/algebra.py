"""Algebraic Rewrite Axioms — Commutativity, Associativity, Distributivity.

Fundamental algebraic identities that operate on OOp terms.
These are not dichotomy axioms but are essential for normalisation.

Key rewrites:
  • Commutativity: op(a, b) → op(b, a) for commutative ops
  • Associativity: op(op(a, b), c) ↔ op(a, op(b, c))
  • Distributivity: mul(a, add(b, c)) → add(mul(a,b), mul(a,c))
  • Absorption: and(a, or(a, b)) → a
  • Idempotence: max(a, a) → a
  • Identity: add(x, 0) → x, mul(x, 1) → x
  • Annihilation: mul(x, 0) → 0, and(x, False) → False
  • Involution: not(not(x)) → x
  • Comparison flips: lt(a,b) ↔ gt(b,a)
  • De Morgan: not(and(a,b)) ↔ or(not(a), not(b))
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "ALG_algebra"
AXIOM_CATEGORY = "utility"

SOUNDNESS_PROOF = """
Standard algebraic identities. Commutativity and associativity hold
for operations that are algebraically commutative/associative.

IMPORTANT: add is only commutative on NUMERIC fibers — string/list
concatenation is NOT commutative. The axiom is fiber-aware via
the FiberCtx parameter (§2.6 sheaf descent).

Distributivity of * over + holds in any ring.
Absorption, idempotence hold in any lattice.
De Morgan holds in any Boolean algebra.
"""

COMPOSES_WITH = ["FOLD", "CASE", "D19_sort_scan", "D20_spec", "D24_eta"]
REQUIRES: List[str] = []

EXAMPLES = [
    ("add(b, a)", "add(a, b)", "ALG_commute"),
    ("add(add(a, b), c)", "add(a, add(b, c))", "ALG_assoc_right"),
    ("mul(a, add(b, c))", "add(mul(a,b), mul(a,c))", "ALG_distribute_mul_add"),
    ("and(a, or(a, b))", "a", "ALG_absorb_and_or"),
    ("max(x, x)", "x", "ALG_idempotent"),
]

# ── Op classification ────────────────────────────────────────

ALWAYS_COMMUTATIVE: FrozenSet[str] = frozenset({
    'mul', 'mult', '.mul', 'imul',
    'and', 'or',
    'min', 'max', 'eq', 'noteq',
    'union', 'intersection',
    'gcd', 'lcm',
})

# bitor/bitand/bitxor commutative on int, NOT on dict (| is merge)
FIBER_COMMUTATIVE: FrozenSet[str] = frozenset({
    'add', '.add', 'iadd',
    'bitor', 'bitand', 'bitxor',
})

ALWAYS_ASSOCIATIVE: FrozenSet[str] = frozenset({
    'mul', 'mult', '.mul', 'imul',
    'and', 'or',
    'min', 'max', 'concat',
    'union', 'intersection',
    'gcd', 'lcm',
})

# bitor/bitand/bitxor associative on int, NOT on dict
FIBER_ASSOCIATIVE: FrozenSet[str] = frozenset({
    'add', '.add', 'iadd',
    'bitor', 'bitand', 'bitxor',
})

IDEMPOTENT_OPS: FrozenSet[str] = frozenset({
    'min', 'max', 'and', 'or',
    'union', 'intersection', 'gcd', 'lcm',
})

IDENTITY_ELEMENTS: Dict[str, Any] = {
    'add': 0, '.add': 0, 'iadd': 0,
    'sub': 0,
    'mul': 1, '.mul': 1, 'imul': 1, 'mult': 1,
    'and': True, 'or': False,
    'bitor': 0, 'bitand': -1, 'bitxor': 0,
    'min': float('inf'), 'max': float('-inf'),
    'concat': '',
    'gcd': 0, 'lcm': 1,
}

COMP_FLIP: Dict[str, str] = {
    'lt': 'gt', 'gt': 'lt', 'lte': 'gte', 'gte': 'lte',
    'le': 'ge', 'ge': 'le',
}


@dataclass
class FiberCtx:
    param_duck_types: Dict[str, str] = field(default_factory=dict)

    def is_numeric(self, term: OTerm) -> bool:
        params = _extract_params(term)
        if not params:
            return True
        for p in params:
            dt = self.param_duck_types.get(p, 'any')
            if dt not in ('int', 'float', 'number'):
                return False
        return True


def _extract_params(term: OTerm) -> Set[str]:
    if isinstance(term, OVar):
        return {term.name} if term.name.startswith('p') else set()
    if isinstance(term, OOp):
        r: Set[str] = set()
        for a in term.args:
            r |= _extract_params(a)
        return r
    if isinstance(term, OCase):
        return (_extract_params(term.test)
                | _extract_params(term.true_branch)
                | _extract_params(term.false_branch))
    if isinstance(term, OFold):
        return _extract_params(term.init) | _extract_params(term.collection)
    return set()


def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply algebraic rewrite rules to *term*."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp):
        return results

    # Determine commutative/associative sets based on fiber
    # IMPORTANT: use is_integer, NOT is_numeric — float addition is
    # not associative/commutative in IEEE 754 (different rounding).
    commutative_ops = set(ALWAYS_COMMUTATIVE)
    assoc_ops = set(ALWAYS_ASSOCIATIVE)
    if hasattr(ctx, 'is_integer') and ctx.is_integer(term):
        commutative_ops |= FIBER_COMMUTATIVE
        assoc_ops |= FIBER_ASSOCIATIVE

    # ── 1. Commutativity: op(a, b) → op(b, a) ──
    if term.name in commutative_ops and len(term.args) == 2:
        swapped = OOp(term.name, (term.args[1], term.args[0]))
        if swapped.canon() != term.canon():
            results.append((swapped, 'ALG_commute'))

    # ── 2. Associativity: op(op(a,b), c) → op(a, op(b,c)) ──
    if term.name in assoc_ops and len(term.args) == 2:
        if isinstance(term.args[0], OOp) and term.args[0].name == term.name:
            inner = term.args[0]
            if len(inner.args) == 2:
                right_assoc = OOp(term.name, (
                    inner.args[0],
                    OOp(term.name, (inner.args[1], term.args[1])),
                ))
                results.append((right_assoc, 'ALG_assoc_right'))

    # op(a, op(b,c)) → op(op(a,b), c) [left associativity]
    if term.name in assoc_ops and len(term.args) == 2:
        if isinstance(term.args[1], OOp) and term.args[1].name == term.name:
            inner = term.args[1]
            if len(inner.args) == 2:
                left_assoc = OOp(term.name, (
                    OOp(term.name, (term.args[0], inner.args[0])),
                    inner.args[1],
                ))
                results.append((left_assoc, 'ALG_assoc_left'))

    # ── 3. Identity elements: add(x, 0) → x, mul(x, 1) → x ──
    if term.name in ('add', '.add', 'iadd', 'sub') and len(term.args) == 2:
        if isinstance(term.args[1], OLit) and term.args[1].value == 0:
            results.append((term.args[0], 'ALG_identity_zero'))
        if isinstance(term.args[0], OLit) and term.args[0].value == 0 and term.name != 'sub':
            results.append((term.args[1], 'ALG_identity_zero_left'))

    if term.name in ('mul', 'mult', '.mul', 'imul') and len(term.args) == 2:
        if isinstance(term.args[1], OLit) and term.args[1].value == 1:
            results.append((term.args[0], 'ALG_identity_one'))
        if isinstance(term.args[0], OLit) and term.args[0].value == 1:
            results.append((term.args[1], 'ALG_identity_one_left'))

    # ── 4. Annihilation: mul(x, 0) → 0, and(x, False) → False ──
    if term.name in ('mul', 'mult', '.mul', 'imul') and len(term.args) == 2:
        for i in range(2):
            if isinstance(term.args[i], OLit) and term.args[i].value == 0:
                results.append((OLit(0), 'ALG_annihilate_zero'))
                break

    if term.name == 'and' and len(term.args) == 2:
        for i in range(2):
            if isinstance(term.args[i], OLit) and term.args[i].value is False:
                results.append((OLit(False), 'ALG_annihilate_false'))
                break

    if term.name == 'or' and len(term.args) == 2:
        for i in range(2):
            if isinstance(term.args[i], OLit) and term.args[i].value is True:
                results.append((OLit(True), 'ALG_annihilate_true'))
                break

    # ── 5. Involution: not(not(x)) → x ──
    if term.name == 'u_not' and len(term.args) == 1:
        if isinstance(term.args[0], OOp) and term.args[0].name == 'u_not':
            results.append((term.args[0].args[0], 'ALG_not_involution'))

    # neg(neg(x)) → x
    if term.name == 'u_neg' and len(term.args) == 1:
        if isinstance(term.args[0], OOp) and term.args[0].name == 'u_neg':
            results.append((term.args[0].args[0], 'ALG_neg_involution'))

    # ── 6. Comparison flips: lt(a,b) ↔ gt(b,a) ──
    if term.name in COMP_FLIP and len(term.args) == 2:
        flipped = OOp(COMP_FLIP[term.name], (term.args[1], term.args[0]))
        results.append((flipped, 'ALG_comp_flip'))

    # ── 7. Absorption: and(a, or(a, b)) → a ──
    if term.name == 'and' and len(term.args) == 2:
        a, rhs = term.args
        if isinstance(rhs, OOp) and rhs.name == 'or' and len(rhs.args) == 2:
            if a.canon() in (rhs.args[0].canon(), rhs.args[1].canon()):
                results.append((a, 'ALG_absorb_and_or'))
        # Symmetric: and(or(a,b), a) → a
        lhs = term.args[0]
        if isinstance(lhs, OOp) and lhs.name == 'or' and len(lhs.args) == 2:
            b2 = term.args[1]
            if b2.canon() in (lhs.args[0].canon(), lhs.args[1].canon()):
                results.append((b2, 'ALG_absorb_and_or_sym'))

    if term.name == 'or' and len(term.args) == 2:
        a, rhs = term.args
        if isinstance(rhs, OOp) and rhs.name == 'and' and len(rhs.args) == 2:
            if a.canon() in (rhs.args[0].canon(), rhs.args[1].canon()):
                results.append((a, 'ALG_absorb_or_and'))

    # ── 8. Idempotence: max(a, a) → a, min(a, a) → a ──
    if term.name in IDEMPOTENT_OPS and len(term.args) == 2:
        if term.args[0].canon() == term.args[1].canon():
            results.append((term.args[0], 'ALG_idempotent'))

    # ── 9. Distributivity: mul(a, add(b, c)) → add(mul(a,b), mul(a,c)) ──
    if term.name in ('mul', 'mult', '.mul') and len(term.args) == 2:
        a, rhs = term.args
        if isinstance(rhs, OOp) and rhs.name in ('add', '.add') and len(rhs.args) == 2:
            b, c = rhs.args
            results.append((
                OOp(rhs.name, (OOp(term.name, (a, b)), OOp(term.name, (a, c)))),
                'ALG_distribute_mul_add',
            ))
        # Right distributivity: mul(add(b, c), a) → add(mul(b,a), mul(c,a))
        lhs = term.args[0]
        if isinstance(lhs, OOp) and lhs.name in ('add', '.add') and len(lhs.args) == 2:
            b, c = lhs.args
            a2 = term.args[1]
            results.append((
                OOp(lhs.name, (OOp(term.name, (b, a2)), OOp(term.name, (c, a2)))),
                'ALG_distribute_mul_add_right',
            ))

    # ── 10. Factoring (inverse of distributivity):
    #         add(mul(a,b), mul(a,c)) → mul(a, add(b,c)) ──
    if term.name in ('add', '.add') and len(term.args) == 2:
        lhs, rhs = term.args
        if (isinstance(lhs, OOp) and isinstance(rhs, OOp)
                and lhs.name in ('mul', 'mult', '.mul')
                and rhs.name in ('mul', 'mult', '.mul')
                and len(lhs.args) == 2 and len(rhs.args) == 2):
            if lhs.args[0].canon() == rhs.args[0].canon():
                results.append((
                    OOp(lhs.name, (lhs.args[0], OOp(term.name, (lhs.args[1], rhs.args[1])))),
                    'ALG_factor_left',
                ))
            if lhs.args[1].canon() == rhs.args[1].canon():
                results.append((
                    OOp(lhs.name, (OOp(term.name, (lhs.args[0], rhs.args[0])), lhs.args[1])),
                    'ALG_factor_right',
                ))

    # ── 11. De Morgan: not(and(a,b)) → or(not(a), not(b)) ──
    if term.name == 'u_not' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'and' and len(inner.args) == 2:
            results.append((
                OOp('or', (OOp('u_not', (inner.args[0],)),
                           OOp('u_not', (inner.args[1],)))),
                'ALG_demorgan_and',
            ))
        if isinstance(inner, OOp) and inner.name == 'or' and len(inner.args) == 2:
            results.append((
                OOp('and', (OOp('u_not', (inner.args[0],)),
                            OOp('u_not', (inner.args[1],)))),
                'ALG_demorgan_or',
            ))

    # ── 12. Self-subtraction/division: sub(x, x) → 0, div(x, x) → 1 ──
    if term.name == 'sub' and len(term.args) == 2:
        if term.args[0].canon() == term.args[1].canon():
            results.append((OLit(0), 'ALG_self_subtract'))

    if term.name in ('truediv', 'floordiv', 'div') and len(term.args) == 2:
        if term.args[0].canon() == term.args[1].canon():
            results.append((OLit(1), 'ALG_self_divide'))

    return results


def recognizes(term: OTerm) -> bool:
    """Return True if algebraic axioms can potentially rewrite *term*."""
    return isinstance(term, OOp)


def relevance_score(source: OTerm, target: OTerm) -> float:
    """ALG is always somewhat relevant when ops differ."""
    sc = source.canon()
    tc = target.canon()
    depth_diff = abs(sc.count('(') - tc.count('('))
    return min(0.5 + depth_diff * 0.05, 0.9)


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse direction for select rules — same as apply for involutions."""
    return apply(term, ctx)


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

    ctx = FiberCtx(param_duck_types={'p0': 'int', 'p1': 'int'})
    a, b, c, x = OVar('a'), OVar('b'), OVar('c'), OVar('x')

    # Commutativity
    t1 = OOp('mul', (b, a))
    r1 = apply(t1, ctx)
    _assert(any(ax == 'ALG_commute' for _, ax in r1), "commute mul(b,a)")

    # Associativity right
    t2 = OOp('mul', (OOp('mul', (a, b)), c))
    r2 = apply(t2, ctx)
    _assert(any(ax == 'ALG_assoc_right' for _, ax in r2), "assoc right")

    # Associativity left
    t3 = OOp('mul', (a, OOp('mul', (b, c))))
    r3 = apply(t3, ctx)
    _assert(any(ax == 'ALG_assoc_left' for _, ax in r3), "assoc left")

    # Identity zero
    t4 = OOp('add', (x, OLit(0)))
    r4 = apply(t4, ctx)
    _assert(any(ax == 'ALG_identity_zero' for _, ax in r4), "identity add 0")

    # Identity one
    t5 = OOp('mul', (x, OLit(1)))
    r5 = apply(t5, ctx)
    _assert(any(ax == 'ALG_identity_one' for _, ax in r5), "identity mul 1")

    # Annihilation zero
    t6 = OOp('mul', (x, OLit(0)))
    r6 = apply(t6, ctx)
    _assert(any(ax == 'ALG_annihilate_zero' for _, ax in r6), "annihilate zero")

    # Annihilation false
    t7 = OOp('and', (x, OLit(False)))
    r7 = apply(t7, ctx)
    _assert(any(ax == 'ALG_annihilate_false' for _, ax in r7), "annihilate false")

    # Annihilation true
    t8 = OOp('or', (x, OLit(True)))
    r8 = apply(t8, ctx)
    _assert(any(ax == 'ALG_annihilate_true' for _, ax in r8), "annihilate true")

    # Involution not
    t9 = OOp('u_not', (OOp('u_not', (x,)),))
    r9 = apply(t9, ctx)
    _assert(any(ax == 'ALG_not_involution' for _, ax in r9), "not involution")

    # Comparison flip
    t10 = OOp('lt', (a, b))
    r10 = apply(t10, ctx)
    _assert(any(ax == 'ALG_comp_flip' for _, ax in r10), "comp flip lt→gt")

    # Absorption and(a, or(a, b)) → a
    t11 = OOp('and', (a, OOp('or', (a, b))))
    r11 = apply(t11, ctx)
    _assert(any(ax == 'ALG_absorb_and_or' for _, ax in r11), "absorption and/or")

    # Idempotence max(x, x) → x
    t12 = OOp('max', (x, x))
    r12 = apply(t12, ctx)
    _assert(any(ax == 'ALG_idempotent' for _, ax in r12), "idempotent max")

    # Distributivity
    t13 = OOp('mul', (a, OOp('add', (b, c))))
    r13 = apply(t13, ctx)
    _assert(any(ax == 'ALG_distribute_mul_add' for _, ax in r13), "distributivity")

    # Factoring
    t14 = OOp('add', (OOp('mul', (a, b)), OOp('mul', (a, c))))
    r14 = apply(t14, ctx)
    _assert(any(ax == 'ALG_factor_left' for _, ax in r14), "factoring left")

    # De Morgan
    t15 = OOp('u_not', (OOp('and', (a, b)),))
    r15 = apply(t15, ctx)
    _assert(any(ax == 'ALG_demorgan_and' for _, ax in r15), "De Morgan and")

    t16 = OOp('u_not', (OOp('or', (a, b)),))
    r16 = apply(t16, ctx)
    _assert(any(ax == 'ALG_demorgan_or' for _, ax in r16), "De Morgan or")

    # Self-subtraction
    t17 = OOp('sub', (x, x))
    r17 = apply(t17, ctx)
    _assert(any(ax == 'ALG_self_subtract' for _, ax in r17), "self subtract")

    # Self-division
    t18 = OOp('truediv', (x, x))
    r18 = apply(t18, ctx)
    _assert(any(ax == 'ALG_self_divide' for _, ax in r18), "self divide")

    # Neg involution
    t19 = OOp('u_neg', (OOp('u_neg', (x,)),))
    r19 = apply(t19, ctx)
    _assert(any(ax == 'ALG_neg_involution' for _, ax in r19), "neg involution")

    # recognizes
    _assert(recognizes(t1), "recognizes OOp")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    print(f"ALG algebra: {_pass} passed, {_fail} failed")
