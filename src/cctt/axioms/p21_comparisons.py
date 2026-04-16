"""P21 Axiom: Comparison Chain Equivalences.

Establishes equivalences between Python comparison patterns:
chained comparisons, membership tests, isinstance, min/max, clamp.

Mathematical basis: Python chained comparisons are conjunctions
over a totally ordered set:
    a < b < c  ≡  (a < b) ∧ (b < c)
This is the transitivity axiom of a total order.

Membership tests use the subset relation:
    x in {a, b, c}  ≡  x = a ∨ x = b ∨ x = c

min/max are the meet/join in a lattice:
    min(a, b) = a ⊓ b    max(a, b) = a ⊔ b

Key rewrites:
  • a < b and b < c  ↔  a < b < c
  • x == a or x == b or x == c  ↔  x in {a, b, c}
  • isinstance(x, (A,B,C))  ↔  isinstance(x,A) or isinstance(x,B) or isinstance(x,C)
  • min(a, max(b, x))  ↔  clamp(x, b, a)
  • a if a < b else b  ↔  min(a, b)
  • a if a > b else b  ↔  max(a, b)

(§P21, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P21_comparisons"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P13_bool_idioms", "D3_guard_reorder"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P21 Comparison Chain Equivalence).

1. a < b and b < c ≡ a < b < c
   Python evaluates chained comparisons with short-circuit and
   evaluates each operand at most once.  a < b < c is syntactic
   sugar for (a < b) and (b < c) with b evaluated once.

2. x == a or x == b or x == c ≡ x in {a, b, c}
   By definition of set membership and disjunction.
   Using a set literal enables O(1) lookup.

3. isinstance(x, (A,B,C)) ≡ isinstance(x,A) or isinstance(x,B) or isinstance(x,C)
   isinstance accepts a tuple of types as the second argument,
   returning True if x is an instance of any.

4. min(a, max(b, x)) ≡ clamp(x, b, a)  (when b ≤ a)
   clamp(x, lo, hi) = max(lo, min(hi, x)).

5. a if a < b else b ≡ min(a, b)
   By definition of min.

6. a if a > b else b ≡ max(a, b)
   By definition of max.
"""

EXAMPLES = [
    ("and(lt($a,$b), lt($b,$c))", "chain_lt($a,$b,$c)", "P21_chain_lt"),
    ("or(eq($x,$a), eq($x,$b), eq($x,$c))", "in($x, set($a,$b,$c))", "P21_eq_to_in"),
    ("case(lt($a,$b), $a, $b)", "min($a, $b)", "P21_ternary_to_min"),
    ("case(gt($a,$b), $a, $b)", "max($a, $b)", "P21_ternary_to_max"),
]

# Comparison operators
_CMP_OPS = frozenset({'lt', 'gt', 'lte', 'gte', 'eq', 'noteq',
                       'Lt', 'Gt', 'LtE', 'GtE', 'Eq', 'NotEq'})


def _is_cmp(term: OTerm, op_names: frozenset) -> Optional[Tuple[OTerm, OTerm]]:
    """Check if term is a comparison op(a, b)."""
    if isinstance(term, OOp) and term.name in op_names and len(term.args) == 2:
        return (term.args[0], term.args[1])
    return None


def _is_and_chain(term: OTerm) -> Optional[List[OTerm]]:
    """Flatten nested and() into a list of conjuncts."""
    if isinstance(term, OOp) and term.name == 'and':
        result: List[OTerm] = []
        for a in term.args:
            sub = _is_and_chain(a)
            if sub:
                result.extend(sub)
            else:
                result.append(a)
        return result
    return None


def _is_or_chain(term: OTerm) -> Optional[List[OTerm]]:
    """Flatten nested or() into a list of disjuncts."""
    if isinstance(term, OOp) and term.name == 'or':
        result: List[OTerm] = []
        for a in term.args:
            sub = _is_or_chain(a)
            if sub:
                result.extend(sub)
            else:
                result.append(a)
        return result
    return None


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P21: Comparison chain rewrites.

    Handles:
      1. and(lt(a,b), lt(b,c)) → chain_lt(a,b,c)
      2. or(eq(x,a), eq(x,b), ...) → in(x, set(a,b,...))
      3. or(isinstance(x,A), isinstance(x,B),...) → isinstance(x,(A,B,...))
      4. min(a, max(b, x)) → clamp(x, b, a)
      5. case(lt(a,b), a, b) → min(a, b)
      6. case(gt(a,b), a, b) → max(a, b)
      7. chain_lt(a,b,c) → and(lt(a,b), lt(b,c))
      8. in(x, set(a,b,...)) → or(eq(x,a), eq(x,b),...)
    """
    results: List[Tuple[OTerm, str]] = []

    # ── 1. Chained comparison: and(lt(a,b), lt(b,c)) → chain ──
    conjuncts = _is_and_chain(term)
    if conjuncts is not None and len(conjuncts) >= 2:
        # Check for adjacent comparisons with shared operand
        cmps = []
        for c in conjuncts:
            pair = _is_cmp(c, frozenset({'lt', 'Lt'}))
            if pair:
                cmps.append(('lt', pair[0], pair[1]))
            else:
                pair = _is_cmp(c, frozenset({'lte', 'LtE'}))
                if pair:
                    cmps.append(('lte', pair[0], pair[1]))

        if len(cmps) >= 2:
            # Check chain: c1.right == c2.left
            chain_elements = [cmps[0][1]]  # start with first left
            valid = True
            op_name = cmps[0][0]
            for i in range(len(cmps)):
                if i > 0 and cmps[i][1].canon() != cmps[i-1][2].canon():
                    valid = False
                    break
                if cmps[i][0] != op_name:
                    valid = False
                    break
                chain_elements.append(cmps[i][2])

            if valid and len(chain_elements) >= 3:
                results.append((
                    OOp(f'chain_{op_name}', tuple(chain_elements)),
                    'P21_and_to_chain',
                ))

    # ── 2. or(eq(x,a), eq(x,b), ...) → in(x, {a,b,...}) ──
    disjuncts = _is_or_chain(term)
    if disjuncts is not None and len(disjuncts) >= 2:
        x_canon = None
        values: List[OTerm] = []
        all_eq = True
        for d in disjuncts:
            pair = _is_cmp(d, frozenset({'eq', 'Eq'}))
            if pair is None:
                all_eq = False
                break
            left, right = pair
            if x_canon is None:
                x_canon = left.canon()
                x_term = left
            if left.canon() == x_canon:
                values.append(right)
            elif right.canon() == x_canon:
                values.append(left)
            else:
                all_eq = False
                break

        if all_eq and len(values) >= 2:
            results.append((
                OOp('in', (x_term, OOp('set_literal', tuple(values)))),
                'P21_or_eq_to_in',
            ))

    # ── 3. or(isinstance(x,A), isinstance(x,B),...) → isinstance(x,(A,B,...)) ──
    if disjuncts is not None and len(disjuncts) >= 2:
        x_canon = None
        types: List[OTerm] = []
        all_isinstance = True
        x_term_is = None
        for d in disjuncts:
            if isinstance(d, OOp) and d.name == 'isinstance' and len(d.args) == 2:
                obj, typ = d.args
                if x_canon is None:
                    x_canon = obj.canon()
                    x_term_is = obj
                if obj.canon() == x_canon:
                    types.append(typ)
                else:
                    all_isinstance = False
                    break
            else:
                all_isinstance = False
                break

        if all_isinstance and len(types) >= 2 and x_term_is is not None:
            results.append((
                OOp('isinstance', (x_term_is, OSeq(tuple(types)))),
                'P21_or_isinstance_to_tuple',
            ))

    # ── 4. min(a, max(b, x)) → clamp(x, b, a) ──
    if isinstance(term, OOp) and term.name == 'min' and len(term.args) == 2:
        a, inner = term.args
        if isinstance(inner, OOp) and inner.name == 'max' and len(inner.args) == 2:
            b, x = inner.args
            results.append((
                OOp('clamp', (x, b, a)),
                'P21_min_max_to_clamp',
            ))

    # ── 5. case(lt(a,b), a, b) → min(a, b) ──
    if isinstance(term, OCase):
        cmp = _is_cmp(term.test, frozenset({'lt', 'Lt'}))
        if cmp is not None:
            a, b = cmp
            if (term.true_branch.canon() == a.canon()
                    and term.false_branch.canon() == b.canon()):
                results.append((
                    OOp('min', (a, b)),
                    'P21_ternary_lt_to_min',
                ))

    # ── 6. case(gt(a,b), a, b) → max(a, b) ──
    if isinstance(term, OCase):
        cmp = _is_cmp(term.test, frozenset({'gt', 'Gt'}))
        if cmp is not None:
            a, b = cmp
            if (term.true_branch.canon() == a.canon()
                    and term.false_branch.canon() == b.canon()):
                results.append((
                    OOp('max', (a, b)),
                    'P21_ternary_gt_to_max',
                ))

    # ── 7. chain_lt(a,b,c) → and(lt(a,b), lt(b,c)) ──
    if isinstance(term, OOp) and term.name.startswith('chain_') and len(term.args) >= 3:
        base_op = term.name[6:]  # 'lt', 'lte', etc.
        pairs = []
        for i in range(len(term.args) - 1):
            pairs.append(OOp(base_op, (term.args[i], term.args[i+1])))
        results.append((
            OOp('and', tuple(pairs)),
            'P21_chain_to_and',
        ))

    # ── 8. in(x, set_literal(a,b,...)) → or(eq(x,a), eq(x,b),...) ──
    if isinstance(term, OOp) and term.name == 'in' and len(term.args) == 2:
        x, s = term.args
        if isinstance(s, OOp) and s.name == 'set_literal':
            eqs = tuple(OOp('eq', (x, v)) for v in s.args)
            results.append((
                OOp('or', eqs),
                'P21_in_to_or_eq',
            ))

    # ── 9. isinstance(x, (A,B,...)) → or(isinstance(x,A),...) ──
    if isinstance(term, OOp) and term.name == 'isinstance' and len(term.args) == 2:
        x, types_term = term.args
        if isinstance(types_term, OSeq) and len(types_term.elements) >= 2:
            checks = tuple(OOp('isinstance', (x, t)) for t in types_term.elements)
            results.append((
                OOp('or', checks),
                'P21_isinstance_tuple_to_or',
            ))

    # ── 10. clamp → min(a, max(b, x)) ──
    if isinstance(term, OOp) and term.name == 'clamp' and len(term.args) == 3:
        x, lo, hi = term.args
        results.append((
            OOp('min', (hi, OOp('max', (lo, x)))),
            'P21_clamp_to_min_max',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Recognizer & scoring
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    if isinstance(term, OOp):
        if term.name in ('and', 'or'):
            return True
        if term.name.startswith('chain_'):
            return True
        if term.name in ('min', 'max', 'clamp', 'isinstance', 'in'):
            return True
    if isinstance(term, OCase):
        if isinstance(term.test, OOp) and term.test.name in _CMP_OPS:
            return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    sc, tc = source.canon(), target.canon()
    if 'chain' in sc or 'chain' in tc:
        return 0.8
    if 'min' in sc and 'max' in tc or 'max' in sc and 'min' in tc:
        return 0.7
    if 'isinstance' in sc and 'isinstance' in tc:
        return 0.7
    if 'in(' in sc and ('eq(' in tc or 'or(' in tc):
        return 0.75
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse: expand chained forms back to explicit."""
    results: List[Tuple[OTerm, str]] = []

    # min(a,b) → case(lt(a,b), a, b)
    if isinstance(term, OOp) and term.name == 'min' and len(term.args) == 2:
        a, b = term.args
        results.append((
            OCase(OOp('lt', (a, b)), a, b),
            'P21_inv_min_to_ternary',
        ))

    # max(a,b) → case(gt(a,b), a, b)
    if isinstance(term, OOp) and term.name == 'max' and len(term.args) == 2:
        a, b = term.args
        results.append((
            OCase(OOp('gt', (a, b)), a, b),
            'P21_inv_max_to_ternary',
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

    # 1. and(lt(a,b), lt(b,c)) → chain_lt(a,b,c)
    t1 = OOp('and', (OOp('lt', (OVar('a'), OVar('b'))),
                      OOp('lt', (OVar('b'), OVar('c')))))
    r1 = apply(t1)
    _assert(any(a == 'P21_and_to_chain' for _, a in r1), "and → chain")

    # 2. or(eq(x,1), eq(x,2), eq(x,3)) → in(x, {1,2,3})
    t2 = OOp('or', (OOp('eq', (OVar('x'), OLit(1))),
                     OOp('eq', (OVar('x'), OLit(2))),
                     OOp('eq', (OVar('x'), OLit(3)))))
    r2 = apply(t2)
    _assert(any(a == 'P21_or_eq_to_in' for _, a in r2), "or eq → in")

    # 3. or(isinstance(x,A), isinstance(x,B)) → isinstance(x,(A,B))
    t3 = OOp('or', (OOp('isinstance', (OVar('x'), OVar('A'))),
                     OOp('isinstance', (OVar('x'), OVar('B')))))
    r3 = apply(t3)
    _assert(any(a == 'P21_or_isinstance_to_tuple' for _, a in r3), "or isinstance → tuple")

    # 4. min(a, max(b, x)) → clamp(x, b, a)
    t4 = OOp('min', (OVar('a'), OOp('max', (OVar('b'), OVar('x')))))
    r4 = apply(t4)
    _assert(any(a == 'P21_min_max_to_clamp' for _, a in r4), "min(max) → clamp")

    # 5. case(lt(a,b), a, b) → min(a, b)
    t5 = OCase(OOp('lt', (OVar('a'), OVar('b'))), OVar('a'), OVar('b'))
    r5 = apply(t5)
    _assert(any(a == 'P21_ternary_lt_to_min' for _, a in r5), "ternary lt → min")

    # 6. case(gt(a,b), a, b) → max(a, b)
    t6 = OCase(OOp('gt', (OVar('a'), OVar('b'))), OVar('a'), OVar('b'))
    r6 = apply(t6)
    _assert(any(a == 'P21_ternary_gt_to_max' for _, a in r6), "ternary gt → max")

    # 7. chain_lt → and
    t7 = OOp('chain_lt', (OVar('a'), OVar('b'), OVar('c')))
    r7 = apply(t7)
    _assert(any(a == 'P21_chain_to_and' for _, a in r7), "chain → and")

    # 8. in(x, set_literal) → or(eq)
    t8 = OOp('in', (OVar('x'), OOp('set_literal', (OLit(1), OLit(2)))))
    r8 = apply(t8)
    _assert(any(a == 'P21_in_to_or_eq' for _, a in r8), "in → or eq")

    # 9. isinstance(x, (A,B)) → or(isinstance)
    t9 = OOp('isinstance', (OVar('x'), OSeq((OVar('A'), OVar('B')))))
    r9 = apply(t9)
    _assert(any(a == 'P21_isinstance_tuple_to_or' for _, a in r9), "isinstance → or")

    # 10. clamp → min(max)
    t10 = OOp('clamp', (OVar('x'), OVar('lo'), OVar('hi')))
    r10 = apply(t10)
    _assert(any(a == 'P21_clamp_to_min_max' for _, a in r10), "clamp → min(max)")

    # 11. recognizes
    _assert(recognizes(t1), "recognizes and")
    _assert(recognizes(t4), "recognizes min")
    _assert(recognizes(t5), "recognizes case(lt)")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # 12. inverse: min → ternary
    r12 = apply_inverse(OOp('min', (OVar('a'), OVar('b'))))
    _assert(any(a == 'P21_inv_min_to_ternary' for _, a in r12), "inv min → ternary")

    # 13. inverse: max → ternary
    r13 = apply_inverse(OOp('max', (OVar('a'), OVar('b'))))
    _assert(any(a == 'P21_inv_max_to_ternary' for _, a in r13), "inv max → ternary")

    # 14. relevance
    _assert(relevance_score(t1, t7) > 0.5, "and/chain relevance")

    print(f"P21 comparisons: {_pass} passed, {_fail} failed")
