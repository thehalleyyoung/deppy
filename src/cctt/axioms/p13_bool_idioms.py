"""P13 Axiom: Boolean / Truthiness Idiom Equivalences.

Establishes equivalences between different Python truthiness and
boolean patterns, canonicalizing them to minimal forms.

Mathematical basis: Python truthiness defines a natural
transformation  τ : Ob(Py) → Bool  where τ(x) maps every Python
object to {True, False} via __bool__ / __len__.  The axiom
canonicalizes expressions that use this transformation:
    bool(x) ≡ x != 0         (for int)
    bool(x) ≡ len(x) > 0     (for collections)
    bool(x) ≡ x is not None  (for optional)

Key rewrites:
  • if x: return True; else: return False  →  return bool(x)
  • x if x else y                         →  x or y
  • not not x                             →  bool(x)
  • any(x == val for x in xs)             →  val in xs
  • all(x != val for x in xs)             →  val not in xs
  • 0, "", [], {}, None, False            →  falsy constants

(§P13, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P13_bool_idioms"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["D3_guard_reorder", "D21_dispatch", "D24_eta"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P13 Boolean Idiom Equivalence).

Python defines truthiness via __bool__ and __len__:
  - For int: bool(n) = (n != 0)
  - For str: bool(s) = (len(s) > 0) = (s != "")
  - For list/dict/set: bool(c) = (len(c) > 0)
  - For None: bool(None) = False

1. if x: return True; else: return False
   ≡ return bool(x)
   By definition of __bool__.

2. x if x else y ≡ x or y
   Python or returns the first truthy operand, else the last.
   When test = body = x, this is exactly 'or' semantics.

3. not not x ≡ bool(x)
   not x = ¬τ(x), not not x = ¬¬τ(x) = τ(x) = bool(x).

4. any(x == val for x in xs) ≡ val in xs
   By definition of __contains__ / any.

5. all(x != val for x in xs) ≡ val not in xs
   ¬∃x∈xs. x=val ≡ ∀x∈xs. x≠val ≡ val ∉ xs.
"""

EXAMPLES = [
    ("case($x, True, False)", "bool($x)", "P13_if_to_bool"),
    ("u_not(u_not($x))", "bool($x)", "P13_double_not"),
    ("case($x, $x, $y)", "or($x, $y)", "P13_ternary_to_or"),
    ("any(map(λ(v).eq(v,val), xs))", "in(val, xs)", "P13_any_eq_to_in"),
    ("all(map(λ(v).noteq(v,val), xs))", "notin(val, xs)", "P13_all_neq_to_notin"),
]

# ── Falsy constants ─────────────────────────────────────────

_FALSY_VALUES = frozenset({0, 0.0, "", False, None, b"", ()})


def _is_falsy_literal(term: OTerm) -> bool:
    """Check if term is a known falsy literal."""
    if isinstance(term, OLit) and term.value in _FALSY_VALUES:
        return True
    if isinstance(term, OSeq) and len(term.elements) == 0:
        return True
    if isinstance(term, ODict) and len(term.pairs) == 0:
        return True
    return False


def _is_truthy_literal(term: OTerm) -> bool:
    """Check if term is a known truthy literal (non-zero, non-empty)."""
    if isinstance(term, OLit):
        if term.value is True:
            return True
        if isinstance(term.value, (int, float)) and term.value != 0:
            return True
        if isinstance(term.value, str) and term.value != "":
            return True
    if isinstance(term, OSeq) and len(term.elements) > 0:
        return True
    if isinstance(term, ODict) and len(term.pairs) > 0:
        return True
    return False


def _is_bool_true(term: OTerm) -> bool:
    return isinstance(term, OLit) and term.value is True


def _is_bool_false(term: OTerm) -> bool:
    return isinstance(term, OLit) and term.value is False


def _is_double_not(term: OTerm) -> Optional[OTerm]:
    """Detect not(not(x)) → x."""
    if (isinstance(term, OOp) and term.name == 'u_not'
            and len(term.args) == 1):
        inner = term.args[0]
        if (isinstance(inner, OOp) and inner.name == 'u_not'
                and len(inner.args) == 1):
            return inner.args[0]
    return None


def _is_any_eq_pattern(term: OTerm) -> Optional[Tuple[OTerm, OTerm]]:
    """Detect any(x == val for x in xs) → (val, xs)."""
    if isinstance(term, OOp) and term.name == 'any' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OMap) and isinstance(inner.transform, OLam):
            lam = inner.transform
            if len(lam.params) == 1:
                body = lam.body
                if (isinstance(body, OOp) and body.name in ('eq', 'Eq')
                        and len(body.args) == 2):
                    a, b = body.args
                    p = lam.params[0]
                    if isinstance(a, OVar) and a.name == p:
                        return (b, inner.collection)
                    if isinstance(b, OVar) and b.name == p:
                        return (a, inner.collection)
    return None


def _is_all_neq_pattern(term: OTerm) -> Optional[Tuple[OTerm, OTerm]]:
    """Detect all(x != val for x in xs) → (val, xs)."""
    if isinstance(term, OOp) and term.name == 'all' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OMap) and isinstance(inner.transform, OLam):
            lam = inner.transform
            if len(lam.params) == 1:
                body = lam.body
                if (isinstance(body, OOp) and body.name in ('noteq', 'NotEq')
                        and len(body.args) == 2):
                    a, b = body.args
                    p = lam.params[0]
                    if isinstance(a, OVar) and a.name == p:
                        return (b, inner.collection)
                    if isinstance(b, OVar) and b.name == p:
                        return (a, inner.collection)
    return None


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P13: Boolean idiom rewrites.

    Handles:
      1. case(x, True, False) → bool(x)
      2. case(x, False, True) → not(x)
      3. not(not(x)) → bool(x)
      4. case(x, x, y) → or(x, y)  (ternary to or)
      5. any(eq pattern) → in
      6. all(neq pattern) → not in
      7. bool(bool(x)) → bool(x)  (idempotent)
      8. bool(falsy) → False
      9. bool(truthy) → True
     10. if falsy → dead branch elimination
    """
    results: List[Tuple[OTerm, str]] = []

    # ── 1. case(x, True, False) → bool(x) ──
    if isinstance(term, OCase):
        if _is_bool_true(term.true_branch) and _is_bool_false(term.false_branch):
            results.append((
                OOp('bool', (term.test,)),
                'P13_if_true_false_to_bool',
            ))
        # ── 2. case(x, False, True) → not(x) ──
        if _is_bool_false(term.true_branch) and _is_bool_true(term.false_branch):
            results.append((
                OOp('u_not', (term.test,)),
                'P13_if_false_true_to_not',
            ))
        # ── 4. case(x, x, y) → or(x, y) ──
        if term.test.canon() == term.true_branch.canon():
            results.append((
                OOp('or', (term.test, term.false_branch)),
                'P13_ternary_to_or',
            ))
        # ── 10. case(falsy, a, b) → b ──
        if _is_falsy_literal(term.test):
            results.append((term.false_branch, 'P13_dead_true_branch'))
        # ── 10b. case(truthy, a, b) → a ──
        if _is_truthy_literal(term.test):
            results.append((term.true_branch, 'P13_dead_false_branch'))

    # ── 3. not(not(x)) → bool(x) ──
    inner = _is_double_not(term)
    if inner is not None:
        results.append((
            OOp('bool', (inner,)),
            'P13_double_not_to_bool',
        ))

    # ── 5. any(x == val for x in xs) → val in xs ──
    any_match = _is_any_eq_pattern(term)
    if any_match is not None:
        val, xs = any_match
        results.append((
            OOp('in', (val, xs)),
            'P13_any_eq_to_in',
        ))

    # ── 6. all(x != val for x in xs) → val not in xs ──
    all_match = _is_all_neq_pattern(term)
    if all_match is not None:
        val, xs = all_match
        results.append((
            OOp('notin', (val, xs)),
            'P13_all_neq_to_notin',
        ))

    # ── 7. bool(bool(x)) → bool(x) ──
    if (isinstance(term, OOp) and term.name == 'bool'
            and len(term.args) == 1):
        inner_arg = term.args[0]
        if (isinstance(inner_arg, OOp) and inner_arg.name == 'bool'
                and len(inner_arg.args) == 1):
            results.append((
                inner_arg,
                'P13_bool_idempotent',
            ))
        # ── 8. bool(falsy) → False ──
        if _is_falsy_literal(inner_arg):
            results.append((OLit(False), 'P13_bool_falsy'))
        # ── 9. bool(truthy) → True ──
        if _is_truthy_literal(inner_arg):
            results.append((OLit(True), 'P13_bool_truthy'))

    return results


# ═══════════════════════════════════════════════════════════
# Recognizer & scoring
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could P13 apply to this term?"""
    if isinstance(term, OCase):
        return True
    if isinstance(term, OOp):
        if term.name in ('u_not', 'bool', 'any', 'all'):
            return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Heuristic 0.0–1.0 for how likely P13 helps bridge source→target."""
    sc, tc = source.canon(), target.canon()
    if 'bool' in sc or 'bool' in tc:
        return 0.7
    if 'case' in sc and ('bool' in tc or 'or' in tc):
        return 0.8
    if 'u_not(u_not' in sc:
        return 0.9
    if 'any(' in sc and 'in(' in tc:
        return 0.85
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse: expand canonical boolean forms back to verbose."""
    results: List[Tuple[OTerm, str]] = []

    # bool(x) → case(x, True, False)
    if isinstance(term, OOp) and term.name == 'bool' and len(term.args) == 1:
        results.append((
            OCase(term.args[0], OLit(True), OLit(False)),
            'P13_inv_bool_to_case',
        ))

    # or(x, y) → case(x, x, y)
    if isinstance(term, OOp) and term.name == 'or' and len(term.args) == 2:
        x, y = term.args
        results.append((
            OCase(x, x, y),
            'P13_inv_or_to_ternary',
        ))

    # in(val, xs) → any(map(λv.eq(v,val), xs))
    if isinstance(term, OOp) and term.name == 'in' and len(term.args) == 2:
        val, xs = term.args
        lam = OLam(('_v',), OOp('eq', (OVar('_v'), val)))
        results.append((
            OOp('any', (OMap(lam, xs),)),
            'P13_inv_in_to_any',
        ))

    # notin(val, xs) → all(map(λv.noteq(v,val), xs))
    if isinstance(term, OOp) and term.name == 'notin' and len(term.args) == 2:
        val, xs = term.args
        lam = OLam(('_v',), OOp('noteq', (OVar('_v'), val)))
        results.append((
            OOp('all', (OMap(lam, xs),)),
            'P13_inv_notin_to_all',
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

    # 1. case(x, True, False) → bool(x)
    t1 = OCase(OVar('x'), OLit(True), OLit(False))
    r1 = apply(t1)
    _assert(any(a == 'P13_if_true_false_to_bool' for _, a in r1), "if T/F → bool")

    # 2. case(x, False, True) → not(x)
    t2 = OCase(OVar('x'), OLit(False), OLit(True))
    r2 = apply(t2)
    _assert(any(a == 'P13_if_false_true_to_not' for _, a in r2), "if F/T → not")

    # 3. not(not(x)) → bool(x)
    t3 = OOp('u_not', (OOp('u_not', (OVar('x'),)),))
    r3 = apply(t3)
    _assert(any(a == 'P13_double_not_to_bool' for _, a in r3), "double not → bool")

    # 4. case(x, x, y) → or(x, y)
    t4 = OCase(OVar('x'), OVar('x'), OVar('y'))
    r4 = apply(t4)
    _assert(any(a == 'P13_ternary_to_or' for _, a in r4), "ternary → or")

    # 5. any(eq) → in
    lam5 = OLam(('v',), OOp('eq', (OVar('v'), OVar('val'))))
    t5 = OOp('any', (OMap(lam5, OVar('xs')),))
    r5 = apply(t5)
    _assert(any(a == 'P13_any_eq_to_in' for _, a in r5), "any(eq) → in")

    # 6. all(neq) → notin
    lam6 = OLam(('v',), OOp('noteq', (OVar('v'), OVar('val'))))
    t6 = OOp('all', (OMap(lam6, OVar('xs')),))
    r6 = apply(t6)
    _assert(any(a == 'P13_all_neq_to_notin' for _, a in r6), "all(neq) → notin")

    # 7. bool(bool(x)) → bool(x)
    t7 = OOp('bool', (OOp('bool', (OVar('x'),)),))
    r7 = apply(t7)
    _assert(any(a == 'P13_bool_idempotent' for _, a in r7), "bool idempotent")

    # 8. bool(0) → False
    t8 = OOp('bool', (OLit(0),))
    r8 = apply(t8)
    _assert(any(a == 'P13_bool_falsy' for _, a in r8), "bool(0) → False")

    # 9. bool(1) → True
    t9 = OOp('bool', (OLit(1),))
    r9 = apply(t9)
    _assert(any(a == 'P13_bool_truthy' for _, a in r9), "bool(1) → True")

    # 10. case(0, a, b) → b
    t10 = OCase(OLit(0), OVar('a'), OVar('b'))
    r10 = apply(t10)
    _assert(any(a == 'P13_dead_true_branch' for _, a in r10), "dead true branch")

    # 11. case(1, a, b) → a
    t11 = OCase(OLit(1), OVar('a'), OVar('b'))
    r11 = apply(t11)
    _assert(any(a == 'P13_dead_false_branch' for _, a in r11), "dead false branch")

    # 12. recognizes
    _assert(recognizes(t1), "recognizes case")
    _assert(recognizes(t3), "recognizes u_not")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # 13. relevance
    _assert(relevance_score(t3, OOp('bool', (OVar('x'),))) > 0.5, "relevance high")

    # 14. inverse: bool(x) → case(x, True, False)
    t14 = OOp('bool', (OVar('x'),))
    r14 = apply_inverse(t14)
    _assert(any(a == 'P13_inv_bool_to_case' for _, a in r14), "inv bool → case")

    # 15. inverse: in → any
    t15 = OOp('in', (OVar('val'), OVar('xs')))
    r15 = apply_inverse(t15)
    _assert(any(a == 'P13_inv_in_to_any' for _, a in r15), "inv in → any")

    print(f"P13 bool_idioms: {_pass} passed, {_fail} failed")
