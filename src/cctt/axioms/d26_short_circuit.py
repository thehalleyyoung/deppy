"""D26: Short-Circuit Simplification — Boolean ↔ Conditional Normal Forms.

§25.2 of the CCTT monograph.  Theorem 25.2.1:
Short-circuit evaluation of Boolean connectives is equivalent to
conditional branching, and can be simplified via Boolean algebra.

Key rewrites:
  • (a and b) ↔ (b if a else False)  — and-as-conditional
  • (a or b)  ↔ (True if a else b)   — or-as-conditional
  • not (a and b) ↔ (not a) or (not b) — De Morgan
  • not (a or b)  ↔ (not a) and (not b) — De Morgan
  • (a or True) → True, (a and False) → False — absorption
  • Boolean chain flattening: a and (b and c) ↔ and(a, b, c)
  • not (not a) → a — double negation elimination
  • Guard-to-boolean: if x: return True; else: return False → bool(x)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "D26_short_circuit"
AXIOM_CATEGORY = "control_flow"

SOUNDNESS_PROOF = r"""
Theorem 25.2.1 (Short-Circuit Equivalence).
In a Boolean algebra B:
  1. a ∧ b = if a then b else ⊥   (by short-circuit semantics of ∧)
  2. a ∨ b = if a then ⊤ else b   (by short-circuit semantics of ∨)

De Morgan's Laws (truth-table verified):
  ¬(a ∧ b) = ¬a ∨ ¬b
  ¬(a ∨ b) = ¬a ∧ ¬b

Absorption:
  a ∧ ⊥ = ⊥,  a ∨ ⊤ = ⊤     (by identity/annihilator laws)

Double negation:
  ¬¬a = a  (involution of complement in B)

Associativity:
  a ∧ (b ∧ c) = (a ∧ b) ∧ c   (associativity of ∧ in B)

Guard-to-boolean:
  case(x, True, False) = bool(x) since the branches are exactly
  the truth values, so the conditional reduces to the test itself.  □
"""

COMPOSES_WITH = ["D3_guard_reorder", "D7_tailrec", "D27_early_return"]
REQUIRES: List[str] = []

EXAMPLES = [
    ("and(a, b)", "case(a, b, False)", "D26_and_to_case"),
    ("or(a, b)", "case(a, True, b)", "D26_or_to_case"),
    ("u_not(and(a, b))", "or(u_not(a), u_not(b))", "D26_demorgan_and"),
    ("u_not(or(a, b))", "and(u_not(a), u_not(b))", "D26_demorgan_or"),
    ("and(a, False)", "False", "D26_absorb_and_false"),
    ("or(a, True)", "True", "D26_absorb_or_true"),
    ("u_not(u_not(a))", "a", "D26_double_neg"),
    ("case(x, True, False)", "bool(x)", "D26_guard_to_bool"),
]


@dataclass
class FiberCtx:
    param_duck_types: Dict[str, str] = field(default_factory=dict)

    def is_numeric(self, term: OTerm) -> bool:
        return True


def _is_lit_bool(term: OTerm, val: bool) -> bool:
    """Check if term is OLit(True) or OLit(False)."""
    return isinstance(term, OLit) and term.value is val


def _flatten_bool_chain(term: OTerm, op_name: str) -> List[OTerm]:
    """Flatten nested and/or into a flat list of operands."""
    if isinstance(term, OOp) and term.name == op_name:
        result: List[OTerm] = []
        for a in term.args:
            result.extend(_flatten_bool_chain(a, op_name))
        return result
    return [term]


def _build_bool_chain(op_name: str, operands: List[OTerm]) -> OTerm:
    """Build a left-associative chain from a flat list."""
    assert len(operands) >= 2
    result = OOp(op_name, (operands[0], operands[1]))
    for op in operands[2:]:
        result = OOp(op_name, (result, op))
    return result


# ═══════════════════════════════════════════════════════════
# Core axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D26 short-circuit simplification rewrites to *term*.

    Handles:
      1. and(a, b) → case(a, b, False)
      2. or(a, b) → case(a, True, b)
      3. De Morgan: not(and(a,b)) → or(not a, not b)
      4. De Morgan: not(or(a,b)) → and(not a, not b)
      5. Absorption: and(_, False) → False, or(_, True) → True
      6. Double negation: not(not(a)) → a
      7. Guard-to-bool: case(x, True, False) → bool(x)
      8. Bool-to-guard: bool(x) → case(x, True, False)
      9. Chain flattening: and(a, and(b, c)) → and(a, b, c)
     10. Idempotence: and(a, a) → a, or(a, a) → a
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    if isinstance(term, OOp):
        # ── 1. and(a, b) → case(a, b, False) ──
        if term.name == 'and' and len(term.args) == 2:
            a, b = term.args
            results.append((
                OCase(a, b, OLit(False)),
                'D26_and_to_case',
            ))
            # Absorption: and(_, False) → False
            if _is_lit_bool(b, False):
                results.append((OLit(False), 'D26_absorb_and_false_r'))
            if _is_lit_bool(a, False):
                results.append((OLit(False), 'D26_absorb_and_false_l'))
            # Identity: and(_, True) → other
            if _is_lit_bool(b, True):
                results.append((a, 'D26_and_true_r'))
            if _is_lit_bool(a, True):
                results.append((b, 'D26_and_true_l'))
            # Idempotence
            if a.canon() == b.canon():
                results.append((a, 'D26_and_idempotent'))

        # ── 2. or(a, b) → case(a, True, b) ──
        if term.name == 'or' and len(term.args) == 2:
            a, b = term.args
            results.append((
                OCase(a, OLit(True), b),
                'D26_or_to_case',
            ))
            # Absorption: or(_, True) → True
            if _is_lit_bool(b, True):
                results.append((OLit(True), 'D26_absorb_or_true_r'))
            if _is_lit_bool(a, True):
                results.append((OLit(True), 'D26_absorb_or_true_l'))
            # Identity: or(_, False) → other
            if _is_lit_bool(b, False):
                results.append((a, 'D26_or_false_r'))
            if _is_lit_bool(a, False):
                results.append((b, 'D26_or_false_l'))
            # Idempotence
            if a.canon() == b.canon():
                results.append((a, 'D26_or_idempotent'))

        # ── 3. De Morgan: not(and(a, b)) → or(not a, not b) ──
        if term.name == 'u_not' and len(term.args) == 1:
            inner = term.args[0]
            if isinstance(inner, OOp) and inner.name == 'and' and len(inner.args) == 2:
                ia, ib = inner.args
                results.append((
                    OOp('or', (OOp('u_not', (ia,)), OOp('u_not', (ib,)))),
                    'D26_demorgan_and',
                ))

            # ── 4. De Morgan: not(or(a, b)) → and(not a, not b) ──
            if isinstance(inner, OOp) and inner.name == 'or' and len(inner.args) == 2:
                ia, ib = inner.args
                results.append((
                    OOp('and', (OOp('u_not', (ia,)), OOp('u_not', (ib,)))),
                    'D26_demorgan_or',
                ))

            # ── 6. Double negation: not(not(a)) → a ──
            if isinstance(inner, OOp) and inner.name == 'u_not' and len(inner.args) == 1:
                results.append((inner.args[0], 'D26_double_neg'))

        # ── 9. Chain flattening: and(a, and(b, c)) → flattened ──
        if term.name in ('and', 'or') and len(term.args) == 2:
            flat = _flatten_bool_chain(term, term.name)
            if len(flat) > 2:
                results.append((
                    OOp(term.name, tuple(flat)),
                    f'D26_flatten_{term.name}',
                ))

    # ── 7. Guard-to-bool: case(x, True, False) → bool(x) ──
    if isinstance(term, OCase):
        if _is_lit_bool(term.true_branch, True) and _is_lit_bool(term.false_branch, False):
            results.append((
                OOp('bool', (term.test,)),
                'D26_guard_to_bool',
            ))
        # case(x, False, True) → not(x)
        if _is_lit_bool(term.true_branch, False) and _is_lit_bool(term.false_branch, True):
            results.append((
                OOp('u_not', (term.test,)),
                'D26_guard_to_not',
            ))

    # ── 8. Bool-to-guard: bool(x) → case(x, True, False) ──
    if isinstance(term, OOp) and term.name == 'bool' and len(term.args) == 1:
        results.append((
            OCase(term.args[0], OLit(True), OLit(False)),
            'D26_bool_to_guard',
        ))

    # ── case from and/or back: case(a, b, False) → and(a, b) ──
    if isinstance(term, OCase):
        if _is_lit_bool(term.false_branch, False):
            results.append((
                OOp('and', (term.test, term.true_branch)),
                'D26_case_to_and',
            ))
        if _is_lit_bool(term.true_branch, True):
            results.append((
                OOp('or', (term.test, term.false_branch)),
                'D26_case_to_or',
            ))

    return results


def recognizes(term: OTerm) -> bool:
    """Quick check: could D26 apply to this term?"""
    if isinstance(term, OOp):
        if term.name in ('and', 'or') and len(term.args) == 2:
            return True
        if term.name == 'u_not' and len(term.args) == 1:
            return True
        if term.name == 'bool' and len(term.args) == 1:
            return True
    if isinstance(term, OCase):
        if _is_lit_bool(term.true_branch, True) or _is_lit_bool(term.false_branch, False):
            return True
        if _is_lit_bool(term.true_branch, False) and _is_lit_bool(term.false_branch, True):
            return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D26's relevance for bridging source → target."""
    sc = source.canon()
    tc = target.canon()
    s_bool = any(kw in sc for kw in ('and(', 'or(', 'u_not(', 'bool('))
    t_bool = any(kw in tc for kw in ('and(', 'or(', 'u_not(', 'bool('))
    s_case = 'case(' in sc
    t_case = 'case(' in tc

    if s_bool and t_case:
        return 0.85
    if s_case and t_bool:
        return 0.85
    if s_bool and t_bool:
        return 0.6
    if s_bool or t_bool:
        return 0.3
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse of D26: case→and/or, demorgan reverse, etc."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # case(a, b, False) → and(a, b)
    if isinstance(term, OCase):
        if _is_lit_bool(term.false_branch, False):
            results.append((
                OOp('and', (term.test, term.true_branch)),
                'D26_inv_case_to_and',
            ))
        if _is_lit_bool(term.true_branch, True):
            results.append((
                OOp('or', (term.test, term.false_branch)),
                'D26_inv_case_to_or',
            ))

    # or(not a, not b) → not(and(a, b))
    if isinstance(term, OOp) and term.name == 'or' and len(term.args) == 2:
        a, b = term.args
        if (isinstance(a, OOp) and a.name == 'u_not' and len(a.args) == 1 and
                isinstance(b, OOp) and b.name == 'u_not' and len(b.args) == 1):
            results.append((
                OOp('u_not', (OOp('and', (a.args[0], b.args[0])),)),
                'D26_inv_demorgan_or',
            ))

    # and(not a, not b) → not(or(a, b))
    if isinstance(term, OOp) and term.name == 'and' and len(term.args) == 2:
        a, b = term.args
        if (isinstance(a, OOp) and a.name == 'u_not' and len(a.args) == 1 and
                isinstance(b, OOp) and b.name == 'u_not' and len(b.args) == 1):
            results.append((
                OOp('u_not', (OOp('or', (a.args[0], b.args[0])),)),
                'D26_inv_demorgan_and',
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
    a, b, c = OVar('a'), OVar('b'), OVar('c')
    x = OVar('x')

    # 1. and(a, b) → case(a, b, False)
    t1 = OOp('and', (a, b))
    r1 = apply(t1, ctx)
    _assert(any(lbl == 'D26_and_to_case' for _, lbl in r1), "and → case")
    case_r = [t for t, lbl in r1 if lbl == 'D26_and_to_case'][0]
    _assert(isinstance(case_r, OCase), "result is OCase")

    # 2. or(a, b) → case(a, True, b)
    t2 = OOp('or', (a, b))
    r2 = apply(t2, ctx)
    _assert(any(lbl == 'D26_or_to_case' for _, lbl in r2), "or → case")

    # 3. De Morgan and: not(and(a, b)) → or(not a, not b)
    t3 = OOp('u_not', (OOp('and', (a, b)),))
    r3 = apply(t3, ctx)
    _assert(any(lbl == 'D26_demorgan_and' for _, lbl in r3), "De Morgan and")
    dm = [t for t, lbl in r3 if lbl == 'D26_demorgan_and'][0]
    _assert(isinstance(dm, OOp) and dm.name == 'or', "De Morgan result is or")

    # 4. De Morgan or: not(or(a, b)) → and(not a, not b)
    t4 = OOp('u_not', (OOp('or', (a, b)),))
    r4 = apply(t4, ctx)
    _assert(any(lbl == 'D26_demorgan_or' for _, lbl in r4), "De Morgan or")

    # 5. Absorption: and(a, False) → False
    t5 = OOp('and', (a, OLit(False)))
    r5 = apply(t5, ctx)
    _assert(any(lbl == 'D26_absorb_and_false_r' for _, lbl in r5), "and(a, False) → False")

    # 6. Absorption: or(a, True) → True
    t6 = OOp('or', (a, OLit(True)))
    r6 = apply(t6, ctx)
    _assert(any(lbl == 'D26_absorb_or_true_r' for _, lbl in r6), "or(a, True) → True")

    # 7. Double negation: not(not(a)) → a
    t7 = OOp('u_not', (OOp('u_not', (a,)),))
    r7 = apply(t7, ctx)
    _assert(any(lbl == 'D26_double_neg' for _, lbl in r7), "double negation")
    dn = [t for t, lbl in r7 if lbl == 'D26_double_neg'][0]
    _assert(dn.canon() == a.canon(), "double neg result is a")

    # 8. Guard-to-bool: case(x, True, False) → bool(x)
    t8 = OCase(x, OLit(True), OLit(False))
    r8 = apply(t8, ctx)
    _assert(any(lbl == 'D26_guard_to_bool' for _, lbl in r8), "guard → bool")

    # 9. Guard-to-not: case(x, False, True) → not(x)
    t9 = OCase(x, OLit(False), OLit(True))
    r9 = apply(t9, ctx)
    _assert(any(lbl == 'D26_guard_to_not' for _, lbl in r9), "guard → not")

    # 10. Bool-to-guard: bool(x) → case(x, True, False)
    t10 = OOp('bool', (x,))
    r10 = apply(t10, ctx)
    _assert(any(lbl == 'D26_bool_to_guard' for _, lbl in r10), "bool → guard")

    # 11. Chain flattening: and(a, and(b, c)) → and(a, b, c)
    t11 = OOp('and', (a, OOp('and', (b, c))))
    r11 = apply(t11, ctx)
    _assert(any(lbl == 'D26_flatten_and' for _, lbl in r11), "flatten and")

    # 12. Identity: and(a, True) → a
    t12 = OOp('and', (a, OLit(True)))
    r12 = apply(t12, ctx)
    _assert(any(lbl == 'D26_and_true_r' for _, lbl in r12), "and(a, True) → a")

    # 13. Idempotence: and(a, a) → a
    t13 = OOp('and', (a, a))
    r13 = apply(t13, ctx)
    _assert(any(lbl == 'D26_and_idempotent' for _, lbl in r13), "and(a,a) → a")

    # 14. case(a, b, False) → and(a, b) (case back to and)
    t14 = OCase(a, b, OLit(False))
    r14 = apply(t14, ctx)
    _assert(any(lbl == 'D26_case_to_and' for _, lbl in r14), "case → and")

    # 15. Recognizes
    _assert(recognizes(t1), "recognizes and")
    _assert(recognizes(t2), "recognizes or")
    _assert(recognizes(t3), "recognizes not")
    _assert(recognizes(t8), "recognizes guard-bool case")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # 16. Relevance
    _assert(relevance_score(t1, t8) > 0.5, "bool↔case relevance high")

    # 17. Inverse: case(a, b, False) → and(a, b)
    r17 = apply_inverse(t14, ctx)
    _assert(any(lbl == 'D26_inv_case_to_and' for _, lbl in r17), "inv case → and")

    # 18. Inverse De Morgan: or(not a, not b) → not(and(a, b))
    t18 = OOp('or', (OOp('u_not', (a,)), OOp('u_not', (b,))))
    r18 = apply_inverse(t18, ctx)
    _assert(any(lbl == 'D26_inv_demorgan_or' for _, lbl in r18), "inv De Morgan or")

    print(f"D26 short-circuit: {_pass} passed, {_fail} failed")
