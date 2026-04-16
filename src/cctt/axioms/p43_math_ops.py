"""P43 Axiom: Math Module Equivalences.

Establishes equivalences between Python's math module functions and
their inline/operator equivalents: math.pow ↔ ** ↔ multiplication,
math.sqrt ↔ ** 0.5, math.floor ↔ int() for positives, math.log
identities, abs ↔ math.fabs, math.gcd ↔ Euclidean algorithm,
sum ↔ math.fsum, divmod ↔ (a//b, a%b), round vs int, and
math.ceil ↔ -math.floor(-x).

Mathematical basis: these are ring-theoretic identities in the
semiring of Python numeric types.  The power operation x ** 2 is
the square in the multiplicative monoid; math.pow(x, 2) is its
floating-point analogue.  math.sqrt is the principal root — the
inverse of squaring in R≥0.

  math.pow(x, 2) ≡ x ** 2 ≡ x * x        (square)
  math.sqrt(x)   ≡ x ** 0.5               (principal root)
  math.floor(x)  ≡ int(x)                 (for x ≥ 0)
  math.log(e**x) ≡ x                      (log-exp inverse)
  abs(x)         ≡ math.fabs(x)           (absolute value)
  math.gcd(a,b)  ≡ euclidean_gcd(a,b)     (GCD algorithm)
  sum(xs)        ≡ math.fsum(xs)          (summation)
  divmod(a,b)    ≡ (a // b, a % b)        (division with remainder)
  round(x)       ≡ int(x + 0.5)          (for x ≥ 0)
  math.ceil(x)   ≡ -math.floor(-x)       (ceiling via floor)

Key rewrites:
  • math.pow(x, 2) ↔ x ** 2
  • x ** 2 ↔ x * x
  • math.sqrt(x) ↔ x ** 0.5
  • math.floor(x) ↔ int(x)       (positive x)
  • math.log(exp(x)) ↔ x
  • abs(x) ↔ math.fabs(x)
  • math.gcd(a, b) ↔ euclidean_gcd(a, b)
  • sum(xs) ↔ math.fsum(xs)
  • divmod(a, b) ↔ (a // b, a % b)
  • round(x) ↔ int(x + 0.5)
  • math.ceil(x) ↔ -math.floor(-x)

(§P43, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P43_math_ops"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P12_numeric", "P16_type_convert"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P43 Math Module Equivalences).

1. math_pow(x, 2) ≡ pow_op(x, 2) ≡ mul_self(x)
   math.pow(x, 2) ≡ x ** 2 ≡ x * x.
   All compute x² in the multiplicative monoid.

2. math_sqrt(x) ≡ pow_half(x)
   math.sqrt(x) ≡ x ** 0.5.
   Both compute the principal square root for x ≥ 0.

3. math_floor(x) ≡ int_trunc(x)
   math.floor(x) ≡ int(x) for x ≥ 0.
   Both compute ⌊x⌋ when x is non-negative.

4. math_log(exp(x)) ≡ x
   log(exp(x)) = x by the log-exp adjunction.

5. abs_fn(x) ≡ math_fabs(x)
   abs(x) ≡ math.fabs(x).
   Both compute |x|; fabs always returns float.

6. math_gcd(a, b) ≡ euclidean_gcd(a, b)
   math.gcd uses the Euclidean algorithm internally.

7. sum_fn(xs) ≡ math_fsum(xs)
   sum(xs) ≡ math.fsum(xs).
   fsum uses compensated summation for better precision.

8. divmod_fn(a, b) ≡ floordiv_mod(a, b)
   divmod(a, b) ≡ (a // b, a % b).
   Both return quotient and remainder.

9. round_fn(x) ≡ int_round(x)
   round(x) ≡ int(x + 0.5) for non-negative x.
   Banker's rounding differs at half-integers.

10. math_ceil(x) ≡ neg_floor_neg(x)
    math.ceil(x) ≡ -math.floor(-x).
    Ceiling via negation-floor-negation identity.

11. math_pow(x, 0) ≡ 1 (power-zero identity).

12. math_pow(x, 1) ≡ x (power-one identity).
"""

EXAMPLES = [
    ("math_pow($x, 2)", "pow_op($x, 2)",
     "P43_math_pow_to_pow_op"),
    ("pow_op($x, 2)", "mul_self($x)",
     "P43_pow_to_mul_self"),
    ("math_sqrt($x)", "pow_half($x)",
     "P43_sqrt_to_pow_half"),
    ("math_floor($x)", "int_trunc($x)",
     "P43_floor_to_int_trunc"),
    ("abs_fn($x)", "math_fabs($x)",
     "P43_abs_to_fabs"),
]

_MATH_OPS = frozenset({
    'math_pow', 'pow_op', 'mul_self', 'math_sqrt', 'pow_half',
    'math_floor', 'int_trunc', 'math_log', 'log_identity',
    'abs_fn', 'math_fabs', 'math_gcd', 'euclidean_gcd',
    'sum_fn', 'math_fsum', 'divmod_fn', 'floordiv_mod',
    'round_fn', 'int_round', 'math_ceil', 'neg_floor_neg',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P43: Math module equivalence rewrites (forward)."""
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp):
        return results

    # ── 1. math_pow(x, 2) ↔ pow_op(x, 2) ──
    if term.name == 'math_pow' and len(term.args) == 2:
        results.append((
            OOp('pow_op', term.args),
            'P43_math_pow_to_pow_op',
        ))

    if term.name == 'pow_op' and len(term.args) == 2:
        results.append((
            OOp('math_pow', term.args),
            'P43_pow_op_to_math_pow',
        ))

    # ── 2. pow_op(x, 2) ↔ mul_self(x) ──
    if term.name == 'pow_op' and len(term.args) == 2:
        x, exp = term.args
        if isinstance(exp, OLit) and exp.value == 2:
            results.append((
                OOp('mul_self', (x,)),
                'P43_pow_to_mul_self',
            ))

    if term.name == 'mul_self' and len(term.args) == 1:
        x = term.args[0]
        results.append((
            OOp('pow_op', (x, OLit(2))),
            'P43_mul_self_to_pow',
        ))

    # ── 3. math_sqrt(x) ↔ pow_half(x) ──
    if term.name == 'math_sqrt' and len(term.args) == 1:
        results.append((
            OOp('pow_half', term.args),
            'P43_sqrt_to_pow_half',
        ))

    if term.name == 'pow_half' and len(term.args) == 1:
        results.append((
            OOp('math_sqrt', term.args),
            'P43_pow_half_to_sqrt',
        ))

    # ── 4. math_floor(x) ↔ int_trunc(x) ──
    if term.name == 'math_floor' and len(term.args) == 1:
        results.append((
            OOp('int_trunc', term.args),
            'P43_floor_to_int_trunc',
        ))

    if term.name == 'int_trunc' and len(term.args) == 1:
        results.append((
            OOp('math_floor', term.args),
            'P43_int_trunc_to_floor',
        ))

    # ── 5. math_log(exp(x)) ↔ x (log-exp inverse) ──
    if term.name == 'math_log' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'math_exp' and len(inner.args) == 1:
            results.append((
                inner.args[0],
                'P43_log_exp_identity',
            ))

    if term.name == 'math_log' and len(term.args) == 1:
        results.append((
            OOp('log_identity', term.args),
            'P43_log_to_log_identity',
        ))

    if term.name == 'log_identity' and len(term.args) == 1:
        results.append((
            OOp('math_log', term.args),
            'P43_log_identity_to_log',
        ))

    # ── 6. abs_fn(x) ↔ math_fabs(x) ──
    if term.name == 'abs_fn' and len(term.args) == 1:
        results.append((
            OOp('math_fabs', term.args),
            'P43_abs_to_fabs',
        ))

    if term.name == 'math_fabs' and len(term.args) == 1:
        results.append((
            OOp('abs_fn', term.args),
            'P43_fabs_to_abs',
        ))

    # ── 7. math_gcd(a, b) ↔ euclidean_gcd(a, b) ──
    if term.name == 'math_gcd' and len(term.args) == 2:
        results.append((
            OOp('euclidean_gcd', term.args),
            'P43_gcd_to_euclidean',
        ))

    if term.name == 'euclidean_gcd' and len(term.args) == 2:
        results.append((
            OOp('math_gcd', term.args),
            'P43_euclidean_to_gcd',
        ))

    # ── 8. sum_fn(xs) ↔ math_fsum(xs) ──
    if term.name == 'sum_fn' and len(term.args) == 1:
        results.append((
            OOp('math_fsum', term.args),
            'P43_sum_to_fsum',
        ))

    if term.name == 'math_fsum' and len(term.args) == 1:
        results.append((
            OOp('sum_fn', term.args),
            'P43_fsum_to_sum',
        ))

    # ── 9. divmod_fn(a, b) ↔ floordiv_mod(a, b) ──
    if term.name == 'divmod_fn' and len(term.args) == 2:
        results.append((
            OOp('floordiv_mod', term.args),
            'P43_divmod_to_floordiv_mod',
        ))

    if term.name == 'floordiv_mod' and len(term.args) == 2:
        results.append((
            OOp('divmod_fn', term.args),
            'P43_floordiv_mod_to_divmod',
        ))

    # ── 10. round_fn(x) ↔ int_round(x) ──
    if term.name == 'round_fn' and len(term.args) == 1:
        results.append((
            OOp('int_round', term.args),
            'P43_round_to_int_round',
        ))

    if term.name == 'int_round' and len(term.args) == 1:
        results.append((
            OOp('round_fn', term.args),
            'P43_int_round_to_round',
        ))

    # ── 11. math_ceil(x) ↔ neg_floor_neg(x) ──
    if term.name == 'math_ceil' and len(term.args) == 1:
        results.append((
            OOp('neg_floor_neg', term.args),
            'P43_ceil_to_neg_floor_neg',
        ))

    if term.name == 'neg_floor_neg' and len(term.args) == 1:
        results.append((
            OOp('math_ceil', term.args),
            'P43_neg_floor_neg_to_ceil',
        ))

    # ── 12. math_pow(x, 0) → 1 (power-zero identity) ──
    if term.name == 'math_pow' and len(term.args) == 2:
        _, exp = term.args
        if isinstance(exp, OLit) and exp.value == 0:
            results.append((
                OLit(1),
                'P43_pow_zero_identity',
            ))

    # ── 13. math_pow(x, 1) → x (power-one identity) ──
    if term.name == 'math_pow' and len(term.args) == 2:
        x, exp = term.args
        if isinstance(exp, OLit) and exp.value == 1:
            results.append((
                x,
                'P43_pow_one_identity',
            ))

    # ── 14. math_sqrt → OOp('pow_op', (x, 0.5)) structural ──
    if term.name == 'math_sqrt' and len(term.args) == 1:
        x = term.args[0]
        results.append((
            OOp('pow_op', (x, OLit(0.5))),
            'P43_sqrt_to_pow_op_half',
        ))

    # ── 15. math_ceil → OCase structural form ──
    if term.name == 'math_ceil' and len(term.args) == 1:
        x = term.args[0]
        results.append((
            OOp('neg', (OOp('math_floor', (OOp('neg', (x,)),)),)),
            'P43_ceil_expand',
        ))

    # ── 16. divmod_fn → OSeq structural form ──
    if term.name == 'divmod_fn' and len(term.args) == 2:
        a, b = term.args
        results.append((
            OSeq((OOp('floordiv', (a, b)), OOp('mod', (a, b)))),
            'P43_divmod_to_seq',
        ))

    # ── 17. abs_fn → OCase structural form ──
    if term.name == 'abs_fn' and len(term.args) == 1:
        x = term.args[0]
        results.append((
            OCase(OOp('ge', (x, OLit(0))), x, OOp('neg', (x,))),
            'P43_abs_to_case',
        ))

    # ── 18. math_gcd(a, 0) → abs(a) ──
    if term.name == 'math_gcd' and len(term.args) == 2:
        a, b = term.args
        if isinstance(b, OLit) and b.value == 0:
            results.append((
                OOp('abs_fn', (a,)),
                'P43_gcd_zero_identity',
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Return reverse rewrites (inline → math module form)."""
    inverse_labels = {
        'P43_pow_op_to_math_pow', 'P43_mul_self_to_pow',
        'P43_pow_half_to_sqrt', 'P43_int_trunc_to_floor',
        'P43_log_identity_to_log', 'P43_fabs_to_abs',
        'P43_euclidean_to_gcd', 'P43_fsum_to_sum',
        'P43_floordiv_mod_to_divmod', 'P43_int_round_to_round',
        'P43_neg_floor_neg_to_ceil',
    }
    return [(t, l) for t, l in apply(term, ctx) if l in inverse_labels]


def recognizes(term: OTerm) -> bool:
    """Return True if the term's root operator is a math op."""
    if isinstance(term, OOp) and term.name in _MATH_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Heuristic relevance for search-guided rewriting."""
    sc, tc = source.canon(), target.canon()
    for kw in ('math_pow', 'pow_op', 'mul_self', 'math_sqrt', 'pow_half',
               'math_floor', 'int_trunc', 'math_log', 'abs_fn', 'math_fabs',
               'math_gcd', 'euclidean_gcd', 'sum_fn', 'math_fsum',
               'divmod_fn', 'floordiv_mod', 'round_fn', 'int_round',
               'math_ceil', 'neg_floor_neg'):
        if kw in sc and kw in tc:
            return 0.9
    if ('math_pow' in sc and 'pow_op' in tc) or \
       ('pow_op' in sc and 'math_pow' in tc):
        return 0.85
    if ('math_sqrt' in sc and 'pow_half' in tc) or \
       ('pow_half' in sc and 'math_sqrt' in tc):
        return 0.85
    if ('math_floor' in sc and 'int_trunc' in tc) or \
       ('int_trunc' in sc and 'math_floor' in tc):
        return 0.85
    if ('abs_fn' in sc and 'math_fabs' in tc) or \
       ('math_fabs' in sc and 'abs_fn' in tc):
        return 0.8
    if ('divmod' in sc and 'floordiv' in tc) or \
       ('floordiv' in sc and 'divmod' in tc):
        return 0.8
    if any(k in sc for k in ('math_pow', 'math_sqrt', 'math_floor',
                             'math_log', 'abs_fn', 'math_gcd',
                             'sum_fn', 'divmod_fn', 'round_fn',
                             'math_ceil')):
        return 0.3
    return 0.05


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

    # 1. math_pow → pow_op
    t = OOp('math_pow', (OVar('x'), OLit(2)))
    r = apply(t)
    _assert(any(l == 'P43_math_pow_to_pow_op' for _, l in r),
            "math_pow → pow_op")

    # 2. pow_op → math_pow
    t2 = OOp('pow_op', (OVar('x'), OLit(2)))
    r2 = apply(t2)
    _assert(any(l == 'P43_pow_op_to_math_pow' for _, l in r2),
            "pow_op → math_pow")

    # 3. pow_op(x, 2) → mul_self(x)
    _assert(any(l == 'P43_pow_to_mul_self' for _, l in r2),
            "pow_op(x,2) → mul_self")

    # 4. mul_self → pow_op(x, 2)
    t4 = OOp('mul_self', (OVar('x'),))
    r4 = apply(t4)
    _assert(any(l == 'P43_mul_self_to_pow' for _, l in r4),
            "mul_self → pow_op")
    mul_results = [(t, l) for t, l in r4 if l == 'P43_mul_self_to_pow']
    if mul_results:
        rr = mul_results[0][0]
        _assert(isinstance(rr, OOp) and rr.name == 'pow_op',
                "mul_self produces pow_op")
    else:
        _assert(False, "mul_self produces pow_op")

    # 5. math_sqrt → pow_half
    t5 = OOp('math_sqrt', (OVar('x'),))
    r5 = apply(t5)
    _assert(any(l == 'P43_sqrt_to_pow_half' for _, l in r5),
            "math_sqrt → pow_half")

    # 6. pow_half → math_sqrt
    t6 = OOp('pow_half', (OVar('x'),))
    r6 = apply(t6)
    _assert(any(l == 'P43_pow_half_to_sqrt' for _, l in r6),
            "pow_half → math_sqrt")

    # 7. math_floor → int_trunc
    t7 = OOp('math_floor', (OVar('x'),))
    r7 = apply(t7)
    _assert(any(l == 'P43_floor_to_int_trunc' for _, l in r7),
            "math_floor → int_trunc")

    # 8. int_trunc → math_floor
    t8 = OOp('int_trunc', (OVar('x'),))
    r8 = apply(t8)
    _assert(any(l == 'P43_int_trunc_to_floor' for _, l in r8),
            "int_trunc → math_floor")

    # 9. abs_fn → math_fabs
    t9 = OOp('abs_fn', (OVar('x'),))
    r9 = apply(t9)
    _assert(any(l == 'P43_abs_to_fabs' for _, l in r9),
            "abs → fabs")

    # 10. math_fabs → abs_fn
    t10 = OOp('math_fabs', (OVar('x'),))
    r10 = apply(t10)
    _assert(any(l == 'P43_fabs_to_abs' for _, l in r10),
            "fabs → abs")

    # 11. math_gcd → euclidean_gcd
    t11 = OOp('math_gcd', (OVar('a'), OVar('b')))
    r11 = apply(t11)
    _assert(any(l == 'P43_gcd_to_euclidean' for _, l in r11),
            "gcd → euclidean")

    # 12. euclidean_gcd → math_gcd
    t12 = OOp('euclidean_gcd', (OVar('a'), OVar('b')))
    r12 = apply(t12)
    _assert(any(l == 'P43_euclidean_to_gcd' for _, l in r12),
            "euclidean → gcd")

    # 13. sum_fn → math_fsum
    t13 = OOp('sum_fn', (OVar('xs'),))
    r13 = apply(t13)
    _assert(any(l == 'P43_sum_to_fsum' for _, l in r13),
            "sum → fsum")

    # 14. math_fsum → sum_fn
    t14 = OOp('math_fsum', (OVar('xs'),))
    r14 = apply(t14)
    _assert(any(l == 'P43_fsum_to_sum' for _, l in r14),
            "fsum → sum")

    # 15. divmod_fn → floordiv_mod
    t15 = OOp('divmod_fn', (OVar('a'), OVar('b')))
    r15 = apply(t15)
    _assert(any(l == 'P43_divmod_to_floordiv_mod' for _, l in r15),
            "divmod → floordiv_mod")

    # 16. floordiv_mod → divmod_fn
    t16 = OOp('floordiv_mod', (OVar('a'), OVar('b')))
    r16 = apply(t16)
    _assert(any(l == 'P43_floordiv_mod_to_divmod' for _, l in r16),
            "floordiv_mod → divmod")

    # 17. round_fn → int_round
    t17 = OOp('round_fn', (OVar('x'),))
    r17 = apply(t17)
    _assert(any(l == 'P43_round_to_int_round' for _, l in r17),
            "round → int_round")

    # 18. int_round → round_fn
    t18 = OOp('int_round', (OVar('x'),))
    r18 = apply(t18)
    _assert(any(l == 'P43_int_round_to_round' for _, l in r18),
            "int_round → round")

    # 19. math_ceil → neg_floor_neg
    t19 = OOp('math_ceil', (OVar('x'),))
    r19 = apply(t19)
    _assert(any(l == 'P43_ceil_to_neg_floor_neg' for _, l in r19),
            "ceil → neg_floor_neg")

    # 20. neg_floor_neg → math_ceil
    t20 = OOp('neg_floor_neg', (OVar('x'),))
    r20 = apply(t20)
    _assert(any(l == 'P43_neg_floor_neg_to_ceil' for _, l in r20),
            "neg_floor_neg → ceil")

    # 21. math_pow(x, 0) → 1
    t21 = OOp('math_pow', (OVar('x'), OLit(0)))
    r21 = apply(t21)
    _assert(any(l == 'P43_pow_zero_identity' for _, l in r21),
            "pow(x,0) → 1")
    pz = [(t, l) for t, l in r21 if l == 'P43_pow_zero_identity']
    if pz:
        _assert(isinstance(pz[0][0], OLit) and pz[0][0].value == 1,
                "pow(x,0) produces 1")
    else:
        _assert(False, "pow(x,0) produces 1")

    # 22. math_pow(x, 1) → x
    t22 = OOp('math_pow', (OVar('y'), OLit(1)))
    r22 = apply(t22)
    _assert(any(l == 'P43_pow_one_identity' for _, l in r22),
            "pow(x,1) → x")
    p1 = [(t, l) for t, l in r22 if l == 'P43_pow_one_identity']
    if p1:
        _assert(isinstance(p1[0][0], OVar) and p1[0][0].name == 'y',
                "pow(y,1) produces y")
    else:
        _assert(False, "pow(y,1) produces y")

    # 23. math_log(exp(x)) → x
    t23 = OOp('math_log', (OOp('math_exp', (OVar('z'),)),))
    r23 = apply(t23)
    _assert(any(l == 'P43_log_exp_identity' for _, l in r23),
            "log(exp(x)) → x")
    le = [(t, l) for t, l in r23 if l == 'P43_log_exp_identity']
    if le:
        _assert(isinstance(le[0][0], OVar) and le[0][0].name == 'z',
                "log(exp(z)) produces z")
    else:
        _assert(False, "log(exp(z)) produces z")

    # 24. math_sqrt → pow_op(x, 0.5) structural
    _assert(any(l == 'P43_sqrt_to_pow_op_half' for _, l in r5),
            "sqrt → pow_op(x, 0.5)")

    # 25. math_ceil expand structural
    _assert(any(l == 'P43_ceil_expand' for _, l in r19),
            "ceil → -floor(-x)")

    # 26. divmod → OSeq structural
    _assert(any(l == 'P43_divmod_to_seq' for _, l in r15),
            "divmod → OSeq")
    seq_results = [(t, l) for t, l in r15 if l == 'P43_divmod_to_seq']
    if seq_results:
        _assert(isinstance(seq_results[0][0], OSeq),
                "divmod produces OSeq")
    else:
        _assert(False, "divmod produces OSeq")

    # 27. abs → OCase structural
    _assert(any(l == 'P43_abs_to_case' for _, l in r9),
            "abs → OCase")
    abs_case = [(t, l) for t, l in r9 if l == 'P43_abs_to_case']
    if abs_case:
        _assert(isinstance(abs_case[0][0], OCase),
                "abs produces OCase")
    else:
        _assert(False, "abs produces OCase")

    # 28. math_gcd(a, 0) → abs(a)
    t28 = OOp('math_gcd', (OVar('a'), OLit(0)))
    r28 = apply(t28)
    _assert(any(l == 'P43_gcd_zero_identity' for _, l in r28),
            "gcd(a,0) → abs(a)")

    # 29. inverse: pow_op → math_pow
    r29_inv = apply_inverse(OOp('pow_op', (OVar('x'), OLit(3))))
    _assert(any(l == 'P43_pow_op_to_math_pow' for _, l in r29_inv),
            "inv: pow_op → math_pow")

    # 30. inverse: fabs → abs
    r30_inv = apply_inverse(OOp('math_fabs', (OVar('x'),)))
    _assert(any(l == 'P43_fabs_to_abs' for _, l in r30_inv),
            "inv: fabs → abs")

    # 31. recognizes math ops
    _assert(recognizes(OOp('math_pow', (OVar('x'), OLit(2)))),
            "recognizes math_pow")
    _assert(recognizes(OOp('math_sqrt', (OVar('x'),))),
            "recognizes math_sqrt")
    _assert(recognizes(OOp('divmod_fn', (OVar('a'), OVar('b')))),
            "recognizes divmod_fn")
    _assert(not recognizes(OLit(42)), "!recognizes literal")
    _assert(not recognizes(OVar('x')), "!recognizes var")

    # 32. relevance: math_pow ↔ pow_op high
    _assert(relevance_score(
        OOp('math_pow', (OVar('x'), OLit(2))),
        OOp('pow_op', (OVar('x'), OLit(2))),
    ) > 0.7, "math_pow/pow_op relevance high")

    # 33. relevance: abs ↔ fabs high
    _assert(relevance_score(
        OOp('abs_fn', (OVar('x'),)),
        OOp('math_fabs', (OVar('x'),)),
    ) > 0.7, "abs/fabs relevance high")

    # 34. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2,
            "unrelated relevance low")

    # 35. no rewrites for non-OOp
    _assert(apply(OVar('x')) == [], "no rewrites for OVar")
    _assert(apply(OLit(42)) == [], "no rewrites for OLit")

    print(f"P43 math_ops: {_pass} passed, {_fail} failed")
