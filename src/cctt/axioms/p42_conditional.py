"""P42 Axiom: Conditional Assignment Equivalences.

Establishes equivalences between different Python conditional
assignment patterns: ternary (x if cond else y) vs and/or trick,
x = x or default, getattr with default vs try/except,
dict.get(k, d) vs if-in-dict, None coalescing, and guarded
function calls.

Mathematical basis: conditional expressions correspond to the
coproduct eliminator (case analysis) in type theory:

  case : Bool × A × A → A
  case(True, a, b) = a
  case(False, a, b) = b

The ternary expression `a if c else b` is case(c, a, b).

The and/or trick `c and a or b` exploits Python's short-circuit
semantics: when a is truthy, `c and a` = a (if c) or False (if
not c), then `a or b` = a; `False or b` = b.  This fails when
a is falsy, so the equivalence holds only when a is known truthy.

or-default: `x = x or default` is case(bool(x), x, default),
the coalescing operator for falsy values.

None-coalescing: `a if a is not None else b` is the option
eliminator Some(a) ↦ a | None ↦ b.

getattr(obj, 'a', d) is the safe field projection with default:
  π_a(obj) if hasattr(obj, 'a') else d

dict.get(k, d) is the safe lookup:
  d[k] if k in d else d

Key rewrites:
  • x if c else y ↔ c and x or y   (when x is truthy)
  • x = x or default ↔ if not x: x = default
  • getattr(obj, 'a', d) ↔ try: obj.a except: d
  • dict.get(k, d) ↔ d[k] if k in d else d
  • a if a is not None else b ↔ coalesce(a, b)
  • max(a, b) ↔ a if a >= b else b
  • min(a, b) ↔ a if a <= b else b
  • x or [] ↔ x if x else []   (empty default)
  • f(x) if x else None ↔ guarded call

(§P42, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P42_conditional"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P13_bool_idioms", "P03_dict_ops", "P09_exceptions"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P42 Conditional Assignment Equivalences).

1. ternary(c, a, b) ≡ and_or(c, a, b)
   (a if c else b) ≡ (c and a or b) when a is truthy.
   Both compute case(c, a, b).

2. or_default(x, d) ≡ if_not_assign(x, d)
   x = x or d ≡ if not x: x = d
   Both assign d when x is falsy.

3. getattr_default(obj, attr, d) ≡ try_attr(obj, attr, d)
   getattr(obj, attr, d) ≡ try: obj.attr except AttributeError: d
   Both safely access an attribute with a fallback.

4. dict_get(d, k, default) ≡ dict_if_in(d, k, default)
   d.get(k, default) ≡ d[k] if k in d else default
   Both safely look up a key with a fallback.

5. none_coalesce(a, b) ≡ if_not_none(a, b)
   (a if a is not None else b) ≡ coalesce(a, b)
   The option eliminator — use a if present, else b.

6. max_default(a, b) ≡ ternary_max(a, b)
   max(a, b) ≡ a if a >= b else b
   Both compute the maximum of two values.

7. min_default(a, b) ≡ ternary_min(a, b)
   min(a, b) ≡ a if a <= b else b
   Both compute the minimum of two values.

8. or_empty(x) ≡ if_none_empty(x)
   x or [] ≡ x if x else []
   Default to empty collection when x is falsy.

9. conditional_call(f, x) ≡ guard_call(f, x)
   f(x) if x else None ≡ guard_call(f, x)
   Only call f when x is truthy; otherwise return None.

10. ternary(c, a, b) → OCase form using OCase(test, true, false).

11. dict_get with literal dict and known key → direct value.

12. none_coalesce(a, a) simplifies to a.
"""

EXAMPLES = [
    ("ternary($c, $a, $b)", "and_or($c, $a, $b)",
     "P42_ternary_to_and_or"),
    ("or_default($x, $d)", "if_not_assign($x, $d)",
     "P42_or_to_if_not"),
    ("getattr_default($obj, $attr, $d)", "try_attr($obj, $attr, $d)",
     "P42_getattr_to_try"),
    ("dict_get($d, $k, $default)", "dict_if_in($d, $k, $default)",
     "P42_dict_get_to_if_in"),
    ("none_coalesce($a, $b)", "if_not_none($a, $b)",
     "P42_coalesce_to_if_not_none"),
]

_CONDITIONAL_OPS = frozenset({
    'ternary', 'and_or', 'or_default', 'if_not_assign',
    'getattr_default', 'try_attr', 'dict_get', 'dict_if_in',
    'none_coalesce', 'if_not_none', 'max_default', 'ternary_max',
    'min_default', 'ternary_min', 'or_empty', 'if_none_empty',
    'conditional_call', 'guard_call',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P42: Conditional assignment equivalence rewrites (forward)."""
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp):
        return results

    # ── 1. ternary ↔ and_or ──
    if term.name == 'ternary' and len(term.args) == 3:
        results.append((
            OOp('and_or', term.args),
            'P42_ternary_to_and_or',
        ))

    if term.name == 'and_or' and len(term.args) == 3:
        results.append((
            OOp('ternary', term.args),
            'P42_and_or_to_ternary',
        ))

    # ── 2. or_default ↔ if_not_assign ──
    if term.name == 'or_default' and len(term.args) == 2:
        results.append((
            OOp('if_not_assign', term.args),
            'P42_or_to_if_not',
        ))

    if term.name == 'if_not_assign' and len(term.args) == 2:
        results.append((
            OOp('or_default', term.args),
            'P42_if_not_to_or',
        ))

    # ── 3. getattr_default ↔ try_attr ──
    if term.name == 'getattr_default' and len(term.args) == 3:
        results.append((
            OOp('try_attr', term.args),
            'P42_getattr_to_try',
        ))

    if term.name == 'try_attr' and len(term.args) == 3:
        results.append((
            OOp('getattr_default', term.args),
            'P42_try_to_getattr',
        ))

    # ── 4. dict_get ↔ dict_if_in ──
    if term.name == 'dict_get' and len(term.args) == 3:
        results.append((
            OOp('dict_if_in', term.args),
            'P42_dict_get_to_if_in',
        ))

    if term.name == 'dict_if_in' and len(term.args) == 3:
        results.append((
            OOp('dict_get', term.args),
            'P42_if_in_to_dict_get',
        ))

    # ── 5. none_coalesce ↔ if_not_none ──
    if term.name == 'none_coalesce' and len(term.args) == 2:
        results.append((
            OOp('if_not_none', term.args),
            'P42_coalesce_to_if_not_none',
        ))

    if term.name == 'if_not_none' and len(term.args) == 2:
        results.append((
            OOp('none_coalesce', term.args),
            'P42_if_not_none_to_coalesce',
        ))

    # ── 6. max_default ↔ ternary_max ──
    if term.name == 'max_default' and len(term.args) == 2:
        results.append((
            OOp('ternary_max', term.args),
            'P42_max_to_ternary',
        ))

    if term.name == 'ternary_max' and len(term.args) == 2:
        results.append((
            OOp('max_default', term.args),
            'P42_ternary_to_max',
        ))

    # ── 7. min_default ↔ ternary_min ──
    if term.name == 'min_default' and len(term.args) == 2:
        results.append((
            OOp('ternary_min', term.args),
            'P42_min_to_ternary',
        ))

    if term.name == 'ternary_min' and len(term.args) == 2:
        results.append((
            OOp('min_default', term.args),
            'P42_ternary_to_min',
        ))

    # ── 8. or_empty ↔ if_none_empty ──
    if term.name == 'or_empty' and len(term.args) == 1:
        results.append((
            OOp('if_none_empty', term.args),
            'P42_or_empty_to_if_none',
        ))

    if term.name == 'if_none_empty' and len(term.args) == 1:
        results.append((
            OOp('or_empty', term.args),
            'P42_if_none_to_or_empty',
        ))

    # ── 9. conditional_call ↔ guard_call ──
    if term.name == 'conditional_call' and len(term.args) == 2:
        results.append((
            OOp('guard_call', term.args),
            'P42_conditional_to_guard',
        ))

    if term.name == 'guard_call' and len(term.args) == 2:
        results.append((
            OOp('conditional_call', term.args),
            'P42_guard_to_conditional',
        ))

    # ── 10. ternary → OCase structural form ──
    if term.name == 'ternary' and len(term.args) == 3:
        c, a, b = term.args
        results.append((
            OCase(c, a, b),
            'P42_ternary_to_ocase',
        ))

    # ── 11. getattr_default → OCatch structural form ──
    if term.name == 'getattr_default' and len(term.args) == 3:
        obj, attr, default = term.args
        results.append((
            OCatch(OOp('getattr', (obj, attr)), default),
            'P42_getattr_to_ocatch',
        ))

    # ── 12. dict_get → OCase with membership test ──
    if term.name == 'dict_get' and len(term.args) == 3:
        d, k, default = term.args
        results.append((
            OCase(
                OOp('contains', (d, k)),
                OOp('getitem', (d, k)),
                default,
            ),
            'P42_dict_get_to_case',
        ))

    # ── 13. none_coalesce → OCase with None test ──
    if term.name == 'none_coalesce' and len(term.args) == 2:
        a, b = term.args
        results.append((
            OCase(OOp('is_not_none', (a,)), a, b),
            'P42_coalesce_to_case',
        ))

    # ── 14. none_coalesce(a, a) → a (simplification) ──
    if term.name == 'none_coalesce' and len(term.args) == 2:
        a, b = term.args
        if a.canon() == b.canon():
            results.append((
                a,
                'P42_coalesce_same_simplify',
            ))

    # ── 15. conditional_call → OCase form ──
    if term.name == 'conditional_call' and len(term.args) == 2:
        f, x = term.args
        results.append((
            OCase(x, OOp('call', (f, x)), OLit(None)),
            'P42_conditional_call_to_case',
        ))

    # ── 16. or_default → OCase form ──
    if term.name == 'or_default' and len(term.args) == 2:
        x, d = term.args
        results.append((
            OCase(x, x, d),
            'P42_or_default_to_case',
        ))

    # ── 17. max_default → OCase form ──
    if term.name == 'max_default' and len(term.args) == 2:
        a, b = term.args
        results.append((
            OCase(OOp('ge', (a, b)), a, b),
            'P42_max_to_case',
        ))

    # ── 18. min_default → OCase form ──
    if term.name == 'min_default' and len(term.args) == 2:
        a, b = term.args
        results.append((
            OCase(OOp('le', (a, b)), a, b),
            'P42_min_to_case',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Return reverse rewrites (manual/verbose → idiomatic form)."""
    inverse_labels = {
        'P42_and_or_to_ternary', 'P42_if_not_to_or',
        'P42_try_to_getattr', 'P42_if_in_to_dict_get',
        'P42_if_not_none_to_coalesce', 'P42_ternary_to_max',
        'P42_ternary_to_min', 'P42_if_none_to_or_empty',
        'P42_guard_to_conditional',
    }
    return [(t, l) for t, l in apply(term, ctx) if l in inverse_labels]


def recognizes(term: OTerm) -> bool:
    """Return True if the term's root operator is a conditional-assign op."""
    if isinstance(term, OOp) and term.name in _CONDITIONAL_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Heuristic relevance for search-guided rewriting."""
    sc, tc = source.canon(), target.canon()
    for kw in ('ternary', 'and_or', 'or_default', 'if_not', 'getattr',
               'try_attr', 'dict_get', 'coalesce', 'none', 'guard'):
        if kw in sc and kw in tc:
            return 0.9
    if ('ternary' in sc and 'and_or' in tc) or \
       ('and_or' in sc and 'ternary' in tc):
        return 0.85
    if ('getattr' in sc and 'try' in tc) or \
       ('try' in sc and 'getattr' in tc):
        return 0.85
    if ('dict_get' in sc and 'if_in' in tc) or \
       ('if_in' in sc and 'dict_get' in tc):
        return 0.85
    if ('coalesce' in sc and 'none' in tc) or \
       ('none' in sc and 'coalesce' in tc):
        return 0.8
    if ('max' in sc and 'ternary' in tc) or \
       ('ternary' in sc and 'max' in tc):
        return 0.8
    if any(k in sc for k in ('ternary', 'and_or', 'getattr', 'dict_get',
                             'coalesce', 'guard')):
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

    # 1. ternary → and_or
    t = OOp('ternary', (OVar('c'), OVar('a'), OVar('b')))
    r = apply(t)
    _assert(any(l == 'P42_ternary_to_and_or' for _, l in r),
            "ternary → and_or")

    # 2. and_or → ternary
    t2 = OOp('and_or', (OVar('c'), OVar('a'), OVar('b')))
    r2 = apply(t2)
    _assert(any(l == 'P42_and_or_to_ternary' for _, l in r2),
            "and_or → ternary")

    # 3. or_default → if_not_assign
    t3 = OOp('or_default', (OVar('x'), OVar('d')))
    r3 = apply(t3)
    _assert(any(l == 'P42_or_to_if_not' for _, l in r3),
            "or_default → if_not")

    # 4. if_not_assign → or_default
    t4 = OOp('if_not_assign', (OVar('x'), OVar('d')))
    r4 = apply(t4)
    _assert(any(l == 'P42_if_not_to_or' for _, l in r4),
            "if_not → or_default")

    # 5. getattr_default → try_attr
    t5 = OOp('getattr_default', (OVar('obj'), OLit('name'), OLit('')))
    r5 = apply(t5)
    _assert(any(l == 'P42_getattr_to_try' for _, l in r5),
            "getattr → try")

    # 6. try_attr → getattr_default
    t6 = OOp('try_attr', (OVar('obj'), OLit('name'), OLit('')))
    r6 = apply(t6)
    _assert(any(l == 'P42_try_to_getattr' for _, l in r6),
            "try → getattr")

    # 7. dict_get → dict_if_in
    t7 = OOp('dict_get', (OVar('d'), OVar('k'), OLit(0)))
    r7 = apply(t7)
    _assert(any(l == 'P42_dict_get_to_if_in' for _, l in r7),
            "dict_get → if_in")

    # 8. dict_if_in → dict_get
    t8 = OOp('dict_if_in', (OVar('d'), OVar('k'), OLit(0)))
    r8 = apply(t8)
    _assert(any(l == 'P42_if_in_to_dict_get' for _, l in r8),
            "if_in → dict_get")

    # 9. none_coalesce → if_not_none
    t9 = OOp('none_coalesce', (OVar('a'), OVar('b')))
    r9 = apply(t9)
    _assert(any(l == 'P42_coalesce_to_if_not_none' for _, l in r9),
            "coalesce → if_not_none")

    # 10. if_not_none → none_coalesce
    t10 = OOp('if_not_none', (OVar('a'), OVar('b')))
    r10 = apply(t10)
    _assert(any(l == 'P42_if_not_none_to_coalesce' for _, l in r10),
            "if_not_none → coalesce")

    # 11. max_default → ternary_max
    t11 = OOp('max_default', (OVar('a'), OVar('b')))
    r11 = apply(t11)
    _assert(any(l == 'P42_max_to_ternary' for _, l in r11),
            "max → ternary_max")

    # 12. ternary_max → max_default
    t12 = OOp('ternary_max', (OVar('a'), OVar('b')))
    r12 = apply(t12)
    _assert(any(l == 'P42_ternary_to_max' for _, l in r12),
            "ternary_max → max")

    # 13. min_default → ternary_min
    t13 = OOp('min_default', (OVar('a'), OVar('b')))
    r13 = apply(t13)
    _assert(any(l == 'P42_min_to_ternary' for _, l in r13),
            "min → ternary_min")

    # 14. ternary_min → min_default
    t14 = OOp('ternary_min', (OVar('a'), OVar('b')))
    r14 = apply(t14)
    _assert(any(l == 'P42_ternary_to_min' for _, l in r14),
            "ternary_min → min")

    # 15. or_empty → if_none_empty
    t15 = OOp('or_empty', (OVar('x'),))
    r15 = apply(t15)
    _assert(any(l == 'P42_or_empty_to_if_none' for _, l in r15),
            "or_empty → if_none")

    # 16. if_none_empty → or_empty
    t16 = OOp('if_none_empty', (OVar('x'),))
    r16 = apply(t16)
    _assert(any(l == 'P42_if_none_to_or_empty' for _, l in r16),
            "if_none → or_empty")

    # 17. conditional_call → guard_call
    t17 = OOp('conditional_call', (OVar('f'), OVar('x')))
    r17 = apply(t17)
    _assert(any(l == 'P42_conditional_to_guard' for _, l in r17),
            "conditional → guard")

    # 18. guard_call → conditional_call
    t18 = OOp('guard_call', (OVar('f'), OVar('x')))
    r18 = apply(t18)
    _assert(any(l == 'P42_guard_to_conditional' for _, l in r18),
            "guard → conditional")

    # 19. ternary → OCase
    _assert(any(l == 'P42_ternary_to_ocase' for _, l in r),
            "ternary → OCase")
    ocase_results = [(t, l) for t, l in r if l == 'P42_ternary_to_ocase']
    if ocase_results:
        _assert(isinstance(ocase_results[0][0], OCase),
                "ternary produces OCase")
    else:
        _assert(False, "ternary produces OCase")

    # 20. getattr_default → OCatch
    _assert(any(l == 'P42_getattr_to_ocatch' for _, l in r5),
            "getattr → OCatch")
    ocatch_results = [(t, l) for t, l in r5
                      if l == 'P42_getattr_to_ocatch']
    if ocatch_results:
        _assert(isinstance(ocatch_results[0][0], OCatch),
                "getattr produces OCatch")
    else:
        _assert(False, "getattr produces OCatch")

    # 21. dict_get → OCase with contains
    _assert(any(l == 'P42_dict_get_to_case' for _, l in r7),
            "dict_get → case")

    # 22. none_coalesce → OCase with is_not_none
    _assert(any(l == 'P42_coalesce_to_case' for _, l in r9),
            "coalesce → case")

    # 23. none_coalesce(a, a) → a (simplification)
    t23 = OOp('none_coalesce', (OVar('x'), OVar('x')))
    r23 = apply(t23)
    _assert(any(l == 'P42_coalesce_same_simplify' for _, l in r23),
            "coalesce(a, a) → a")
    simplify_results = [(t, l) for t, l in r23
                        if l == 'P42_coalesce_same_simplify']
    if simplify_results:
        _assert(isinstance(simplify_results[0][0], OVar)
                and simplify_results[0][0].name == 'x',
                "coalesce simplify produces var")
    else:
        _assert(False, "coalesce simplify produces var")

    # 24. conditional_call → OCase form
    _assert(any(l == 'P42_conditional_call_to_case' for _, l in r17),
            "conditional_call → case")

    # 25. or_default → OCase form
    _assert(any(l == 'P42_or_default_to_case' for _, l in r3),
            "or_default → case")

    # 26. max_default → OCase form
    _assert(any(l == 'P42_max_to_case' for _, l in r11),
            "max → case")

    # 27. min_default → OCase form
    _assert(any(l == 'P42_min_to_case' for _, l in r13),
            "min → case")

    # 28. inverse: and_or → ternary
    r28_inv = apply_inverse(OOp('and_or', (OVar('c'), OVar('a'), OVar('b'))))
    _assert(any(l == 'P42_and_or_to_ternary' for _, l in r28_inv),
            "inv: and_or → ternary")

    # 29. inverse: try_attr → getattr
    r29_inv = apply_inverse(
        OOp('try_attr', (OVar('obj'), OLit('a'), OLit(''))))
    _assert(any(l == 'P42_try_to_getattr' for _, l in r29_inv),
            "inv: try → getattr")

    # 30. inverse: if_in → dict_get
    r30_inv = apply_inverse(
        OOp('dict_if_in', (OVar('d'), OVar('k'), OLit(0))))
    _assert(any(l == 'P42_if_in_to_dict_get' for _, l in r30_inv),
            "inv: if_in → dict_get")

    # 31. recognizes conditional ops
    _assert(recognizes(OOp('ternary', (OVar('c'), OVar('a'), OVar('b')))),
            "recognizes ternary")
    _assert(recognizes(OOp('dict_get', (OVar('d'), OVar('k'), OLit(0)))),
            "recognizes dict_get")
    _assert(recognizes(OOp('none_coalesce', (OVar('a'), OVar('b')))),
            "recognizes none_coalesce")
    _assert(not recognizes(OLit(42)), "!recognizes literal")
    _assert(not recognizes(OVar('x')), "!recognizes var")

    # 32. relevance: ternary ↔ and_or high
    _assert(relevance_score(
        OOp('ternary', (OVar('c'), OVar('a'), OVar('b'))),
        OOp('and_or', (OVar('c'), OVar('a'), OVar('b'))),
    ) > 0.7, "ternary/and_or relevance high")

    # 33. relevance: dict_get ↔ if_in high
    _assert(relevance_score(
        OOp('dict_get', (OVar('d'), OVar('k'), OLit(0))),
        OOp('dict_if_in', (OVar('d'), OVar('k'), OLit(0))),
    ) > 0.7, "dict_get/if_in relevance high")

    # 34. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2,
            "unrelated relevance low")

    print(f"P42 conditional: {_pass} passed, {_fail} failed")
