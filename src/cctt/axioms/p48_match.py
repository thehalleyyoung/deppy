"""P48 Axiom: Structural Pattern Matching Equivalences.

Establishes equivalences between Python 3.10+ structural pattern matching
(match/case) and equivalent if/elif chains, isinstance checks, dict lookups,
and slice unpacking.

Mathematical basis: match/case is a coproduct eliminator in the category of
Python types.  Each case clause selects a summand of a coproduct (disjoint
union) type and projects the associated data.  The equivalence with if/elif
chains is the universal property of the coproduct: any morphism out of a
coproduct A + B → C is uniquely determined by a pair of morphisms A → C
and B → C.  The match statement is the categorical "case analysis" and
the if/elif chain is its explicit Church encoding.

  match x / case [a, *rest]       ≡  a, rest = x[0], x[1:]     (sequence unpack)
  match x / case {"key": val}     ≡  val = x["key"]            (mapping lookup)
  match x / case Point(x, y)      ≡  isinstance + attr access  (class pattern)
  match x / case v if guard       ≡  if isinstance and guard   (guarded pattern)
  match x / case _                ≡  else                      (wildcard / default)
  match x / case A | B            ≡  isinstance(x, (A, B))     (or-pattern)
  match x / case 42               ≡  if x == 42                (value pattern)
  match x / case v                ≡  v = x                     (capture pattern)
  match x / case [_, _, *rest]    ≡  rest = x[2:]              (star pattern)
  match x / case Outer(Inner(y))  ≡  nested isinstance         (nested pattern)

Key rewrites:
  • match_case(x, branches) ↔ if_elif_chain(x, branches)
  • match_sequence(x, pat) ↔ slice_unpack(x, pat)
  • match_mapping(x, pat) ↔ dict_lookup(x, pat)
  • match_class(x, cls, attrs) ↔ isinstance_attrs(x, cls, attrs)
  • match_guard(x, pat, guard) ↔ isinstance_and_guard(x, pat, guard)
  • match_wildcard(x) ↔ else_branch(x)
  • match_or(x, pats) ↔ isinstance_or(x, pats)
  • match_value(x, val) ↔ eq_check(x, val)
  • match_capture(x, name) ↔ assign_var(x, name)
  • match_star(x, prefix_len) ↔ rest_slice(x, prefix_len)
  • match_nested(x, outer, inner) ↔ nested_isinstance(x, outer, inner)

(§P48, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P48_match"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P42_conditional", "P09_exceptions", "P21_comparisons"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P48 Structural Pattern Matching Equivalences).

1. match_case(x, branches) ≡ if_elif_chain(x, branches)
   A match statement with n case clauses is equivalent to an
   if/elif chain with n branches, each testing the pattern.

2. match_sequence(x, pat) ≡ slice_unpack(x, pat)
   case [a, *rest] ≡ a, rest = x[0], x[1:].
   Sequence pattern destructuring is equivalent to index + slice.

3. match_mapping(x, pat) ≡ dict_lookup(x, pat)
   case {"key": val} ≡ val = x["key"].
   Mapping pattern destructuring is equivalent to dict subscript.

4. match_class(x, cls, attrs) ≡ isinstance_attrs(x, cls, attrs)
   case Point(x, y) ≡ isinstance(x, Point) and x.x, x.y.
   Class pattern is isinstance check plus attribute access.

5. match_guard(x, pat, guard) ≡ isinstance_and_guard(x, pat, guard)
   case v if guard ≡ if isinstance(x, ...) and guard.
   Guarded pattern adds a boolean predicate to pattern match.

6. match_wildcard(x) ≡ else_branch(x)
   case _ always matches — equivalent to an else clause.

7. match_or(x, pats) ≡ isinstance_or(x, pats)
   case A | B ≡ isinstance(x, (A, B)).
   Or-pattern is a union of type checks.

8. match_value(x, val) ≡ eq_check(x, val)
   case 42 ≡ if x == 42.
   Value pattern is an equality check.

9. match_capture(x, name) ≡ assign_var(x, name)
   case v (capture) ≡ v = x.
   Capture pattern binds the value to a variable.

10. match_star(x, prefix_len) ≡ rest_slice(x, prefix_len)
    case [_, _, *rest] ≡ rest = x[prefix_len:].
    Star capture is a slice from the prefix length.

11. match_nested(x, outer, inner) ≡ nested_isinstance(x, outer, inner)
    case Outer(Inner(y)) ≡ isinstance(x, Outer) and isinstance(x.inner, Inner).
    Nested class patterns compose isinstance checks.
"""

EXAMPLES = [
    ("match_case($x, $branches)", "if_elif_chain($x, $branches)",
     "P48_match_to_if_elif"),
    ("match_sequence($x, $pat)", "slice_unpack($x, $pat)",
     "P48_sequence_to_slice"),
    ("match_mapping($x, $pat)", "dict_lookup($x, $pat)",
     "P48_mapping_to_lookup"),
    ("match_class($x, $cls, $attrs)", "isinstance_attrs($x, $cls, $attrs)",
     "P48_class_to_isinstance"),
    ("match_wildcard($x)", "else_branch($x)",
     "P48_wildcard_to_else"),
]

# All operator names handled by this axiom.
_MATCH_OPS = frozenset({
    'match_case', 'if_elif_chain', 'match_sequence', 'slice_unpack',
    'match_mapping', 'dict_lookup', 'match_class', 'isinstance_attrs',
    'match_guard', 'isinstance_and_guard', 'match_wildcard', 'else_branch',
    'match_or', 'isinstance_or', 'match_value', 'eq_check',
    'match_capture', 'assign_var', 'match_star', 'rest_slice',
    'match_nested', 'nested_isinstance',
})

# Mapping: (match_form, elif_form, arity, forward_label, inverse_label).
_PAIRS: Tuple[Tuple[str, str, int, str, str], ...] = (
    ('match_case',     'if_elif_chain',      2, 'P48_match_to_if_elif',       'P48_if_elif_to_match'),
    ('match_sequence', 'slice_unpack',        2, 'P48_sequence_to_slice',      'P48_slice_to_sequence'),
    ('match_mapping',  'dict_lookup',         2, 'P48_mapping_to_lookup',      'P48_lookup_to_mapping'),
    ('match_class',    'isinstance_attrs',    3, 'P48_class_to_isinstance',    'P48_isinstance_to_class'),
    ('match_guard',    'isinstance_and_guard', 3, 'P48_guard_to_isinstance',   'P48_isinstance_to_guard'),
    ('match_wildcard', 'else_branch',         1, 'P48_wildcard_to_else',       'P48_else_to_wildcard'),
    ('match_or',       'isinstance_or',       2, 'P48_or_to_isinstance',       'P48_isinstance_to_or'),
    ('match_value',    'eq_check',            2, 'P48_value_to_eq',            'P48_eq_to_value'),
    ('match_capture',  'assign_var',          2, 'P48_capture_to_assign',      'P48_assign_to_capture'),
    ('match_star',     'rest_slice',          2, 'P48_star_to_slice',          'P48_slice_to_star'),
    ('match_nested',   'nested_isinstance',   3, 'P48_nested_to_isinstance',  'P48_isinstance_to_nested'),
)

# Precomputed lookup tables.
_MATCH_TO_ELIF = {m: (e, ar, fwd) for m, e, ar, fwd, _ in _PAIRS}
_ELIF_TO_MATCH = {e: (m, ar, inv) for m, e, ar, _, inv in _PAIRS}

# Labels that belong to the inverse direction.
_INVERSE_LABELS = frozenset(inv for _, _, _, _, inv in _PAIRS)


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P48: Structural pattern matching equivalence rewrites."""
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp):
        return results

    # ── Match form → if/elif form ──
    if term.name in _MATCH_TO_ELIF:
        elif_name, arity, label = _MATCH_TO_ELIF[term.name]
        if len(term.args) >= arity:
            results.append((
                OOp(elif_name, term.args),
                label,
            ))

    # ── If/elif form → match form ──
    if term.name in _ELIF_TO_MATCH:
        match_name, arity, label = _ELIF_TO_MATCH[term.name]
        if len(term.args) >= arity:
            results.append((
                OOp(match_name, term.args),
                label,
            ))

    # ── Structural expansions ──

    # match_case(x, branches) → OCase chain
    if term.name == 'match_case' and len(term.args) >= 2:
        x, branches = term.args[0], term.args[1]
        results.append((
            OCase(x, branches, OOp('else_branch', (x,))),
            'P48_match_to_case',
        ))

    # match_sequence(x, pat) → OSeq of index accesses
    if term.name == 'match_sequence' and len(term.args) == 2:
        x, pat = term.args
        results.append((
            OSeq((
                OOp('getitem', (x, OLit(0))),
                OOp('slice', (x, OLit(1), OUnknown('end'))),
            )),
            'P48_sequence_to_oseq',
        ))

    # match_mapping(x, pat) → OOp('getitem', ...) for key access
    if term.name == 'match_mapping' and len(term.args) == 2:
        x, pat = term.args
        results.append((
            OOp('getitem', (x, pat)),
            'P48_mapping_to_getitem',
        ))

    # match_class(x, cls, attrs) → OCase(isinstance, attr_access, fail)
    if term.name == 'match_class' and len(term.args) >= 3:
        x, cls, attrs = term.args[0], term.args[1], term.args[2]
        results.append((
            OCase(
                OOp('isinstance', (x, cls)),
                OOp('getattr_multi', (x, attrs)),
                OLit(None),
            ),
            'P48_class_to_case',
        ))

    # match_guard(x, pat, guard) → OCase with compound test
    if term.name == 'match_guard' and len(term.args) >= 3:
        x, pat, guard = term.args[0], term.args[1], term.args[2]
        results.append((
            OCase(
                OOp('and', (OOp('isinstance_attrs', (x, pat, OLit(None))), guard)),
                x,
                OLit(None),
            ),
            'P48_guard_to_case',
        ))

    # match_wildcard(x) → x (identity — wildcard always matches)
    if term.name == 'match_wildcard' and len(term.args) >= 1:
        x = term.args[0]
        results.append((x, 'P48_wildcard_to_identity'))

    # match_or(x, pats) → OCase with isinstance union
    if term.name == 'match_or' and len(term.args) >= 2:
        x, pats = term.args[0], term.args[1]
        results.append((
            OCase(OOp('isinstance', (x, pats)), x, OLit(None)),
            'P48_or_to_case',
        ))

    # match_value(x, val) → OCase(eq(x, val), ...)
    if term.name == 'match_value' and len(term.args) >= 2:
        x, val = term.args[0], term.args[1]
        results.append((
            OCase(OOp('eq', (x, val)), x, OLit(None)),
            'P48_value_to_case',
        ))

    # match_capture(x, name) → OOp('assign', (name, x))
    if term.name == 'match_capture' and len(term.args) >= 2:
        x, name = term.args[0], term.args[1]
        results.append((
            OOp('assign', (name, x)),
            'P48_capture_to_assign_op',
        ))

    # match_star(x, prefix_len) → OOp('slice', (x, prefix_len, end))
    if term.name == 'match_star' and len(term.args) >= 2:
        x, prefix_len = term.args[0], term.args[1]
        results.append((
            OOp('slice', (x, prefix_len, OUnknown('end'))),
            'P48_star_to_slice_op',
        ))

    # match_nested(x, outer, inner) → compound isinstance chain
    if term.name == 'match_nested' and len(term.args) >= 3:
        x, outer, inner = term.args[0], term.args[1], term.args[2]
        results.append((
            OOp('and', (
                OOp('isinstance', (x, outer)),
                OOp('isinstance', (OOp('getattr', (x, OLit('inner'))), inner)),
            )),
            'P48_nested_to_compound',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Return reverse rewrites (if/elif → match form)."""
    return [(t, l) for t, l in apply(term, ctx) if l in _INVERSE_LABELS]


def recognizes(term: OTerm) -> bool:
    """Return True if the term's root operator is a match/case op."""
    if isinstance(term, OOp) and term.name in _MATCH_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Heuristic relevance for search-guided rewriting."""
    sc, tc = source.canon(), target.canon()
    for match_name, elif_name, _, _, _ in _PAIRS:
        if match_name in sc and elif_name in tc:
            return 0.9
        if elif_name in sc and match_name in tc:
            return 0.9
    for kw in _MATCH_OPS:
        if kw in sc and kw in tc:
            return 0.85
    if any(k in sc for k in ('match_case', 'match_sequence', 'match_mapping',
                             'match_class', 'match_guard', 'match_wildcard',
                             'match_or', 'match_value', 'match_capture',
                             'match_star', 'match_nested')):
        return 0.3
    if any(k in sc for k in ('if_elif_chain', 'slice_unpack', 'dict_lookup',
                             'isinstance_attrs', 'isinstance_and_guard',
                             'else_branch', 'isinstance_or', 'eq_check',
                             'assign_var', 'rest_slice', 'nested_isinstance')):
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

    # 1. match_case → if_elif_chain
    t1 = OOp('match_case', (OVar('x'), OSeq((OLit(1), OLit(2)))))
    r1 = apply(t1)
    _assert(any(l == 'P48_match_to_if_elif' for _, l in r1),
            "match_case → if_elif_chain")

    # 2. if_elif_chain → match_case
    t2 = OOp('if_elif_chain', (OVar('x'), OSeq((OLit(1), OLit(2)))))
    r2 = apply(t2)
    _assert(any(l == 'P48_if_elif_to_match' for _, l in r2),
            "if_elif_chain → match_case")

    # 3. match_sequence → slice_unpack
    t3 = OOp('match_sequence', (OVar('xs'), OLit('pattern')))
    r3 = apply(t3)
    _assert(any(l == 'P48_sequence_to_slice' for _, l in r3),
            "match_sequence → slice_unpack")

    # 4. slice_unpack → match_sequence
    t4 = OOp('slice_unpack', (OVar('xs'), OLit('pattern')))
    r4 = apply(t4)
    _assert(any(l == 'P48_slice_to_sequence' for _, l in r4),
            "slice_unpack → match_sequence")

    # 5. match_mapping → dict_lookup
    t5 = OOp('match_mapping', (OVar('d'), OLit('key')))
    r5 = apply(t5)
    _assert(any(l == 'P48_mapping_to_lookup' for _, l in r5),
            "match_mapping → dict_lookup")

    # 6. dict_lookup → match_mapping
    t6 = OOp('dict_lookup', (OVar('d'), OLit('key')))
    r6 = apply(t6)
    _assert(any(l == 'P48_lookup_to_mapping' for _, l in r6),
            "dict_lookup → match_mapping")

    # 7. match_class → isinstance_attrs
    t7 = OOp('match_class', (OVar('p'), OLit('Point'), OSeq((OLit('x'), OLit('y')))))
    r7 = apply(t7)
    _assert(any(l == 'P48_class_to_isinstance' for _, l in r7),
            "match_class → isinstance_attrs")

    # 8. isinstance_attrs → match_class
    t8 = OOp('isinstance_attrs', (OVar('p'), OLit('Point'), OSeq((OLit('x'), OLit('y')))))
    r8 = apply(t8)
    _assert(any(l == 'P48_isinstance_to_class' for _, l in r8),
            "isinstance_attrs → match_class")

    # 9. match_guard → isinstance_and_guard
    t9 = OOp('match_guard', (OVar('x'), OLit('int'), OOp('gt', (OVar('x'), OLit(0)))))
    r9 = apply(t9)
    _assert(any(l == 'P48_guard_to_isinstance' for _, l in r9),
            "match_guard → isinstance_and_guard")

    # 10. isinstance_and_guard → match_guard
    t10 = OOp('isinstance_and_guard', (OVar('x'), OLit('int'), OOp('gt', (OVar('x'), OLit(0)))))
    r10 = apply(t10)
    _assert(any(l == 'P48_isinstance_to_guard' for _, l in r10),
            "isinstance_and_guard → match_guard")

    # 11. match_wildcard → else_branch
    t11 = OOp('match_wildcard', (OVar('x'),))
    r11 = apply(t11)
    _assert(any(l == 'P48_wildcard_to_else' for _, l in r11),
            "match_wildcard → else_branch")

    # 12. else_branch → match_wildcard
    t12 = OOp('else_branch', (OVar('x'),))
    r12 = apply(t12)
    _assert(any(l == 'P48_else_to_wildcard' for _, l in r12),
            "else_branch → match_wildcard")

    # 13. match_or → isinstance_or
    t13 = OOp('match_or', (OVar('x'), OSeq((OLit('int'), OLit('float')))))
    r13 = apply(t13)
    _assert(any(l == 'P48_or_to_isinstance' for _, l in r13),
            "match_or → isinstance_or")

    # 14. isinstance_or → match_or
    t14 = OOp('isinstance_or', (OVar('x'), OSeq((OLit('int'), OLit('float')))))
    r14 = apply(t14)
    _assert(any(l == 'P48_isinstance_to_or' for _, l in r14),
            "isinstance_or → match_or")

    # 15. match_value → eq_check
    t15 = OOp('match_value', (OVar('x'), OLit(42)))
    r15 = apply(t15)
    _assert(any(l == 'P48_value_to_eq' for _, l in r15),
            "match_value → eq_check")

    # 16. eq_check → match_value
    t16 = OOp('eq_check', (OVar('x'), OLit(42)))
    r16 = apply(t16)
    _assert(any(l == 'P48_eq_to_value' for _, l in r16),
            "eq_check → match_value")

    # 17. match_capture → assign_var
    t17 = OOp('match_capture', (OVar('x'), OLit('result')))
    r17 = apply(t17)
    _assert(any(l == 'P48_capture_to_assign' for _, l in r17),
            "match_capture → assign_var")

    # 18. assign_var → match_capture
    t18 = OOp('assign_var', (OVar('x'), OLit('result')))
    r18 = apply(t18)
    _assert(any(l == 'P48_assign_to_capture' for _, l in r18),
            "assign_var → match_capture")

    # 19. match_star → rest_slice
    t19 = OOp('match_star', (OVar('xs'), OLit(2)))
    r19 = apply(t19)
    _assert(any(l == 'P48_star_to_slice' for _, l in r19),
            "match_star → rest_slice")

    # 20. rest_slice → match_star
    t20 = OOp('rest_slice', (OVar('xs'), OLit(2)))
    r20 = apply(t20)
    _assert(any(l == 'P48_slice_to_star' for _, l in r20),
            "rest_slice → match_star")

    # 21. match_nested → nested_isinstance
    t21 = OOp('match_nested', (OVar('x'), OLit('Outer'), OLit('Inner')))
    r21 = apply(t21)
    _assert(any(l == 'P48_nested_to_isinstance' for _, l in r21),
            "match_nested → nested_isinstance")

    # 22. nested_isinstance → match_nested
    t22 = OOp('nested_isinstance', (OVar('x'), OLit('Outer'), OLit('Inner')))
    r22 = apply(t22)
    _assert(any(l == 'P48_isinstance_to_nested' for _, l in r22),
            "nested_isinstance → match_nested")

    # 23. match_case → OCase structural
    _assert(any(l == 'P48_match_to_case' for _, l in r1),
            "match_case → OCase structural")
    mc = [(t, l) for t, l in r1 if l == 'P48_match_to_case']
    if mc:
        _assert(isinstance(mc[0][0], OCase),
                "match_case produces OCase")
    else:
        _assert(False, "match_case produces OCase")

    # 24. match_sequence → OSeq structural
    _assert(any(l == 'P48_sequence_to_oseq' for _, l in r3),
            "match_sequence → OSeq structural")
    sq = [(t, l) for t, l in r3 if l == 'P48_sequence_to_oseq']
    if sq:
        _assert(isinstance(sq[0][0], OSeq),
                "match_sequence produces OSeq")
    else:
        _assert(False, "match_sequence produces OSeq")

    # 25. match_mapping → getitem structural
    _assert(any(l == 'P48_mapping_to_getitem' for _, l in r5),
            "match_mapping → getitem structural")

    # 26. match_class → OCase structural
    _assert(any(l == 'P48_class_to_case' for _, l in r7),
            "match_class → OCase structural")
    cl = [(t, l) for t, l in r7 if l == 'P48_class_to_case']
    if cl:
        _assert(isinstance(cl[0][0], OCase),
                "match_class produces OCase")
    else:
        _assert(False, "match_class produces OCase")

    # 27. match_guard → OCase structural
    _assert(any(l == 'P48_guard_to_case' for _, l in r9),
            "match_guard → OCase structural")

    # 28. match_wildcard → identity structural
    _assert(any(l == 'P48_wildcard_to_identity' for _, l in r11),
            "match_wildcard → identity")
    wi = [(t, l) for t, l in r11 if l == 'P48_wildcard_to_identity']
    if wi:
        _assert(isinstance(wi[0][0], OVar),
                "wildcard identity produces OVar")
    else:
        _assert(False, "wildcard identity produces OVar")

    # 29. match_or → OCase structural
    _assert(any(l == 'P48_or_to_case' for _, l in r13),
            "match_or → OCase structural")

    # 30. match_value → OCase structural
    _assert(any(l == 'P48_value_to_case' for _, l in r15),
            "match_value → OCase structural")

    # 31. match_capture → assign structural
    _assert(any(l == 'P48_capture_to_assign_op' for _, l in r17),
            "match_capture → assign op")

    # 32. match_star → slice structural
    _assert(any(l == 'P48_star_to_slice_op' for _, l in r19),
            "match_star → slice op")

    # 33. match_nested → compound structural
    _assert(any(l == 'P48_nested_to_compound' for _, l in r21),
            "match_nested → compound isinstance")

    # 34. inverse: if_elif_chain → match_case
    r34_inv = apply_inverse(OOp('if_elif_chain', (OVar('x'), OSeq((OLit(1),)))))
    _assert(any(l == 'P48_if_elif_to_match' for _, l in r34_inv),
            "inv: if_elif → match")

    # 35. inverse: slice_unpack → match_sequence
    r35_inv = apply_inverse(OOp('slice_unpack', (OVar('xs'), OLit('p'))))
    _assert(any(l == 'P48_slice_to_sequence' for _, l in r35_inv),
            "inv: slice_unpack → sequence")

    # 36. inverse: eq_check → match_value
    r36_inv = apply_inverse(OOp('eq_check', (OVar('x'), OLit(42))))
    _assert(any(l == 'P48_eq_to_value' for _, l in r36_inv),
            "inv: eq_check → value")

    # 37. recognizes match ops
    _assert(recognizes(OOp('match_case', (OVar('x'), OLit(1)))),
            "recognizes match_case")
    _assert(recognizes(OOp('if_elif_chain', (OVar('x'), OLit(1)))),
            "recognizes if_elif_chain")
    _assert(recognizes(OOp('match_wildcard', (OVar('x'),))),
            "recognizes match_wildcard")
    _assert(recognizes(OOp('match_nested', (OVar('x'), OLit('A'), OLit('B')))),
            "recognizes match_nested")
    _assert(not recognizes(OLit(42)), "!recognizes literal")
    _assert(not recognizes(OVar('x')), "!recognizes var")

    # 38. relevance: match_case ↔ if_elif_chain high
    _assert(relevance_score(
        OOp('match_case', (OVar('x'), OLit(1))),
        OOp('if_elif_chain', (OVar('x'), OLit(1))),
    ) > 0.7, "match/elif relevance high")

    # 39. relevance: match_class ↔ isinstance_attrs high
    _assert(relevance_score(
        OOp('match_class', (OVar('p'), OLit('Point'), OLit('attrs'))),
        OOp('isinstance_attrs', (OVar('p'), OLit('Point'), OLit('attrs'))),
    ) > 0.7, "class/isinstance relevance high")

    # 40. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2,
            "unrelated relevance low")

    # 41. no rewrites for non-OOp
    _assert(apply(OVar('x')) == [], "no rewrites for OVar")
    _assert(apply(OLit(42)) == [], "no rewrites for OLit")

    print(f"P48 match: {_pass} passed, {_fail} failed")
