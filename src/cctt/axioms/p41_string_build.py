"""P41 Axiom: String Join/Build Equivalences.

Establishes equivalences between different Python string-building
patterns: "".join(parts) vs + concatenation, f-strings vs
.format() vs %-formatting, io.StringIO vs list+join, str.translate
vs chained replace, and re.sub vs multiple replaces.

Mathematical basis: string concatenation is the free-monoid
operation on the alphabet Σ*:

  concat : Σ* × Σ* → Σ*
  join(sep, parts) = intercalate(sep, parts) = foldl1(λa b. a ⊕ sep ⊕ b, parts)

where ⊕ is concatenation.

"".join(parts) computes concat in O(n) by pre-allocating the
result buffer.  Repeated s += x is O(n²) in the worst case
because each += may copy the growing string.

f-strings, .format(), and %-formatting are all syntactic
variants of the same interpolation operation:

  interp : Template × Tuple(Σ*) → Σ*

str.translate applies a character-level map χ : Σ → Σ ∪ {ε},
while chained .replace(a, b) applies sequential substitutions.
They are equivalent when the replacements are non-overlapping
single-character maps.

Key rewrites:
  • "".join(parts) ↔ s += x loop   (join is O(n), loop is O(n²))
  • f"{a}{b}{c}" ↔ a + b + c ↔ "{}{}{}".format(a,b,c)
  • io.StringIO build ↔ list + join
  • str.translate ↔ chain of replace
  • re.sub ↔ multiple replace (when pattern is literal alternation)
  • sep.join(map(f, xs)) ↔ sep.join(f(x) for x in xs)
  • sep.join(strs) ↔ loop with sep concatenation
  • str builder append pattern ↔ list + join

(§P41, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P41_string_build"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P04_string_ops", "P22_format", "P25_regex"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P41 String Join/Build Equivalences).

1. str_join(parts) ≡ str_concat(parts)
   "".join(parts) and the loop s = ""; for p in parts: s += p
   both compute concat(parts).  join is O(n); += loop is O(n²).

2. fstring_concat(a, b, c) ≡ format_concat(a, b, c)
   f"{a}{b}{c}" and "{}{}{}".format(a, b, c) both compute
   str(a) + str(b) + str(c).

3. fstring_concat(a, b, c) ≡ percent_format(a, b, c)
   f"{a}{b}{c}" and "%s%s%s" % (a, b, c) are equivalent
   when all values are string-coercible.

4. stringio_build(ops) ≡ list_join_build(ops)
   Building a string with io.StringIO().write() calls and
   building with a list of parts then "".join() produce the
   same result.

5. str_translate(s, table) ≡ chain_replace(s, replacements)
   s.translate(table) and sequential s.replace(old, new) calls
   are equivalent for non-overlapping single-char replacements.

6. re_sub_multi(pattern, repl, s) ≡ multi_replace(s, pairs)
   re.sub with a literal alternation pattern and a dict-based
   replacement function is equivalent to sequential replaces
   when the patterns don't overlap.

7. str_join_sep(sep, parts) ≡ str_concat_sep(sep, parts)
   sep.join(parts) and the manual loop with sep insertion both
   compute intercalate(sep, parts).

8. str_join_map(sep, f, xs) ≡ str_concat_map(sep, f, xs)
   sep.join(f(x) for x in xs) and sep.join(map(f, xs)) are
   equivalent — both apply f then join with sep.

9. str_builder_append(ops) ≡ list_join_build(ops)
   The builder pattern (append to list, join at end) is
   equivalent to StringIO or direct list+join.

10. fstring_concat → OFold using string concat.
"""

EXAMPLES = [
    ("str_join($parts)", "str_concat($parts)", "P41_join_to_concat"),
    ("fstring_concat($a, $b, $c)", "format_concat($a, $b, $c)",
     "P41_fstring_to_format"),
    ("stringio_build($ops)", "list_join_build($ops)",
     "P41_stringio_to_list_join"),
    ("str_translate($s, $table)", "chain_replace($s, $repls)",
     "P41_translate_to_replace"),
    ("str_join_sep($sep, $parts)", "str_concat_sep($sep, $parts)",
     "P41_join_sep_to_concat_sep"),
]

_STRING_BUILD_OPS = frozenset({
    'str_join', 'str_concat', 'fstring_concat', 'format_concat',
    'percent_format', 'stringio_build', 'list_join_build',
    'str_translate', 'chain_replace', 're_sub_multi', 'multi_replace',
    'str_join_sep', 'str_concat_sep', 'str_join_map', 'str_concat_map',
    'str_builder_append',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P41: String join/build equivalence rewrites (forward)."""
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp):
        return results

    # ── 1. str_join ↔ str_concat ──
    if term.name == 'str_join' and len(term.args) >= 1:
        results.append((
            OOp('str_concat', term.args),
            'P41_join_to_concat',
        ))

    if term.name == 'str_concat' and len(term.args) >= 1:
        results.append((
            OOp('str_join', term.args),
            'P41_concat_to_join',
        ))

    # ── 2. fstring_concat ↔ format_concat ──
    if term.name == 'fstring_concat' and len(term.args) >= 1:
        results.append((
            OOp('format_concat', term.args),
            'P41_fstring_to_format',
        ))

    if term.name == 'format_concat' and len(term.args) >= 1:
        results.append((
            OOp('fstring_concat', term.args),
            'P41_format_to_fstring',
        ))

    # ── 3. fstring_concat ↔ percent_format ──
    if term.name == 'fstring_concat' and len(term.args) >= 1:
        results.append((
            OOp('percent_format', term.args),
            'P41_fstring_to_percent',
        ))

    if term.name == 'percent_format' and len(term.args) >= 1:
        results.append((
            OOp('fstring_concat', term.args),
            'P41_percent_to_fstring',
        ))

    # ── 4. format_concat ↔ percent_format ──
    if term.name == 'format_concat' and len(term.args) >= 1:
        results.append((
            OOp('percent_format', term.args),
            'P41_format_to_percent',
        ))

    if term.name == 'percent_format' and len(term.args) >= 1:
        results.append((
            OOp('format_concat', term.args),
            'P41_percent_to_format',
        ))

    # ── 5. stringio_build ↔ list_join_build ──
    if term.name == 'stringio_build' and len(term.args) >= 1:
        results.append((
            OOp('list_join_build', term.args),
            'P41_stringio_to_list_join',
        ))

    if term.name == 'list_join_build' and len(term.args) >= 1:
        results.append((
            OOp('stringio_build', term.args),
            'P41_list_join_to_stringio',
        ))

    # ── 6. str_translate ↔ chain_replace ──
    if term.name == 'str_translate' and len(term.args) == 2:
        results.append((
            OOp('chain_replace', term.args),
            'P41_translate_to_replace',
        ))

    if term.name == 'chain_replace' and len(term.args) == 2:
        results.append((
            OOp('str_translate', term.args),
            'P41_replace_to_translate',
        ))

    # ── 7. re_sub_multi ↔ multi_replace ──
    if term.name == 're_sub_multi' and len(term.args) >= 2:
        results.append((
            OOp('multi_replace', term.args),
            'P41_re_sub_to_multi_replace',
        ))

    if term.name == 'multi_replace' and len(term.args) >= 2:
        results.append((
            OOp('re_sub_multi', term.args),
            'P41_multi_replace_to_re_sub',
        ))

    # ── 8. str_join_sep ↔ str_concat_sep ──
    if term.name == 'str_join_sep' and len(term.args) == 2:
        results.append((
            OOp('str_concat_sep', term.args),
            'P41_join_sep_to_concat_sep',
        ))

    if term.name == 'str_concat_sep' and len(term.args) == 2:
        results.append((
            OOp('str_join_sep', term.args),
            'P41_concat_sep_to_join_sep',
        ))

    # ── 9. str_join_map ↔ str_concat_map ──
    if term.name == 'str_join_map' and len(term.args) == 3:
        results.append((
            OOp('str_concat_map', term.args),
            'P41_join_map_to_concat_map',
        ))

    if term.name == 'str_concat_map' and len(term.args) == 3:
        results.append((
            OOp('str_join_map', term.args),
            'P41_concat_map_to_join_map',
        ))

    # ── 10. str_builder_append ↔ list_join_build ──
    if term.name == 'str_builder_append' and len(term.args) >= 1:
        results.append((
            OOp('list_join_build', term.args),
            'P41_builder_to_list_join',
        ))

    if term.name == 'list_join_build' and len(term.args) >= 1:
        results.append((
            OOp('str_builder_append', term.args),
            'P41_list_join_to_builder',
        ))

    # ── 11. fstring_concat → str_concat (+ operator) ──
    if term.name == 'fstring_concat' and len(term.args) >= 2:
        results.append((
            OOp('str_concat', term.args),
            'P41_fstring_to_plus',
        ))

    # ── 12. str_join → OFold form ──
    if term.name == 'str_join' and len(term.args) == 1:
        parts = term.args[0]
        results.append((
            OFold('str_add', OLit(""), parts),
            'P41_join_to_fold',
        ))

    # ── 13. str_join_map → str_join(map(…)) structural ──
    if term.name == 'str_join_map' and len(term.args) == 3:
        sep, f, xs = term.args
        results.append((
            OOp('str_join_sep', (sep, OMap(f, xs))),
            'P41_join_map_to_join_mapped',
        ))

    # ── 14. str_join with literal parts → single OLit ──
    if term.name == 'str_join' and len(term.args) == 1:
        parts = term.args[0]
        if isinstance(parts, OSeq) and all(
                isinstance(p, OLit) and isinstance(p.value, str)
                for p in parts.elements):
            joined = "".join(p.value for p in parts.elements)  # type: ignore
            results.append((
                OLit(joined),
                'P41_join_literal_to_str',
            ))

    # ── 15. str_join_sep with literal parts → single OLit ──
    if term.name == 'str_join_sep' and len(term.args) == 2:
        sep, parts = term.args
        if isinstance(sep, OLit) and isinstance(sep.value, str) \
                and isinstance(parts, OSeq) and all(
                    isinstance(p, OLit) and isinstance(p.value, str)
                    for p in parts.elements):
            joined = sep.value.join(  # type: ignore
                p.value for p in parts.elements)  # type: ignore
            results.append((
                OLit(joined),
                'P41_join_sep_literal_to_str',
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Return reverse rewrites (concat/manual → join/idiomatic form)."""
    inverse_labels = {
        'P41_concat_to_join', 'P41_format_to_fstring',
        'P41_percent_to_fstring', 'P41_list_join_to_stringio',
        'P41_replace_to_translate', 'P41_multi_replace_to_re_sub',
        'P41_concat_sep_to_join_sep', 'P41_concat_map_to_join_map',
        'P41_list_join_to_builder',
    }
    return [(t, l) for t, l in apply(term, ctx) if l in inverse_labels]


def recognizes(term: OTerm) -> bool:
    """Return True if the term's root operator is a string-build op."""
    if isinstance(term, OOp) and term.name in _STRING_BUILD_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Heuristic relevance for search-guided rewriting."""
    sc, tc = source.canon(), target.canon()
    for kw in ('join', 'concat', 'fstring', 'format', 'percent',
               'stringio', 'translate', 'replace', 'builder'):
        if kw in sc and kw in tc:
            return 0.9
    if ('join' in sc and 'concat' in tc) or \
       ('concat' in sc and 'join' in tc):
        return 0.85
    if ('fstring' in sc and 'format' in tc) or \
       ('format' in sc and 'fstring' in tc):
        return 0.85
    if ('translate' in sc and 'replace' in tc) or \
       ('replace' in sc and 'translate' in tc):
        return 0.8
    if ('stringio' in sc and 'list' in tc) or \
       ('list' in sc and 'stringio' in tc):
        return 0.8
    if any(k in sc for k in ('join', 'concat', 'fstring', 'format',
                             'stringio', 'translate')):
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

    # 1. str_join → str_concat
    t = OOp('str_join', (OVar('parts'),))
    r = apply(t)
    _assert(any(l == 'P41_join_to_concat' for _, l in r),
            "join → concat")

    # 2. str_concat → str_join
    t2 = OOp('str_concat', (OVar('parts'),))
    r2 = apply(t2)
    _assert(any(l == 'P41_concat_to_join' for _, l in r2),
            "concat → join")

    # 3. fstring_concat → format_concat
    t3 = OOp('fstring_concat', (OVar('a'), OVar('b'), OVar('c')))
    r3 = apply(t3)
    _assert(any(l == 'P41_fstring_to_format' for _, l in r3),
            "fstring → format")

    # 4. format_concat → fstring_concat
    t4 = OOp('format_concat', (OVar('a'), OVar('b'), OVar('c')))
    r4 = apply(t4)
    _assert(any(l == 'P41_format_to_fstring' for _, l in r4),
            "format → fstring")

    # 5. fstring_concat → percent_format
    _assert(any(l == 'P41_fstring_to_percent' for _, l in r3),
            "fstring → percent")

    # 6. percent_format → fstring_concat
    t6 = OOp('percent_format', (OVar('a'), OVar('b')))
    r6 = apply(t6)
    _assert(any(l == 'P41_percent_to_fstring' for _, l in r6),
            "percent → fstring")

    # 7. stringio_build → list_join_build
    t7 = OOp('stringio_build', (OVar('ops'),))
    r7 = apply(t7)
    _assert(any(l == 'P41_stringio_to_list_join' for _, l in r7),
            "stringio → list_join")

    # 8. list_join_build → stringio_build
    t8 = OOp('list_join_build', (OVar('ops'),))
    r8 = apply(t8)
    _assert(any(l == 'P41_list_join_to_stringio' for _, l in r8),
            "list_join → stringio")

    # 9. str_translate → chain_replace
    t9 = OOp('str_translate', (OVar('s'), OVar('table')))
    r9 = apply(t9)
    _assert(any(l == 'P41_translate_to_replace' for _, l in r9),
            "translate → replace")

    # 10. chain_replace → str_translate
    t10 = OOp('chain_replace', (OVar('s'), OVar('repls')))
    r10 = apply(t10)
    _assert(any(l == 'P41_replace_to_translate' for _, l in r10),
            "replace → translate")

    # 11. re_sub_multi → multi_replace
    t11 = OOp('re_sub_multi', (OVar('pat'), OVar('s')))
    r11 = apply(t11)
    _assert(any(l == 'P41_re_sub_to_multi_replace' for _, l in r11),
            "re_sub → multi_replace")

    # 12. multi_replace → re_sub_multi
    t12 = OOp('multi_replace', (OVar('s'), OVar('pairs')))
    r12 = apply(t12)
    _assert(any(l == 'P41_multi_replace_to_re_sub' for _, l in r12),
            "multi_replace → re_sub")

    # 13. str_join_sep → str_concat_sep
    t13 = OOp('str_join_sep', (OVar('sep'), OVar('parts')))
    r13 = apply(t13)
    _assert(any(l == 'P41_join_sep_to_concat_sep' for _, l in r13),
            "join_sep → concat_sep")

    # 14. str_concat_sep → str_join_sep
    t14 = OOp('str_concat_sep', (OVar('sep'), OVar('parts')))
    r14 = apply(t14)
    _assert(any(l == 'P41_concat_sep_to_join_sep' for _, l in r14),
            "concat_sep → join_sep")

    # 15. str_join_map → str_concat_map
    t15 = OOp('str_join_map', (OVar('sep'), OVar('f'), OVar('xs')))
    r15 = apply(t15)
    _assert(any(l == 'P41_join_map_to_concat_map' for _, l in r15),
            "join_map → concat_map")

    # 16. str_concat_map → str_join_map
    t16 = OOp('str_concat_map', (OVar('sep'), OVar('f'), OVar('xs')))
    r16 = apply(t16)
    _assert(any(l == 'P41_concat_map_to_join_map' for _, l in r16),
            "concat_map → join_map")

    # 17. str_builder_append → list_join_build
    t17 = OOp('str_builder_append', (OVar('ops'),))
    r17 = apply(t17)
    _assert(any(l == 'P41_builder_to_list_join' for _, l in r17),
            "builder → list_join")

    # 18. fstring_concat → str_concat (+ operator)
    _assert(any(l == 'P41_fstring_to_plus' for _, l in r3),
            "fstring → plus")

    # 19. str_join → OFold form
    _assert(any(l == 'P41_join_to_fold' for _, l in r),
            "join → fold")

    # 20. str_join_map → str_join_sep(sep, map(…))
    _assert(any(l == 'P41_join_map_to_join_mapped' for _, l in r15),
            "join_map → join(mapped)")

    # 21. str_join with literal parts → single string
    t21 = OOp('str_join', (OSeq((OLit("hello"), OLit(" "), OLit("world"))),))
    r21 = apply(t21)
    _assert(any(l == 'P41_join_literal_to_str' for _, l in r21),
            "join literal → str")
    lit_results = [(t, l) for t, l in r21 if l == 'P41_join_literal_to_str']
    if lit_results:
        _assert(isinstance(lit_results[0][0], OLit)
                and lit_results[0][0].value == "hello world",
                "join literal value correct")
    else:
        _assert(False, "join literal value correct")

    # 22. str_join_sep with literal parts → single string
    t22 = OOp('str_join_sep', (OLit(", "), OSeq((
        OLit("a"), OLit("b"), OLit("c"))),))
    r22 = apply(t22)
    _assert(any(l == 'P41_join_sep_literal_to_str' for _, l in r22),
            "join_sep literal → str")
    sep_results = [(t, l) for t, l in r22
                   if l == 'P41_join_sep_literal_to_str']
    if sep_results:
        _assert(isinstance(sep_results[0][0], OLit)
                and sep_results[0][0].value == "a, b, c",
                "join_sep literal value correct")
    else:
        _assert(False, "join_sep literal value correct")

    # 23. format_concat → percent_format
    _assert(any(l == 'P41_format_to_percent' for _, l in r4),
            "format → percent")

    # 24. inverse: concat → join
    r24_inv = apply_inverse(OOp('str_concat', (OVar('parts'),)))
    _assert(any(l == 'P41_concat_to_join' for _, l in r24_inv),
            "inv: concat → join")

    # 25. inverse: format → fstring
    r25_inv = apply_inverse(OOp('format_concat', (OVar('a'), OVar('b'))))
    _assert(any(l == 'P41_format_to_fstring' for _, l in r25_inv),
            "inv: format → fstring")

    # 26. inverse: replace → translate
    r26_inv = apply_inverse(OOp('chain_replace', (OVar('s'), OVar('r'))))
    _assert(any(l == 'P41_replace_to_translate' for _, l in r26_inv),
            "inv: replace → translate")

    # 27. recognizes string build ops
    _assert(recognizes(OOp('str_join', (OVar('p'),))),
            "recognizes str_join")
    _assert(recognizes(OOp('fstring_concat', (OVar('a'), OVar('b')))),
            "recognizes fstring_concat")
    _assert(recognizes(OOp('str_translate', (OVar('s'), OVar('t')))),
            "recognizes str_translate")
    _assert(not recognizes(OLit(42)), "!recognizes literal")
    _assert(not recognizes(OVar('x')), "!recognizes var")

    # 28. relevance: join ↔ concat high
    _assert(relevance_score(
        OOp('str_join', (OVar('p'),)),
        OOp('str_concat', (OVar('p'),)),
    ) > 0.7, "join/concat relevance high")

    # 29. relevance: fstring ↔ format high
    _assert(relevance_score(
        OOp('fstring_concat', (OVar('a'), OVar('b'))),
        OOp('format_concat', (OVar('a'), OVar('b'))),
    ) > 0.7, "fstring/format relevance high")

    # 30. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2,
            "unrelated relevance low")

    print(f"P41 string_build: {_pass} passed, {_fail} failed")
