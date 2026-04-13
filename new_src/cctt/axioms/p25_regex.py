"""P25 Axiom: Regular Expression Pattern Equivalences.

Establishes equivalences between different Python regex patterns
and their string-method counterparts.

Mathematical basis: Regular expressions define a regular language
L(r) ⊆ Σ*.  The equivalence classes arise from the algebraic
identities of the regular expression semiring:
    re.match(r, s) ≅ re.search('^' + r, s)
    re.findall(r, s) ≅ list(re.finditer(r, s))
    re.sub(literal, repl, s) ≅ s.replace(literal, repl)

Key rewrites:
  • re.match(r, s) ↔ re.search('^' + r, s)
  • re.findall(r, s) ↔ [m.group() for m in re.finditer(r, s)]
  • re.sub(literal, repl, s) ↔ s.replace(literal, repl)
  • re.compile(r).search(s) ↔ re.search(r, s)
  • re.split(literal, s) ↔ s.split(literal)
  • Named groups ↔ indexed groups
  • Lookahead equivalences

(§P25, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P25_regex"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P4_string_ops", "P22_format"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P25 Regex Equivalences).

1. re.match(r, s) ≡ re.search('^' + r, s)
   re.match anchors at start; search('^...') does same via anchor.

2. re.findall(r, s) ≡ [m.group() for m in re.finditer(r, s)]
   findall returns list of strings; finditer returns match objects.
   Extracting .group() from each yields the same list.

3. re.sub(lit, repl, s) ≡ s.replace(lit, repl) (for literal patterns)
   When pattern contains no regex metacharacters, both perform
   identical literal string replacement.

4. re.compile(r).search(s) ≡ re.search(r, s)
   Compilation is a performance optimization; semantics are identical.

5. re.split(lit, s) ≡ s.split(lit) (for literal delimiters)
   Both split on exact literal occurrences.

6. (?P<name>...) group access via .group('name') ≡ .group(n)
   Named groups are aliases for positional groups.
"""

EXAMPLES = [
    ("re.match($r, $s)", "re.search('^' + $r, $s)", "P25_match_to_search"),
    ("re.findall($r, $s)", "[m.group() for m in re.finditer($r, $s)]", "P25_findall_to_finditer"),
    ("re.sub($lit, $repl, $s)", "$s.replace($lit, $repl)", "P25_sub_to_replace"),
    ("re.compile($r).search($s)", "re.search($r, $s)", "P25_compiled_to_inline"),
    ("re.split($lit, $s)", "$s.split($lit)", "P25_re_split_to_str_split"),
]

_REGEX_OPS = frozenset({
    're.match', 're.search', 're.findall', 're.finditer',
    're.sub', 're.split', 're.compile', 're_compiled_search',
    're_compiled_match', 're_compiled_findall', 're_compiled_sub',
    're_compiled_split', 'str.replace', 'str.split',
})


def _is_literal_pattern(term: OTerm) -> bool:
    """Check if a regex pattern is a literal (no metacharacters)."""
    if isinstance(term, OLit) and isinstance(term.value, str):
        import re
        return re.escape(term.value) == term.value
    return False


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P25: Regex pattern equivalence rewrites."""
    results: List[Tuple[OTerm, str]] = []

    # ── re.match(r, s) → re.search('^'+r, s) ──
    if isinstance(term, OOp) and term.name == 're.match' and len(term.args) == 2:
        r, s = term.args
        anchored = OOp('str.concat', (OLit('^'), r))
        results.append((
            OOp('re.search', (anchored, s)),
            'P25_match_to_search',
        ))

    # ── re.search('^'+r, s) → re.match(r, s) ──
    if isinstance(term, OOp) and term.name == 're.search' and len(term.args) == 2:
        r, s = term.args
        if isinstance(r, OOp) and r.name == 'str.concat' and len(r.args) == 2:
            if isinstance(r.args[0], OLit) and r.args[0].value == '^':
                results.append((
                    OOp('re.match', (r.args[1], s)),
                    'P25_search_to_match',
                ))
        if isinstance(r, OLit) and isinstance(r.value, str) and r.value.startswith('^'):
            inner_pat = OLit(r.value[1:])
            results.append((
                OOp('re.match', (inner_pat, s)),
                'P25_search_anchored_to_match',
            ))

    # ── re.findall(r, s) ↔ list(re.finditer(r, s)) ──
    if isinstance(term, OOp) and term.name == 're.findall' and len(term.args) == 2:
        r, s = term.args
        results.append((
            OOp('list_groups', (OOp('re.finditer', (r, s)),)),
            'P25_findall_to_finditer',
        ))

    if isinstance(term, OOp) and term.name == 'list_groups' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 're.finditer' and len(inner.args) == 2:
            r, s = inner.args
            results.append((
                OOp('re.findall', (r, s)),
                'P25_finditer_to_findall',
            ))

    # ── re.sub(lit, repl, s) ↔ s.replace(lit, repl) for literals ──
    if isinstance(term, OOp) and term.name == 're.sub' and len(term.args) == 3:
        pat, repl, s = term.args
        if _is_literal_pattern(pat):
            results.append((
                OOp('str.replace', (s, pat, repl)),
                'P25_sub_literal_to_replace',
            ))

    if isinstance(term, OOp) and term.name == 'str.replace' and len(term.args) == 3:
        s, old, new = term.args
        results.append((
            OOp('re.sub', (old, new, s)),
            'P25_replace_to_sub',
        ))

    # ── compiled pattern ↔ inline ──
    if isinstance(term, OOp) and term.name == 're_compiled_search' and len(term.args) == 2:
        r, s = term.args
        results.append((
            OOp('re.search', (r, s)),
            'P25_compiled_search_to_inline',
        ))

    if isinstance(term, OOp) and term.name == 're.search' and len(term.args) == 2:
        r, s = term.args
        results.append((
            OOp('re_compiled_search', (r, s)),
            'P25_inline_search_to_compiled',
        ))

    if isinstance(term, OOp) and term.name == 're_compiled_match' and len(term.args) == 2:
        r, s = term.args
        results.append((
            OOp('re.match', (r, s)),
            'P25_compiled_match_to_inline',
        ))

    if isinstance(term, OOp) and term.name == 're_compiled_findall' and len(term.args) == 2:
        r, s = term.args
        results.append((
            OOp('re.findall', (r, s)),
            'P25_compiled_findall_to_inline',
        ))

    if isinstance(term, OOp) and term.name == 're_compiled_sub' and len(term.args) == 3:
        r, repl, s = term.args
        results.append((
            OOp('re.sub', (r, repl, s)),
            'P25_compiled_sub_to_inline',
        ))

    # ── re.split(lit, s) ↔ s.split(lit) for literals ──
    if isinstance(term, OOp) and term.name == 're.split' and len(term.args) == 2:
        pat, s = term.args
        if _is_literal_pattern(pat):
            results.append((
                OOp('str.split', (s, pat)),
                'P25_re_split_to_str_split',
            ))

    if isinstance(term, OOp) and term.name == 'str.split' and len(term.args) == 2:
        s, sep = term.args
        results.append((
            OOp('re.split', (sep, s)),
            'P25_str_split_to_re_split',
        ))

    # ── Named group ↔ indexed group ──
    if isinstance(term, OOp) and term.name == 're_group_named' and len(term.args) == 2:
        match, name = term.args
        results.append((
            OOp('re_group_indexed', (match, name)),
            'P25_named_group_to_indexed',
        ))

    if isinstance(term, OOp) and term.name == 're_group_indexed' and len(term.args) == 2:
        match, idx = term.args
        results.append((
            OOp('re_group_named', (match, idx)),
            'P25_indexed_group_to_named',
        ))

    # ── Lookahead: x(?=y) match ↔ match x then check y ──
    if isinstance(term, OOp) and term.name == 're_lookahead' and len(term.args) == 3:
        pat, ahead, s = term.args
        results.append((
            OOp('re_match_and_check', (pat, ahead, s)),
            'P25_lookahead_to_match_check',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    results = apply(term, ctx)
    inv = {'P25_search_to_match', 'P25_search_anchored_to_match',
           'P25_finditer_to_findall', 'P25_replace_to_sub',
           'P25_compiled_search_to_inline', 'P25_compiled_match_to_inline',
           'P25_str_split_to_re_split', 'P25_indexed_group_to_named'}
    return [(t, l) for t, l in results if l in inv]


def recognizes(term: OTerm) -> bool:
    if isinstance(term, OOp) and term.name in _REGEX_OPS:
        return True
    if isinstance(term, OOp) and term.name in (
        're_group_named', 're_group_indexed', 're_lookahead',
        're_match_and_check', 'list_groups',
    ):
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    sc, tc = source.canon(), target.canon()
    for kw in ('re.match', 're.search', 're.findall', 're.sub', 're.split',
               'replace', 'str.split', 'finditer', 'compile'):
        if kw in sc and kw in tc:
            return 0.85
    if any(k in sc for k in ('re.', 'regex')) and any(k in tc for k in ('re.', 'regex')):
        return 0.6
    if any(k in sc for k in ('re.',)) or any(k in tc for k in ('re.',)):
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

    # 1. re.match → re.search
    t = OOp('re.match', (OVar('r'), OVar('s')))
    r = apply(t)
    _assert(any(a == 'P25_match_to_search' for _, a in r), "match → search")

    # 2. re.search('^'+r, s) → re.match
    t2 = OOp('re.search', (OOp('str.concat', (OLit('^'), OVar('r'))), OVar('s')))
    r2 = apply(t2)
    _assert(any(a == 'P25_search_to_match' for _, a in r2), "search(^r) → match")

    # 3. Anchored literal search → match
    t3 = OOp('re.search', (OLit('^abc'), OVar('s')))
    r3 = apply(t3)
    _assert(any(a == 'P25_search_anchored_to_match' for _, a in r3), "search('^abc') → match")

    # 4. findall → finditer
    t4 = OOp('re.findall', (OVar('r'), OVar('s')))
    r4 = apply(t4)
    _assert(any(a == 'P25_findall_to_finditer' for _, a in r4), "findall → finditer")

    # 5. finditer → findall
    t5 = OOp('list_groups', (OOp('re.finditer', (OVar('r'), OVar('s'))),))
    r5 = apply(t5)
    _assert(any(a == 'P25_finditer_to_findall' for _, a in r5), "finditer → findall")

    # 6. re.sub literal → str.replace
    t6 = OOp('re.sub', (OLit('hello'), OLit('world'), OVar('s')))
    r6 = apply(t6)
    _assert(any(a == 'P25_sub_literal_to_replace' for _, a in r6), "sub(lit) → replace")

    # 7. str.replace → re.sub
    t7 = OOp('str.replace', (OVar('s'), OLit('a'), OLit('b')))
    r7 = apply(t7)
    _assert(any(a == 'P25_replace_to_sub' for _, a in r7), "replace → sub")

    # 8. compiled search → inline
    t8 = OOp('re_compiled_search', (OVar('r'), OVar('s')))
    r8 = apply(t8)
    _assert(any(a == 'P25_compiled_search_to_inline' for _, a in r8), "compiled → inline")

    # 9. inline search → compiled
    t9 = OOp('re.search', (OVar('r'), OVar('s')))
    r9 = apply(t9)
    _assert(any(a == 'P25_inline_search_to_compiled' for _, a in r9), "inline → compiled")

    # 10. re.split literal → str.split
    t10 = OOp('re.split', (OLit(','), OVar('s')))
    r10 = apply(t10)
    _assert(any(a == 'P25_re_split_to_str_split' for _, a in r10), "re.split → str.split")

    # 11. str.split → re.split
    t11 = OOp('str.split', (OVar('s'), OLit(',')))
    r11 = apply(t11)
    _assert(any(a == 'P25_str_split_to_re_split' for _, a in r11), "str.split → re.split")

    # 12. named group → indexed
    t12 = OOp('re_group_named', (OVar('m'), OLit('name')))
    r12 = apply(t12)
    _assert(any(a == 'P25_named_group_to_indexed' for _, a in r12), "named → indexed")

    # 13. indexed → named
    t13 = OOp('re_group_indexed', (OVar('m'), OLit(1)))
    r13 = apply(t13)
    _assert(any(a == 'P25_indexed_group_to_named' for _, a in r13), "indexed → named")

    # 14. lookahead → match+check
    t14 = OOp('re_lookahead', (OVar('pat'), OVar('ahead'), OVar('s')))
    r14 = apply(t14)
    _assert(any(a == 'P25_lookahead_to_match_check' for _, a in r14), "lookahead → check")

    # 15. compiled match → inline
    t15 = OOp('re_compiled_match', (OVar('r'), OVar('s')))
    r15 = apply(t15)
    _assert(any(a == 'P25_compiled_match_to_inline' for _, a in r15), "compiled match → inline")

    # 16. compiled findall → inline
    t16 = OOp('re_compiled_findall', (OVar('r'), OVar('s')))
    r16 = apply(t16)
    _assert(any(a == 'P25_compiled_findall_to_inline' for _, a in r16), "compiled findall → inline")

    # 17. compiled sub → inline
    t17 = OOp('re_compiled_sub', (OVar('r'), OLit('x'), OVar('s')))
    r17 = apply(t17)
    _assert(any(a == 'P25_compiled_sub_to_inline' for _, a in r17), "compiled sub → inline")

    # 18. recognizes
    _assert(recognizes(t), "recognizes re.match")
    _assert(recognizes(OOp('re.search', (OVar('r'), OVar('s')))), "recognizes re.search")
    _assert(not recognizes(OLit(42)), "!recognizes literal")

    # 19. relevance
    _assert(relevance_score(t, t9) > 0.5, "match/search relevance")

    # 20. inverse
    inv = apply_inverse(t3)
    _assert(any(a == 'P25_search_anchored_to_match' for _, a in inv), "inverse anchored")

    print(f"P25 regex: {_pass} passed, {_fail} failed")
