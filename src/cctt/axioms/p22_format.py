"""P22 Axiom: Print / Format / Logging Equivalences.

Establishes equivalences between Python string formatting and
output patterns.

Mathematical basis: String formatting is a morphism in the
free monoid of characters:
    format : T × FmtSpec → String
Different formatting approaches (f-string, .format(), % operator)
are all implementations of the same morphism.

Output patterns (print, sys.stdout.write, logging) are effects
in the IO fiber.  They produce the same output string but
differ in side-effect semantics (buffering, newlines, levels).

Key rewrites:
  • print(f"{a} {b}")  ↔  print(a, b)  ↔  sys.stdout.write(f"{a} {b}\\n")
  • ", ".join(str(x) for x in xs)  ↔  ", ".join(map(str, xs))
  • f"{x:.2f}"  ↔  format(x, '.2f')  ↔  "%.2f" % x
  • repr(x)  ↔  f"{x!r}"
  • pprint.pformat(d)  ↔  manual pretty-print

(§P22, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P22_format"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["D24_eta", "P16_type_convert", "D22_effect_elim"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P22 Format/Print Equivalence).

1. print(f"{a} {b}") ≡ print(a, b)
   print() with sep=' ' (default) joins str() of args with spaces
   and adds a newline.  f"{a} {b}" produces the same string
   (assuming default str() conversion).

2. ", ".join(str(x) for x in xs) ≡ ", ".join(map(str, xs))
   Generator expression vs map: both produce an iterator of
   str(x) for each x in xs.  join() consumes the iterator.

3. f"{x:.2f}" ≡ format(x, '.2f') ≡ "%.2f" % x
   All three produce the same formatted string.
   f-string calls format(x, '.2f') under the hood.
   %-formatting is the legacy equivalent.

4. repr(x) ≡ f"{x!r}"
   The !r conversion flag in f-strings calls repr().

5. sys.stdout.write(s + '\n') ≡ print(s)
   print() calls sys.stdout.write with the string followed
   by end='\n' (default).
"""

EXAMPLES = [
    ("effect_io(fstring($a, ' ', $b))", "effect_io($a, $b)", "P22_fstring_to_print"),
    ("join(', ', map(str, $xs))", "join(', ', map(str, $xs))", "P22_join_map"),
    ("fstring_fmt($x, '.2f')", "format($x, '.2f')", "P22_fstring_to_format"),
    ("fstring_repr($x)", "repr($x)", "P22_fstring_repr"),
]

# Format/print operation names
_FORMAT_OPS = frozenset({
    'effect_io', 'print', 'stdout_write',
    'fstring', 'format', 'percent_fmt',
    'repr', 'str', 'join',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P22: Print/format/logging rewrites.

    Handles:
      1. effect_io(fstring(a,' ',b)) → effect_io(a, b)  (f-string to print args)
      2. join(sep, map(str, xs)) ↔ join(sep, comp(str, xs))
      3. fstring_fmt(x, spec) → format(x, spec)
      4. format(x, spec) → percent_fmt(spec, x)
      5. fstring_repr(x) → repr(x)
      6. effect_io(x) → stdout_write(add(str(x), '\n'))
      7. stdout_write(add(s, '\n')) → effect_io(s)
      8. repr(x) → fstring_repr(x)
      9. join(sep, map(str, xs)) ↔ join(sep, genexpr(str, xs))
    """
    results: List[Tuple[OTerm, str]] = []

    # ── 1. effect_io(fstring(a, ' ', b)) → effect_io(a, b) ──
    if isinstance(term, OOp) and term.name == 'effect_io' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'fstring':
            # Check for simple space-separated pattern
            parts = inner.args
            non_space = [p for p in parts if not (isinstance(p, OLit) and p.value == ' ')]
            if len(non_space) >= 2:
                results.append((
                    OOp('effect_io', tuple(non_space)),
                    'P22_fstring_to_print_args',
                ))

        # ── 6. effect_io(x) → stdout_write(str(x) + '\n') ──
        results.append((
            OOp('stdout_write', (OOp('add', (OOp('str', (inner,)), OLit('\n'))),)),
            'P22_print_to_stdout_write',
        ))

    # ── 7. stdout_write(add(s, '\n')) → effect_io(s) ──
    if isinstance(term, OOp) and term.name == 'stdout_write' and len(term.args) == 1:
        inner = term.args[0]
        if (isinstance(inner, OOp) and inner.name == 'add'
                and len(inner.args) == 2
                and isinstance(inner.args[1], OLit)
                and inner.args[1].value == '\n'):
            results.append((
                OOp('effect_io', (inner.args[0],)),
                'P22_stdout_write_to_print',
            ))

    # ── 2. join(sep, map(str, xs)) ↔ join(sep, comp) ──
    if isinstance(term, OOp) and term.name == 'join' and len(term.args) == 2:
        sep, source = term.args
        if isinstance(source, OOp) and source.name == 'map' and len(source.args) == 2:
            fn, xs = source.args
            results.append((
                OOp('join', (sep, OMap(fn, xs))),
                'P22_join_map_to_comp',
            ))
        if isinstance(source, OMap) and source.filter_pred is None:
            results.append((
                OOp('join', (sep, OOp('map', (source.transform, source.collection)))),
                'P22_join_comp_to_map',
            ))

    # ── 3. fstring_fmt(x, spec) → format(x, spec) ──
    if isinstance(term, OOp) and term.name == 'fstring_fmt' and len(term.args) == 2:
        x, spec = term.args
        results.append((
            OOp('format', (x, spec)),
            'P22_fstring_fmt_to_format',
        ))

    # ── 4. format(x, spec) ↔ percent_fmt(spec, x) ──
    if isinstance(term, OOp) and term.name == 'format' and len(term.args) == 2:
        x, spec = term.args
        results.append((
            OOp('percent_fmt', (spec, x)),
            'P22_format_to_percent',
        ))
        results.append((
            OOp('fstring_fmt', (x, spec)),
            'P22_format_to_fstring',
        ))

    if isinstance(term, OOp) and term.name == 'percent_fmt' and len(term.args) == 2:
        spec, x = term.args
        results.append((
            OOp('format', (x, spec)),
            'P22_percent_to_format',
        ))

    # ── 5. fstring_repr(x) ↔ repr(x) ──
    if isinstance(term, OOp) and term.name == 'fstring_repr' and len(term.args) == 1:
        results.append((
            OOp('repr', term.args),
            'P22_fstring_repr_to_repr',
        ))

    # ── 8. repr(x) → fstring_repr(x) ──
    if isinstance(term, OOp) and term.name == 'repr' and len(term.args) == 1:
        results.append((
            OOp('fstring_repr', term.args),
            'P22_repr_to_fstring_repr',
        ))

    # ── 9. effect_io(a, b, ...) → effect_io(fstring(a, ' ', b, ...)) ──
    if isinstance(term, OOp) and term.name == 'effect_io' and len(term.args) >= 2:
        parts: List[OTerm] = []
        for i, arg in enumerate(term.args):
            if i > 0:
                parts.append(OLit(' '))
            parts.append(arg)
        results.append((
            OOp('effect_io', (OOp('fstring', tuple(parts)),)),
            'P22_print_args_to_fstring',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Recognizer & scoring
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    if isinstance(term, OOp):
        if term.name in _FORMAT_OPS:
            return True
        if term.name in ('fstring_fmt', 'fstring_repr', 'percent_fmt',
                         'stdout_write'):
            return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    sc, tc = source.canon(), target.canon()
    for kw in ('effect_io', 'print', 'stdout', 'fstring', 'format',
               'join', 'repr', 'percent'):
        if kw in sc and kw in tc:
            return 0.8
    if ('effect_io' in sc or 'print' in sc) and ('stdout' in tc or 'write' in tc):
        return 0.7
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse: expand formatting patterns."""
    results: List[Tuple[OTerm, str]] = []

    # format(x, spec) → fstring_fmt(x, spec)
    if isinstance(term, OOp) and term.name == 'format' and len(term.args) == 2:
        results.append((
            OOp('fstring_fmt', term.args),
            'P22_inv_format_to_fstring_fmt',
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

    # 1. effect_io(fstring(a, ' ', b)) → effect_io(a, b)
    t1 = OOp('effect_io', (OOp('fstring', (OVar('a'), OLit(' '), OVar('b'))),))
    r1 = apply(t1)
    _assert(any(a == 'P22_fstring_to_print_args' for _, a in r1), "fstring → print args")

    # 2. print → stdout_write
    t2 = OOp('effect_io', (OVar('x'),))
    r2 = apply(t2)
    _assert(any(a == 'P22_print_to_stdout_write' for _, a in r2), "print → stdout_write")

    # 3. stdout_write(s + '\n') → print
    t3 = OOp('stdout_write', (OOp('add', (OVar('s'), OLit('\n'))),))
    r3 = apply(t3)
    _assert(any(a == 'P22_stdout_write_to_print' for _, a in r3), "stdout_write → print")

    # 4. join(sep, map) → join(sep, comp)
    t4 = OOp('join', (OLit(', '), OOp('map', (OVar('str'), OVar('xs')))))
    r4 = apply(t4)
    _assert(any(a == 'P22_join_map_to_comp' for _, a in r4), "join map → comp")

    # 5. join(sep, comp) → join(sep, map)
    t5 = OOp('join', (OLit(', '), OMap(OVar('str'), OVar('xs'))))
    r5 = apply(t5)
    _assert(any(a == 'P22_join_comp_to_map' for _, a in r5), "join comp → map")

    # 6. fstring_fmt → format
    t6 = OOp('fstring_fmt', (OVar('x'), OLit('.2f')))
    r6 = apply(t6)
    _assert(any(a == 'P22_fstring_fmt_to_format' for _, a in r6), "fstring_fmt → format")

    # 7. format → percent_fmt
    t7 = OOp('format', (OVar('x'), OLit('.2f')))
    r7 = apply(t7)
    _assert(any(a == 'P22_format_to_percent' for _, a in r7), "format → percent")

    # 8. format → fstring_fmt
    _assert(any(a == 'P22_format_to_fstring' for _, a in r7), "format → fstring_fmt")

    # 9. percent_fmt → format
    t9 = OOp('percent_fmt', (OLit('.2f'), OVar('x')))
    r9 = apply(t9)
    _assert(any(a == 'P22_percent_to_format' for _, a in r9), "percent → format")

    # 10. fstring_repr ↔ repr
    t10 = OOp('fstring_repr', (OVar('x'),))
    r10 = apply(t10)
    _assert(any(a == 'P22_fstring_repr_to_repr' for _, a in r10), "fstring_repr → repr")

    t10b = OOp('repr', (OVar('x'),))
    r10b = apply(t10b)
    _assert(any(a == 'P22_repr_to_fstring_repr' for _, a in r10b), "repr → fstring_repr")

    # 11. effect_io(a, b) → effect_io(fstring)
    t11 = OOp('effect_io', (OVar('a'), OVar('b')))
    r11 = apply(t11)
    _assert(any(a == 'P22_print_args_to_fstring' for _, a in r11), "print args → fstring")

    # 12. recognizes
    _assert(recognizes(t1), "recognizes effect_io")
    _assert(recognizes(t6), "recognizes fstring_fmt")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # 13. relevance
    _assert(relevance_score(t1, t2) > 0.5, "print-print relevance")

    # 14. inverse
    r14 = apply_inverse(t7)
    _assert(any(a == 'P22_inv_format_to_fstring_fmt' for _, a in r14), "inv format")

    print(f"P22 format: {_pass} passed, {_fail} failed")
