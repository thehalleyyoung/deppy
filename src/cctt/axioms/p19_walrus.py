"""P19 Axiom: Walrus / Assignment Expression Equivalences.

Establishes equivalences between Python walrus operator (:=)
patterns and their multi-statement counterparts.

Mathematical basis: The walrus operator is a let-binding
in expression position:
    (x := e) ≡ let x = e in x
This is the monadic bind in the state monad — it evaluates e,
binds the result to x, and returns the value.  The key benefit
is avoiding re-computation: f(x) computed once vs. twice.

Key rewrites:
  • if (m := re.match(pat, s)):     ↔  m = re.match(pat, s); if m:
  • while (line := f.readline()):   ↔  for line in f:
  • [y for x in xs if (y := f(x)) > 0]  ↔  [f(x) for x in xs if f(x) > 0]
  • any((result := f(x)) for x in xs)   (capture pattern)

(§P19, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P19_walrus"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["D2_beta", "D24_eta", "P13_bool_idioms"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P19 Walrus / Assignment Expression Equivalence).

The walrus operator := is a let-binding in expression position:

1. if (x := expr): body ≡ x = expr; if x: body
   The walrus operator evaluates expr, binds to x, and the
   result is used as the test condition.  Equivalent to
   sequential assignment + test.

2. while (line := f.readline()): body
   ≡ for line in f: body
   readline() returns '' at EOF (falsy), so the while loop
   with walrus is equivalent to iterating over the file.

3. [y for x in xs if (y := f(x)) > 0]
   ≡ [f(x) for x in xs if f(x) > 0]  (but f(x) computed twice)
   The walrus version computes f(x) once and uses the result
   both for the filter and the mapping.  The non-walrus version
   computes f(x) twice.  The walrus is more efficient but
   semantically equivalent when f is pure.

4. any((result := f(x)) for x in xs)
   Captures the first truthy f(x) in result.  This is the
   monadic bind: do { result <- f(x); guard (truthy result) }
"""

EXAMPLES = [
    ("let_case($x, $e, $body)", "seq(assign($x,$e), case($x, $body, None))",
     "P19_walrus_if"),
    ("let_while($x, $e, $body)", "for_iter($x, iter_source($e), $body)",
     "P19_walrus_while"),
    ("filter_map_let($f, $xs)", "filter_map_double($f, $xs)",
     "P19_walrus_comp"),
]


def _is_let_case(term: OTerm) -> Optional[Tuple[str, OTerm, OTerm]]:
    """Detect let_case(x, expr, body) — walrus in if."""
    if isinstance(term, OOp) and term.name == 'let_case' and len(term.args) == 3:
        x_term, expr, body = term.args
        if isinstance(x_term, OVar):
            return (x_term.name, expr, body)
    return None


def _is_let_while(term: OTerm) -> Optional[Tuple[str, OTerm, OTerm]]:
    """Detect let_while(x, expr, body) — walrus in while."""
    if isinstance(term, OOp) and term.name == 'let_while' and len(term.args) == 3:
        x_term, expr, body = term.args
        if isinstance(x_term, OVar):
            return (x_term.name, expr, body)
    return None


def _is_seq_assign_case(term: OTerm) -> Optional[Tuple[str, OTerm, OTerm]]:
    """Detect seq(assign(x, expr), case(x, body, ...))."""
    if isinstance(term, OOp) and term.name == 'seq' and len(term.args) == 2:
        assign, case = term.args
        if (isinstance(assign, OOp) and assign.name == 'assign'
                and len(assign.args) == 2):
            x_term, expr = assign.args
            if isinstance(x_term, OVar) and isinstance(case, OCase):
                if (isinstance(case.test, OVar)
                        and case.test.name == x_term.name):
                    return (x_term.name, expr, case.true_branch)
    return None


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P19: Walrus / assignment expression rewrites.

    Handles:
      1. let_case(x, expr, body) → seq(assign(x,expr), case(x,body,None))
      2. seq(assign(x,expr), case(x,body,None)) → let_case(x, expr, body)
      3. let_while(x, expr, body) → for_iter(x, source, body)
      4. filter_map_let(f, xs) → filter_map_double(f, xs)
      5. any_capture(f, xs, var) → any(map(f, xs)) + side effect
      6. let_bind(x, e, body) → beta_subst(body, x, e)
      7. walrus_or(x, e, default) → assign_or(x, e, default)
    """
    results: List[Tuple[OTerm, str]] = []

    # ── 1. let_case → seq(assign, case) ──
    lc = _is_let_case(term)
    if lc is not None:
        x, expr, body = lc
        results.append((
            OOp('seq', (
                OOp('assign', (OVar(x), expr)),
                OCase(OVar(x), body, OLit(None)),
            )),
            'P19_walrus_if_to_seq',
        ))

    # ── 2. seq(assign(x,e), case(x,...)) → let_case ──
    sac = _is_seq_assign_case(term)
    if sac is not None:
        x, expr, body = sac
        results.append((
            OOp('let_case', (OVar(x), expr, body)),
            'P19_seq_to_walrus_if',
        ))

    # ── 3. let_while → for_iter ──
    lw = _is_let_while(term)
    if lw is not None:
        x, expr, body = lw
        results.append((
            OOp('for_iter', (OVar(x), OOp('iter_source', (expr,)), body)),
            'P19_walrus_while_to_for',
        ))

    # ── 3b. for_iter(x, iter_source(readline), body) → let_while ──
    if isinstance(term, OOp) and term.name == 'for_iter' and len(term.args) == 3:
        x_term, source, body = term.args
        if (isinstance(source, OOp) and source.name == 'iter_source'
                and isinstance(x_term, OVar)):
            results.append((
                OOp('let_while', (x_term, source.args[0], body)),
                'P19_for_to_walrus_while',
            ))

    # ── 4. filter_map_let(f, xs) ↔ filter_map_double(f, xs) ──
    if isinstance(term, OOp) and term.name == 'filter_map_let' and len(term.args) == 2:
        f, xs = term.args
        results.append((
            OOp('filter_map_double', (f, xs)),
            'P19_walrus_comp_to_double',
        ))

    if isinstance(term, OOp) and term.name == 'filter_map_double' and len(term.args) == 2:
        f, xs = term.args
        results.append((
            OOp('filter_map_let', (f, xs)),
            'P19_double_to_walrus_comp',
        ))

    # ── 5. any_capture(f, xs) — capture first truthy ──
    if isinstance(term, OOp) and term.name == 'any_capture' and len(term.args) == 2:
        f, xs = term.args
        results.append((
            OOp('any', (OMap(f, xs),)),
            'P19_any_capture_to_any',
        ))

    # ── 6. let_bind(x, e, body) → inline/beta ──
    if isinstance(term, OOp) and term.name == 'let_bind' and len(term.args) == 3:
        x_term, e, body = term.args
        if isinstance(x_term, OVar):
            # Model as lambda application: (λx. body)(e)
            results.append((
                OOp('__call__', (OLam((x_term.name,), body), e)),
                'P19_let_to_beta',
            ))

    # ── 7. walrus_or(x, e, default) → case(assign(x,e), x, default) ──
    if isinstance(term, OOp) and term.name == 'walrus_or' and len(term.args) == 3:
        x_term, e, default = term.args
        if isinstance(x_term, OVar):
            results.append((
                OOp('or', (OOp('assign', (x_term, e)), default)),
                'P19_walrus_or_to_or_assign',
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Recognizer & scoring
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    if isinstance(term, OOp):
        if term.name in ('let_case', 'let_while', 'let_bind', 'walrus_or',
                         'filter_map_let', 'filter_map_double', 'any_capture'):
            return True
    sac = _is_seq_assign_case(term)
    if sac is not None:
        return True
    if isinstance(term, OOp) and term.name == 'for_iter' and len(term.args) == 3:
        _, src, _ = term.args
        if isinstance(src, OOp) and src.name == 'iter_source':
            return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    sc, tc = source.canon(), target.canon()
    for kw in ('let_case', 'let_while', 'walrus', 'let_bind', 'assign'):
        if kw in sc or kw in tc:
            return 0.7
    if 'filter_map' in sc and 'filter_map' in tc:
        return 0.8
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse: introduce walrus patterns."""
    results: List[Tuple[OTerm, str]] = []

    # any(map(f, xs)) → any_capture(f, xs)
    if isinstance(term, OOp) and term.name == 'any' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OMap):
            results.append((
                OOp('any_capture', (inner.transform, inner.collection)),
                'P19_inv_any_to_capture',
            ))

    # beta application → let_bind
    if isinstance(term, OOp) and term.name == '__call__' and len(term.args) == 2:
        fn, arg = term.args
        if isinstance(fn, OLam) and len(fn.params) == 1:
            results.append((
                OOp('let_bind', (OVar(fn.params[0]), arg, fn.body)),
                'P19_inv_beta_to_let',
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

    # 1. let_case → seq(assign, case)
    t1 = OOp('let_case', (OVar('m'), OOp('match', (OVar('pat'), OVar('s'))), OVar('body')))
    r1 = apply(t1)
    _assert(any(a == 'P19_walrus_if_to_seq' for _, a in r1), "walrus if → seq")

    # 2. seq(assign, case) → let_case
    t2 = OOp('seq', (
        OOp('assign', (OVar('m'), OOp('match', ()))),
        OCase(OVar('m'), OVar('body'), OLit(None)),
    ))
    r2 = apply(t2)
    _assert(any(a == 'P19_seq_to_walrus_if' for _, a in r2), "seq → walrus if")

    # 3. let_while → for_iter
    t3 = OOp('let_while', (OVar('line'), OOp('readline', ()), OVar('body')))
    r3 = apply(t3)
    _assert(any(a == 'P19_walrus_while_to_for' for _, a in r3), "walrus while → for")

    # 4. for_iter with iter_source → let_while
    t4 = OOp('for_iter', (OVar('line'), OOp('iter_source', (OOp('readline', ()),)), OVar('body')))
    r4 = apply(t4)
    _assert(any(a == 'P19_for_to_walrus_while' for _, a in r4), "for → walrus while")

    # 5. filter_map_let → double
    t5 = OOp('filter_map_let', (OVar('f'), OVar('xs')))
    r5 = apply(t5)
    _assert(any(a == 'P19_walrus_comp_to_double' for _, a in r5), "walrus comp → double")

    # 6. filter_map_double → let
    t6 = OOp('filter_map_double', (OVar('f'), OVar('xs')))
    r6 = apply(t6)
    _assert(any(a == 'P19_double_to_walrus_comp' for _, a in r6), "double → walrus comp")

    # 7. any_capture → any
    t7 = OOp('any_capture', (OVar('f'), OVar('xs')))
    r7 = apply(t7)
    _assert(any(a == 'P19_any_capture_to_any' for _, a in r7), "any_capture → any")

    # 8. let_bind → beta
    t8 = OOp('let_bind', (OVar('x'), OLit(42), OOp('f', (OVar('x'),))))
    r8 = apply(t8)
    _assert(any(a == 'P19_let_to_beta' for _, a in r8), "let_bind → beta")

    # 9. walrus_or → or(assign, default)
    t9 = OOp('walrus_or', (OVar('x'), OOp('get', ()), OLit(0)))
    r9 = apply(t9)
    _assert(any(a == 'P19_walrus_or_to_or_assign' for _, a in r9), "walrus_or → or")

    # 10. recognizes
    _assert(recognizes(t1), "recognizes let_case")
    _assert(recognizes(t5), "recognizes filter_map_let")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # 11. inverse: any → any_capture
    t11 = OOp('any', (OMap(OVar('f'), OVar('xs')),))
    r11 = apply_inverse(t11)
    _assert(any(a == 'P19_inv_any_to_capture' for _, a in r11), "inv any → capture")

    # 12. inverse: beta → let_bind
    t12 = OOp('__call__', (OLam(('x',), OOp('f', (OVar('x'),))), OLit(42)))
    r12 = apply_inverse(t12)
    _assert(any(a == 'P19_inv_beta_to_let' for _, a in r12), "inv beta → let")

    # 13. relevance
    _assert(relevance_score(t1, t2) > 0.5, "walrus relevance")

    print(f"P19 walrus: {_pass} passed, {_fail} failed")
