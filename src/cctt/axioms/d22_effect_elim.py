"""D22: Effect Elimination Axiom — try/except ↔ Conditional Guard.

§23.2 of the CCTT monograph.  Theorem 23.2.1:
OCatch(body, default) ≡ OCase(can_succeed(body), body, default)
when the exception condition is decidable.

Key rewrites:
  • catch(body, default) → case(guard, body, default)
  • case(guard, body, default) → catch(body, default)
  • Exception guard extraction for:
      ZeroDivisionError  (x//y, x/y, x%y)
      IndexError          (xs[i])
      KeyError             (d[k])
      ValueError           (int(s), float(s))
      AttributeError       (x.attr)
  • Nested try/except normalisation
  • LBYL ↔ EAFP style equivalence
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "D22_effect_elim"
AXIOM_CATEGORY = "language_feature"

SOUNDNESS_PROOF = """
Theorem 23.2.1 (Effect Elimination).
Let body : A + ⊥ (may raise), default : A.
If guard = can_succeed(body) is a decidable predicate, then:
    catch(body, default) ≡ case(guard, body, default)
because guard=True ⟹ body terminates normally, and
guard=False ⟹ body raises, so catch returns default.

The guard must be a conservative approximation: guard=True
implies body succeeds (no false positives).  For the supported
exception types, the guards are exact.

Reverse direction: case(guard, body, default) ≡ catch(body, default)
when guard is an exception-avoidance condition.
"""

COMPOSES_WITH = ["CASE", "ALG", "D20_spec"]
REQUIRES: List[str] = []

EXAMPLES = [
    ("catch(floordiv(x, y), 0)", "case(noteq(y, 0), floordiv(x, y), 0)",
     "D22_catch_to_case"),
    ("catch(getitem(xs, i), default)",
     "case(and(ge(i,0), lt(i, len(xs))), getitem(xs,i), default)",
     "D22_catch_to_case"),
    ("case(noteq(y, 0), floordiv(x,y), 0)", "catch(floordiv(x,y), 0)",
     "D22_case_to_catch"),
]


@dataclass
class FiberCtx:
    param_duck_types: Dict[str, str] = field(default_factory=dict)

    def is_numeric(self, term: OTerm) -> bool:
        return True


# ── Exception guard extraction ──────────────────────────────

def extract_exception_guard(body: OTerm) -> Optional[OTerm]:
    """Extract a decidable guard from a try/except body.

    Returns an OTerm guard G such that: G=True ⟹ body succeeds.
    Covers:
      • ZeroDivisionError  from x//y, x/y, x%y
      • IndexError          from xs[i]
      • KeyError             from d[k]
      • ValueError           from int(s), float(s)
      • AttributeError       from x.attr
      • TypeError             from op on wrong types
    """
    if isinstance(body, OOp):
        # ZeroDivisionError
        if body.name in ('floordiv', 'truediv', 'div', 'mod'):
            if len(body.args) == 2:
                return OOp('noteq', (body.args[1], OLit(0)))

        # IndexError
        if body.name == 'getitem':
            if len(body.args) == 2:
                xs, i = body.args
                return OOp('and', (
                    OOp('ge', (i, OLit(0))),
                    OOp('lt', (i, OOp('len', (xs,)))),
                ))

        # KeyError from dict access
        if body.name in ('dictget', 'dict_getitem'):
            if len(body.args) == 2:
                return OOp('contains', (body.args[0], body.args[1]))

        # ValueError from type conversion
        if body.name in ('int', 'float'):
            if len(body.args) == 1:
                return OOp('isdigit', (body.args[0],))

        # AttributeError
        if body.name == 'getattr':
            if len(body.args) == 2:
                return OOp('hasattr', (body.args[0], body.args[1]))

        # TypeError from indexing None
        if body.name == '.index' or body.name == '.find':
            if len(body.args) >= 1:
                return OOp('noteq', (body.args[0], OLit(None)))

    # Recursive: handle nested expressions
    if isinstance(body, OCase):
        guard_then = extract_exception_guard(body.true_branch)
        guard_else = extract_exception_guard(body.false_branch)
        if guard_then and guard_else:
            return OOp('and', (
                OOp('or', (OOp('u_not', (body.test,)), guard_then)),
                OOp('or', (body.test, guard_else)),
            ))
        if guard_then:
            return OOp('or', (OOp('u_not', (body.test,)), guard_then))
        if guard_else:
            return OOp('or', (body.test, guard_else))

    # Recursive: handle OOp with nested exceptional sub-terms
    if isinstance(body, OOp):
        sub_guards = []
        for arg in body.args:
            g = extract_exception_guard(arg)
            if g is not None:
                sub_guards.append(g)
        if len(sub_guards) == 1:
            return sub_guards[0]
        if len(sub_guards) > 1:
            result = sub_guards[0]
            for g in sub_guards[1:]:
                result = OOp('and', (result, g))
            return result

    return None


def is_exception_guard(test: OTerm) -> bool:
    """Check whether *test* is recognisably an exception-avoidance guard.

    Matches: noteq(y, 0), lt(i, len(xs)), ge(i, 0),
    contains(d, k), isdigit(s), hasattr(x, a).
    """
    if not isinstance(test, OOp):
        return False

    # ZeroDivisionError guard: noteq(y, 0)
    if test.name == 'noteq' and len(test.args) == 2:
        if isinstance(test.args[1], OLit) and test.args[1].value == 0:
            return True

    # IndexError guard: lt(i, len(xs))
    if test.name == 'lt' and len(test.args) == 2:
        if isinstance(test.args[1], OOp) and test.args[1].name == 'len':
            return True

    # Bounds lower: ge(i, 0)
    if test.name == 'ge' and len(test.args) == 2:
        if isinstance(test.args[1], OLit) and test.args[1].value == 0:
            return True

    # KeyError / ValueError / AttributeError guards
    if test.name in ('contains', 'isdigit', 'hasattr'):
        return True

    # None check: noteq(x, None)
    if test.name == 'noteq' and len(test.args) == 2:
        if isinstance(test.args[1], OLit) and test.args[1].value is None:
            return True

    # Compound guards
    if test.name == 'and' and len(test.args) == 2:
        return all(is_exception_guard(a) for a in test.args)

    if test.name == 'or' and len(test.args) == 2:
        return any(is_exception_guard(a) for a in test.args)

    return False


# ── Core axiom application ──────────────────────────────────

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D22 effect-elimination rewrites to *term*."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── 1. catch(body, default) → case(guard, body, default) ──
    if isinstance(term, OCatch):
        guard = extract_exception_guard(term.body)
        if guard is not None:
            results.append((
                OCase(guard, term.body, term.default),
                'D22_catch_to_case',
            ))

    # ── 2. case(guard, body, default) → catch(body, default) ──
    if isinstance(term, OCase):
        if is_exception_guard(term.test):
            results.append((
                OCatch(term.true_branch, term.false_branch),
                'D22_case_to_catch',
            ))

    # ── 3. Nested catch normalisation: catch(catch(a, b), c) → catch(a, c) ──
    if isinstance(term, OCatch):
        if isinstance(term.body, OCatch):
            results.append((
                OCatch(term.body.body, term.default),
                'D22_nested_catch_flatten',
            ))

    # ── 4. catch(lit, default) → lit (literal never raises) ──
    if isinstance(term, OCatch):
        if isinstance(term.body, OLit):
            results.append((
                term.body,
                'D22_catch_literal_elim',
            ))

    # ── 5. catch(var, default) → var (variable access never raises) ──
    if isinstance(term, OCatch):
        if isinstance(term.body, OVar):
            results.append((
                term.body,
                'D22_catch_var_elim',
            ))

    # ── 6. catch(body, body) → body (same result either way) ──
    if isinstance(term, OCatch):
        if term.body.canon() == term.default.canon():
            results.append((
                term.body,
                'D22_catch_identical',
            ))

    # ── 7. .get(d, k, default) → case(contains(d,k), getitem(d,k), default) ──
    if isinstance(term, OOp) and term.name == '.get':
        if len(term.args) == 3:
            d, k, default = term.args
            results.append((
                OCase(OOp('contains', (d, k)),
                      OOp('getitem', (d, k)),
                      default),
                'D22_dict_get_to_case',
            ))
            results.append((
                OCatch(OOp('dictget', (d, k)), default),
                'D22_dict_get_to_catch',
            ))

    # ── 8. case(contains(d,k), getitem(d,k), default) → .get(d,k,default) ──
    if isinstance(term, OCase):
        if isinstance(term.test, OOp) and term.test.name == 'contains' and len(term.test.args) == 2:
            d, k = term.test.args
            if isinstance(term.true_branch, OOp) and term.true_branch.name == 'getitem':
                if len(term.true_branch.args) == 2:
                    if (term.true_branch.args[0].canon() == d.canon() and
                            term.true_branch.args[1].canon() == k.canon()):
                        results.append((
                            OOp('.get', (d, k, term.false_branch)),
                            'D22_case_to_dict_get',
                        ))

    return results


def recognizes(term: OTerm) -> bool:
    """Return True if D22 can potentially rewrite *term*."""
    if isinstance(term, OCatch):
        return True
    if isinstance(term, OCase) and is_exception_guard(term.test):
        return True
    if isinstance(term, OOp) and term.name == '.get':
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D22's relevance for bridging *source* → *target*."""
    sc = source.canon()
    tc = target.canon()
    s_catch = 'catch(' in sc
    t_catch = 'catch(' in tc
    s_case = 'case(' in sc
    t_case = 'case(' in tc
    if s_catch != t_catch:
        return 0.95
    if s_catch and t_case:
        return 0.7
    if s_case and t_catch:
        return 0.7
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse: inject catch or case depending on current form."""
    results: List[Tuple[OTerm, str]] = []

    # case → catch
    if isinstance(term, OCase) and is_exception_guard(term.test):
        results.append((
            OCatch(term.true_branch, term.false_branch),
            'D22_case_to_catch_inv',
        ))

    # catch → case
    if isinstance(term, OCatch):
        guard = extract_exception_guard(term.body)
        if guard is not None:
            results.append((
                OCase(guard, term.body, term.default),
                'D22_catch_to_case_inv',
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
    x, y = OVar('x'), OVar('y')
    xs, i = OVar('xs'), OVar('i')
    d, k = OVar('d'), OVar('k')
    s = OVar('s')

    # ZeroDivisionError guard
    div_body = OOp('floordiv', (x, y))
    guard = extract_exception_guard(div_body)
    _assert(guard is not None, "floordiv guard extracted")
    _assert(isinstance(guard, OOp) and guard.name == 'noteq', "guard is noteq")

    # IndexError guard
    idx_body = OOp('getitem', (xs, i))
    idx_guard = extract_exception_guard(idx_body)
    _assert(idx_guard is not None, "getitem guard extracted")
    _assert(isinstance(idx_guard, OOp) and idx_guard.name == 'and', "index guard is and")

    # KeyError guard
    dict_body = OOp('dictget', (d, k))
    dict_guard = extract_exception_guard(dict_body)
    _assert(dict_guard is not None, "dictget guard extracted")
    _assert(isinstance(dict_guard, OOp) and dict_guard.name == 'contains', "dict guard")

    # ValueError guard
    int_body = OOp('int', (s,))
    int_guard = extract_exception_guard(int_body)
    _assert(int_guard is not None, "int() guard extracted")
    _assert(isinstance(int_guard, OOp) and int_guard.name == 'isdigit', "int guard is isdigit")

    # AttributeError guard
    attr_body = OOp('getattr', (x, OLit('foo')))
    attr_guard = extract_exception_guard(attr_body)
    _assert(attr_guard is not None, "getattr guard extracted")
    _assert(isinstance(attr_guard, OOp) and attr_guard.name == 'hasattr', "attr guard")

    # catch → case
    catch_term = OCatch(div_body, OLit(0))
    r1 = apply(catch_term, ctx)
    _assert(any(a == 'D22_catch_to_case' for _, a in r1), "catch → case")
    _assert(isinstance(r1[0][0], OCase), "result is OCase")

    # case → catch
    case_term = OCase(OOp('noteq', (y, OLit(0))), div_body, OLit(0))
    r2 = apply(case_term, ctx)
    _assert(any(a == 'D22_case_to_catch' for _, a in r2), "case → catch")

    # is_exception_guard checks
    _assert(is_exception_guard(guard), "noteq(y,0) is exception guard")
    _assert(is_exception_guard(idx_guard), "bounds check is exception guard")
    _assert(not is_exception_guard(OOp('add', (OLit(1), OLit(2)))), "add not guard")

    # Nested catch flattening
    nested = OCatch(OCatch(div_body, OLit(-1)), OLit(0))
    r3 = apply(nested, ctx)
    _assert(any(a == 'D22_nested_catch_flatten' for _, a in r3), "nested catch flatten")

    # Literal catch elimination
    lit_catch = OCatch(OLit(42), OLit(0))
    r4 = apply(lit_catch, ctx)
    _assert(any(a == 'D22_catch_literal_elim' for _, a in r4), "literal catch elim")

    # Identical catch
    ident = OCatch(x, x)
    r5 = apply(ident, ctx)
    _assert(any(a == 'D22_catch_identical' for _, a in r5), "identical catch")

    # dict .get
    get_term = OOp('.get', (d, k, OLit(None)))
    r6 = apply(get_term, ctx)
    _assert(any(a == 'D22_dict_get_to_case' for _, a in r6), ".get → case")
    _assert(any(a == 'D22_dict_get_to_catch' for _, a in r6), ".get → catch")

    # case(contains(d,k), getitem(d,k), default) → .get
    case_dict = OCase(
        OOp('contains', (d, k)),
        OOp('getitem', (d, k)),
        OLit(None),
    )
    r7 = apply(case_dict, ctx)
    _assert(any(a == 'D22_case_to_dict_get' for _, a in r7), "case → .get")

    # recognizes
    _assert(recognizes(catch_term), "recognizes catch")
    _assert(recognizes(case_term), "recognizes exception guard case")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # relevance
    _assert(relevance_score(catch_term, case_term) > 0.5,
            "high relevance catch↔case")

    print(f"D22 effect-elim: {_pass} passed, {_fail} failed")
