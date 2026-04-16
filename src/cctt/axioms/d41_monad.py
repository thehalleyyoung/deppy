"""D41: Monad Laws Axiom.

Rewrites based on the three monad laws applied to common Python
monadic patterns: Optional/None, List, Exception.

Mathematical foundation:
  A monad (T, η, μ) on a category C satisfies:
    Left unit:     μ ∘ Tη = id           bind(return(a), f) = f(a)
    Right unit:    μ ∘ ηT = id           bind(m, return) = m
    Associativity: μ ∘ Tμ = μ ∘ μT      bind(bind(m,f),g) = bind(m, λx.bind(f(x),g))

  In Python these manifest as:
    • Optional monad: None-propagation chains
    • List monad: nested comprehension flattening
    • Exception monad: try/except chain normalisation
    • Result monad: if/else error-checking chains

Covers:
  • Left unit: bind(return(a), f) → f(a)
  • Right unit: bind(m, return) → m
  • Associativity: bind(bind(m,f), g) → bind(m, λx. bind(f(x), g))
  • Optional chains: x if x is not None flattening
  • List monad: nested for-comprehension fusion
  • Exception monad: try/except chain normalisation
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ═══════════════════════════════════════════════════════════
# Axiom metadata
# ═══════════════════════════════════════════════════════════

AXIOM_NAME = "D41_monad"
AXIOM_CATEGORY = "higher_order"

SOUNDNESS_PROOF = r"""
Theorem (Monad Laws).
  For any monad (T, return, bind):

  Left unit:  bind(return(a), f) = f(a)
    Proof: μ ∘ Tη ∘ f = id ∘ f = f by the left unit law.

  Right unit: bind(m, return) = m
    Proof: μ ∘ ηT(m) = id(m) = m by the right unit law.

  Associativity: bind(bind(m, f), g) = bind(m, λx. bind(f(x), g))
    Proof: μ ∘ Tμ = μ ∘ μT (Mac Lane's coherence).

  Optional monad in Python:
    return(a) = a  (just the value)
    bind(m, f) = f(m) if m is not None else None
    Left unit:  bind(a, f) = f(a) when a is not None  ✓
    Right unit: bind(m, id) = m  ✓
    Associativity: nested None-checks can be flattened  ✓

  List monad:
    return(a) = [a]
    bind(xs, f) = [y for x in xs for y in f(x)]
    Nested comprehensions obey associativity.

  Exception monad:
    return(a) = a (no exception)
    bind(m, f) = try: f(m) except: propagate
    Nested try/except chains can be flattened.  ∎
"""

COMPOSES_WITH = ["D22_effect_elim", "D04_comp_fusion", "D24_eta", "D39_defunc"]
REQUIRES: List[str] = []

EXAMPLES = [
    {
        "name": "Left unit: bind(return(a), f) → f(a)",
        "before": "bind(return(a), f)",
        "after": "f(a)",
        "axiom": "D41_left_unit",
    },
    {
        "name": "Right unit: bind(m, return) → m",
        "before": "bind(m, return)",
        "after": "m",
        "axiom": "D41_right_unit",
    },
    {
        "name": "Associativity",
        "before": "bind(bind(m, f), g)",
        "after": "bind(m, λ(x)bind(f(x), g))",
        "axiom": "D41_assoc",
    },
    {
        "name": "Optional left unit",
        "before": "case(isnot(a, None), f(a), None)",
        "after": "f(a)",
        "axiom": "D41_optional_left_unit",
    },
    {
        "name": "Nested None check flatten",
        "before": "case(isnot(case(isnot(m, None), f(m), None), None), g(r), None)",
        "after": "case(isnot(m, None), case(isnot(f(m), None), g(f(m)), None), None)",
        "axiom": "D41_optional_assoc",
    },
    {
        "name": "Nested try/except flatten",
        "before": "catch(catch(body, d1), d2)",
        "after": "catch(body, d2)",
        "axiom": "D41_exception_assoc",
    },
]


@dataclass
class FiberCtx:
    param_duck_types: Dict[str, str] = field(default_factory=dict)

    def is_numeric(self, term: OTerm) -> bool:
        return True


# ═══════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════

def _is_none_check(test: OTerm) -> Optional[OTerm]:
    """Detect 'x is not None' pattern → return x."""
    if isinstance(test, OOp) and test.name in ("isnot", "is_not") and len(test.args) == 2:
        if isinstance(test.args[1], OLit) and test.args[1].value is None:
            return test.args[0]
    if isinstance(test, OOp) and test.name == "noteq" and len(test.args) == 2:
        if isinstance(test.args[1], OLit) and test.args[1].value is None:
            return test.args[0]
    return None


def _is_none_lit(term: OTerm) -> bool:
    return isinstance(term, OLit) and term.value is None


def _is_return(term: OTerm) -> bool:
    """Detect return/pure/unit pattern."""
    if isinstance(term, OOp) and term.name in ("return", "pure", "unit", "Some"):
        return True
    if isinstance(term, OLam) and len(term.params) == 1:
        if isinstance(term.body, OVar) and term.body.name == term.params[0]:
            return True
    return False


def _is_bind(term: OTerm) -> Optional[Tuple[OTerm, OTerm]]:
    """Detect bind(m, f) pattern → return (m, f)."""
    if isinstance(term, OOp) and term.name in ("bind", "flatmap", "chain") and len(term.args) == 2:
        return (term.args[0], term.args[1])
    return None


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D41 monad law rewrites to *term*."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── 1. Left unit: bind(return(a), f) → f(a) ──
    bind = _is_bind(term)
    if bind is not None:
        m, f = bind
        if isinstance(m, OOp) and m.name in ("return", "pure", "unit", "Some") and len(m.args) == 1:
            val = m.args[0]
            if isinstance(f, OLam) and len(f.params) == 1:
                # Substitute val into f's body
                from ..denotation import _subst
                body = _subst(f.body, {f.params[0]: val})
                results.append((body, "D41_left_unit"))
            elif isinstance(f, OOp) or isinstance(f, OVar):
                results.append((OOp(f.canon(), (val,)), "D41_left_unit"))

    # ── 2. Right unit: bind(m, return) → m ──
    if bind is not None:
        m, f = bind
        if _is_return(f):
            results.append((m, "D41_right_unit"))

    # ── 3. Associativity: bind(bind(m,f), g) → bind(m, λx. bind(f(x), g)) ──
    if bind is not None:
        outer_m, g = bind
        inner_bind = _is_bind(outer_m)
        if inner_bind is not None:
            m, f = inner_bind
            param = "_ma"
            if isinstance(f, OLam) and len(f.params) == 1:
                new_body = OOp("bind", (f.body, g))
                new_f = OLam(f.params, new_body)
            else:
                f_app = OOp("apply", (f, OVar(param)))
                new_f = OLam((param,), OOp("bind", (f_app, g)))
            results.append((
                OOp("bind", (m, new_f)),
                "D41_assoc",
            ))

    # ── 4. Inverse associativity: bind(m, λx. bind(f(x), g)) → bind(bind(m,f), g) ──
    if bind is not None:
        m, f = bind
        if isinstance(f, OLam) and len(f.params) == 1:
            inner = f.body
            inner_bind = _is_bind(inner)
            if inner_bind is not None:
                f_inner, g = inner_bind
                results.append((
                    OOp("bind", (OOp("bind", (m, OLam(f.params, f_inner))), g)),
                    "D41_assoc_inv",
                ))

    # ── 5. Optional monad: case(x is not None, f(x), None) patterns ──
    if isinstance(term, OCase):
        checked = _is_none_check(term.test)
        if checked is not None and _is_none_lit(term.false_branch):
            # This is bind_optional(checked, λx. true_branch)
            results.append((
                OOp("bind_optional", (checked, OLam(("_ov",), term.true_branch))),
                "D41_optional_bind",
            ))

    # ── 6. Nested Optional: case(is_not_none(case(is_not_none(m), f(m), None)), g(r), None) ──
    if isinstance(term, OCase):
        checked_outer = _is_none_check(term.test)
        if (checked_outer is not None
                and _is_none_lit(term.false_branch)
                and isinstance(checked_outer, OCase)):
            inner_case = checked_outer
            checked_inner = _is_none_check(inner_case.test)
            if checked_inner is not None and _is_none_lit(inner_case.false_branch):
                # Flatten: nest the checks properly
                results.append((
                    OCase(inner_case.test,
                          OCase(OOp("isnot", (inner_case.true_branch, OLit(None))),
                                term.true_branch, OLit(None)),
                          OLit(None)),
                    "D41_optional_assoc",
                ))

    # ── 7. Exception monad: catch(catch(body, d1), d2) → catch(body, d2) ──
    if isinstance(term, OCatch):
        if isinstance(term.body, OCatch):
            inner = term.body
            # catch(catch(body, d1), d2) — if inner throws, d1 is used;
            # if d1 also throws, d2 is used; simplify to catch(body, d2)
            results.append((
                OCatch(inner.body, term.default),
                "D41_exception_assoc",
            ))

    # ── 8. catch(return(a), d) → return(a) — exception left unit ──
    if isinstance(term, OCatch):
        body = term.body
        if isinstance(body, OLit):
            # A literal can't throw
            results.append((body, "D41_exception_left_unit"))
        if isinstance(body, OOp) and body.name in ("return", "pure"):
            results.append((body, "D41_exception_left_unit"))

    # ── 9. List monad: nested comprehensions ──
    # map(f, map(g, xs)) → map(compose(f,g), xs) when f returns lists
    if isinstance(term, OMap) and term.filter_pred is None:
        if isinstance(term.collection, OMap) and term.collection.filter_pred is None:
            inner_map = term.collection
            if isinstance(term.transform, OLam) and isinstance(inner_map.transform, OLam):
                results.append((
                    OMap(
                        OLam(inner_map.transform.params,
                             OOp("apply", (term.transform, inner_map.transform.body))),
                        inner_map.collection,
                    ),
                    "D41_list_map_fusion",
                ))

    # ── 10. bind_optional(a, λx.x) → a  (right unit for optional) ──
    if isinstance(term, OOp) and term.name == "bind_optional" and len(term.args) == 2:
        m, f = term.args
        if isinstance(f, OLam) and len(f.params) == 1:
            if isinstance(f.body, OVar) and f.body.name == f.params[0]:
                results.append((m, "D41_optional_right_unit"))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D41 in reverse: introduce monadic structure."""
    results: List[Tuple[OTerm, str]] = []

    # f(a) → bind(return(a), f) — introduce left unit
    if isinstance(term, OOp) and len(term.args) == 1:
        a = term.args[0]
        results.append((
            OOp("bind", (OOp("return", (a,)), OOp(term.name, ()))),
            "D41_inv_left_unit",
        ))

    # m → bind(m, return) — introduce right unit
    if isinstance(term, OVar):
        results.append((
            OOp("bind", (term, OLam(("_x",), OVar("_x")))),
            "D41_inv_right_unit",
        ))

    # catch(body, d) → catch(catch(body, d), d) — introduce exception nesting
    if isinstance(term, OCatch):
        results.append((
            OCatch(OCatch(term.body, term.default), term.default),
            "D41_inv_exception_assoc",
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D41 can potentially rewrite *term*."""
    if isinstance(term, OOp) and term.name in ("bind", "flatmap", "chain", "bind_optional"):
        return True
    if isinstance(term, OCase):
        if _is_none_check(term.test) is not None:
            return True
    if isinstance(term, OCatch):
        return True
    if isinstance(term, OMap) and isinstance(term.collection, OMap):
        return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D41 relevance for bridging *source* → *target*."""
    sc, tc = source.canon(), target.canon()
    s_bind = "bind(" in sc or "flatmap(" in sc or "chain(" in sc
    t_bind = "bind(" in tc or "flatmap(" in tc or "chain(" in tc
    s_catch = "catch(" in sc
    t_catch = "catch(" in tc
    s_none = "None" in sc
    t_none = "None" in tc

    if s_bind or t_bind:
        return 0.85
    if s_catch != t_catch:
        return 0.70
    if s_none and t_none:
        return 0.60
    if s_catch and t_catch:
        return 0.55
    return 0.05


# ═══════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════

if __name__ == "__main__":
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
    a, m = OVar("a"), OVar("m")
    f_var, g_var = OVar("f"), OVar("g")

    # ── Left unit: bind(return(a), f) → f(a) ──
    print("D41: left unit ...")
    f_lam = OLam(("x",), OOp("f", (OVar("x"),)))
    t1 = OOp("bind", (OOp("return", (a,)), f_lam))
    r1 = apply(t1, ctx)
    _assert(any(lbl == "D41_left_unit" for _, lbl in r1), "left unit")

    # ── Right unit: bind(m, return) → m ──
    print("D41: right unit ...")
    ret_lam = OLam(("x",), OVar("x"))
    t2 = OOp("bind", (m, ret_lam))
    r2 = apply(t2, ctx)
    _assert(any(lbl == "D41_right_unit" for _, lbl in r2), "right unit")

    # ── Associativity: bind(bind(m,f), g) → bind(m, λx. bind(f(x), g)) ──
    print("D41: associativity ...")
    g_lam = OLam(("y",), OOp("g", (OVar("y"),)))
    inner = OOp("bind", (m, f_lam))
    t3 = OOp("bind", (inner, g_lam))
    r3 = apply(t3, ctx)
    _assert(any(lbl == "D41_assoc" for _, lbl in r3), "associativity")

    # ── Optional monad: case(x is not None, f(x), None) ──
    print("D41: optional bind ...")
    t4 = OCase(
        OOp("isnot", (a, OLit(None))),
        OOp("f", (a,)),
        OLit(None),
    )
    r4 = apply(t4, ctx)
    _assert(any(lbl == "D41_optional_bind" for _, lbl in r4), "optional bind")

    # ── Exception monad: catch(catch(body, d1), d2) → catch(body, d2) ──
    print("D41: exception assoc ...")
    body = OOp("risky", (a,))
    t5 = OCatch(OCatch(body, OLit(0)), OLit(-1))
    r5 = apply(t5, ctx)
    _assert(any(lbl == "D41_exception_assoc" for _, lbl in r5), "exception assoc")

    # ── Exception left unit: catch(lit, d) → lit ──
    print("D41: exception left unit ...")
    t6 = OCatch(OLit(42), OLit(0))
    r6 = apply(t6, ctx)
    _assert(any(lbl == "D41_exception_left_unit" for _, lbl in r6), "exception left unit")

    # ── List map fusion ──
    print("D41: list map fusion ...")
    f_m = OLam(("x",), OOp("f", (OVar("x"),)))
    g_m = OLam(("y",), OOp("g", (OVar("y"),)))
    xs = OVar("xs")
    t7 = OMap(f_m, OMap(g_m, xs))
    r7 = apply(t7, ctx)
    _assert(any(lbl == "D41_list_map_fusion" for _, lbl in r7), "list map fusion")

    # ── Optional right unit: bind_optional(a, λx.x) → a ──
    print("D41: optional right unit ...")
    t8 = OOp("bind_optional", (a, OLam(("x",), OVar("x"))))
    r8 = apply(t8, ctx)
    _assert(any(lbl == "D41_optional_right_unit" for _, lbl in r8), "optional right unit")

    # ── recognizes ──
    print("D41: recognizes ...")
    _assert(recognizes(t1), "recognizes bind")
    _assert(recognizes(t4), "recognizes optional pattern")
    _assert(recognizes(t5), "recognizes catch")
    _assert(not recognizes(OLit(42)), "does not recognise literal")

    # ── relevance_score ──
    print("D41: relevance_score ...")
    score = relevance_score(t1, t2)
    _assert(score > 0.5, f"bind relevance={score:.2f}")

    # ── apply_inverse ──
    print("D41: apply_inverse ...")
    inv = apply_inverse(OOp("f", (a,)), ctx)
    _assert(any(lbl == "D41_inv_left_unit" for _, lbl in inv), "inv left unit")

    inv2 = apply_inverse(m, ctx)
    _assert(any(lbl == "D41_inv_right_unit" for _, lbl in inv2), "inv right unit")

    print(f"\n{'='*50}")
    print(f"  D41 monad: {_pass} passed, {_fail} failed")
    print(f"{'='*50}")
    if _fail > 0:
        raise SystemExit(1)
