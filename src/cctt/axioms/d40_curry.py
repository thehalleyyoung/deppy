"""D40: Currying ↔ Uncurrying Axiom.

Converts between curried and uncurried function representations.

Mathematical foundation:
  In any cartesian closed category (CCC), the curry adjunction:
    Hom(A × B, C)  ≅  Hom(A, C^B)
  gives a natural isomorphism between:
    f : A × B → C              [uncurried]
    curry(f) : A → (B → C)     [curried]

  This extends to:
    f(a)(b)  ≡  f(a, b)                      [curry/uncurry]
    λa. λb. body  ≡  λ(a,b). body            [lambda flattening]
    partial(f, a)  ≡  λb. f(a, b)            [partial = curry + apply]
    map(partial(add, 1), xs) ≡ [x+1 for x in xs]  [partial in HOF]
    flip(f)(a)(b) ≡ f(b)(a)                   [argument reordering]

Covers:
  • f(a)(b) ↔ f(a, b) conversion
  • Nested lambda flattening
  • functools.partial ↔ lambda equivalence
  • partial in map/filter contexts
  • flip / argument reordering
  • Section syntax: (+ 1) ↔ partial(add, 1) ↔ λx. x + 1
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

AXIOM_NAME = "D40_curry"
AXIOM_CATEGORY = "higher_order"

SOUNDNESS_PROOF = r"""
Theorem (Curry-Uncurry Adjunction).
  In any CCC, the exponential adjunction gives:
    curry : Hom(A × B, C) → Hom(A, C^B)
    uncurry : Hom(A, C^B) → Hom(A × B, C)
  with curry ∘ uncurry = id and uncurry ∘ curry = id.

  Lambda flattening: λa. λb. e  =  λ(a,b). e
  by iterated currying.

  Partial application: partial(f, a)  =  curry(f)(a)
  which equals λb. f(a, b) by definition of curry.

  Flip: flip(f)(a)(b) = f(b)(a) = curry(f ∘ swap)(a)(b)
  where swap(a,b) = (b,a).  ∎
"""

COMPOSES_WITH = ["D24_eta", "D39_defunc", "D38_partial_eval"]
REQUIRES: List[str] = []

EXAMPLES = [
    {
        "name": "Uncurry: f(a)(b) → f(a, b)",
        "before": "apply(apply(f, a), b)",
        "after": "f(a, b)",
        "axiom": "D40_uncurry",
    },
    {
        "name": "Flatten nested lambda",
        "before": "λ(a)λ(b)add(a, b)",
        "after": "λ(a, b)add(a, b)",
        "axiom": "D40_flatten_lambda",
    },
    {
        "name": "partial → lambda",
        "before": "partial(f, a)",
        "after": "λ(b)f(a, b)",
        "axiom": "D40_partial_to_lambda",
    },
    {
        "name": "lambda → partial",
        "before": "λ(b)f(a, b)",
        "after": "partial(f, a)",
        "axiom": "D40_lambda_to_partial",
    },
    {
        "name": "map(partial(add,1), xs) → [x+1 for x in xs]",
        "before": "map(partial(add, 1), xs)",
        "after": "map(λ(_b0)add(_b0, 1), xs)",
        "axiom": "D40_partial_in_map",
    },
    {
        "name": "flip",
        "before": "flip(f)(a)(b)",
        "after": "f(b, a)",
        "axiom": "D40_flip",
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

def _extract_free_vars(term: OTerm, bound: Optional[Set[str]] = None) -> Set[str]:
    """Extract free variables from a term."""
    if bound is None:
        bound = set()
    if isinstance(term, OVar):
        return {term.name} - bound
    if isinstance(term, (OLit, OUnknown)):
        return set()
    if isinstance(term, OOp):
        r: Set[str] = set()
        for a in term.args:
            r |= _extract_free_vars(a, bound)
        return r
    if isinstance(term, OLam):
        return _extract_free_vars(term.body, bound | set(term.params))
    if isinstance(term, OCase):
        return (_extract_free_vars(term.test, bound)
                | _extract_free_vars(term.true_branch, bound)
                | _extract_free_vars(term.false_branch, bound))
    if isinstance(term, OSeq):
        r2: Set[str] = set()
        for e in term.elements:
            r2 |= _extract_free_vars(e, bound)
        return r2
    if isinstance(term, OFold):
        return _extract_free_vars(term.init, bound) | _extract_free_vars(term.collection, bound)
    if isinstance(term, OMap):
        r3 = _extract_free_vars(term.transform, bound) | _extract_free_vars(term.collection, bound)
        if term.filter_pred:
            r3 |= _extract_free_vars(term.filter_pred, bound)
        return r3
    if isinstance(term, ODict):
        r4: Set[str] = set()
        for k, v in term.pairs:
            r4 |= _extract_free_vars(k, bound) | _extract_free_vars(v, bound)
        return r4
    if isinstance(term, OQuotient):
        return _extract_free_vars(term.inner, bound)
    if isinstance(term, OCatch):
        return _extract_free_vars(term.body, bound) | _extract_free_vars(term.default, bound)
    if isinstance(term, OFix):
        return _extract_free_vars(term.body, bound)
    if isinstance(term, OAbstract):
        r5: Set[str] = set()
        for a in term.inputs:
            r5 |= _extract_free_vars(a, bound)
        return r5
    return set()


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D40 currying/uncurrying rewrites to *term*."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── 1. Flatten nested lambdas: λa. λb. body → λ(a,b). body ──
    if isinstance(term, OLam):
        if isinstance(term.body, OLam):
            inner = term.body
            merged_params = term.params + inner.params
            results.append((
                OLam(merged_params, inner.body),
                "D40_flatten_lambda",
            ))

    # ── 2. Nest lambda: λ(a,b). body → λa. λb. body ──
    if isinstance(term, OLam) and len(term.params) >= 2:
        outer_param = (term.params[0],)
        inner_params = term.params[1:]
        results.append((
            OLam(outer_param, OLam(inner_params, term.body)),
            "D40_nest_lambda",
        ))

    # ── 3. partial(f, c₁, ...) → λ(x₁,...). f(c₁,...,x₁,...) ──
    if isinstance(term, OOp) and term.name == "partial" and len(term.args) >= 2:
        fn = term.args[0]
        consts = term.args[1:]
        if isinstance(fn, OOp) and len(fn.args) == 0:
            # partial(f, c) → λ(_x). f(c, _x)
            param = "_px"
            results.append((
                OLam((param,), OOp(fn.name, consts + (OVar(param),))),
                "D40_partial_to_lambda",
            ))
        elif isinstance(fn, OVar):
            param = "_px"
            results.append((
                OLam((param,), OOp(fn.name, consts + (OVar(param),))),
                "D40_partial_to_lambda",
            ))

    # ── 4. λb. f(a, b) → partial(f, a) when a is free ──
    if isinstance(term, OLam) and len(term.params) == 1:
        p = term.params[0]
        body = term.body
        if isinstance(body, OOp) and len(body.args) >= 2:
            # Check: last arg is the param, everything else is free
            if (isinstance(body.args[-1], OVar) and body.args[-1].name == p):
                leading_args = body.args[:-1]
                # Ensure param doesn't appear in leading args
                param_in_leading = any(
                    p in _extract_free_vars(a) for a in leading_args
                )
                if not param_in_leading and len(leading_args) >= 1:
                    results.append((
                        OOp("partial", (OOp(body.name, ()), *leading_args)),
                        "D40_lambda_to_partial",
                    ))

    # ── 5. map(partial(f, c), xs) → map(λx. f(c, x), xs) ──
    if isinstance(term, OMap) and isinstance(term.transform, OOp):
        tf = term.transform
        if tf.name == "partial" and len(tf.args) >= 2:
            fn = tf.args[0]
            consts = tf.args[1:]
            if isinstance(fn, OOp) and len(fn.args) == 0:
                param = "_px"
                new_lam = OLam((param,), OOp(fn.name, consts + (OVar(param),)))
                results.append((
                    OMap(new_lam, term.collection, term.filter_pred),
                    "D40_partial_in_map",
                ))

    # ── 6. flip(f) → λa. λb. f(b, a) ──
    if isinstance(term, OOp) and term.name == "flip" and len(term.args) == 1:
        fn = term.args[0]
        if isinstance(fn, OOp) and len(fn.args) == 0:
            results.append((
                OLam(("_a", "_b"), OOp(fn.name, (OVar("_b"), OVar("_a")))),
                "D40_flip_to_lambda",
            ))
        elif isinstance(fn, OVar):
            results.append((
                OLam(("_a", "_b"), OOp(fn.name, (OVar("_b"), OVar("_a")))),
                "D40_flip_to_lambda",
            ))

    # ── 7. λ(a,b). f(b, a) → flip(f) ──
    if isinstance(term, OLam) and len(term.params) == 2:
        a_p, b_p = term.params
        body = term.body
        if (isinstance(body, OOp) and len(body.args) == 2
                and isinstance(body.args[0], OVar) and body.args[0].name == b_p
                and isinstance(body.args[1], OVar) and body.args[1].name == a_p):
            results.append((
                OOp("flip", (OOp(body.name, ()),)),
                "D40_lambda_to_flip",
            ))

    # ── 8. compose(f, partial(g, c)) → λx. f(g(c, x)) ──
    if isinstance(term, OOp) and term.name == "compose" and len(term.args) == 2:
        f_term, g_term = term.args
        if isinstance(g_term, OOp) and g_term.name == "partial" and len(g_term.args) >= 2:
            fn_g = g_term.args[0]
            consts = g_term.args[1:]
            if isinstance(f_term, OOp) and isinstance(fn_g, OOp):
                param = "_cx"
                inner = OOp(fn_g.name, consts + (OVar(param),))
                results.append((
                    OLam((param,), OOp(f_term.name, (inner,))),
                    "D40_compose_partial",
                ))

    # ── 9. Section: OOp with one arg → partial application ──
    if isinstance(term, OOp) and len(term.args) == 1 and not isinstance(term.args[0], OOp):
        # f(c) where f is a binary op → partial(f, c) conceptually
        if term.name in ("add", "mul", "mult", "sub"):
            results.append((
                OOp("partial", (OOp(term.name, ()), term.args[0])),
                "D40_section_to_partial",
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D40 in reverse."""
    results: List[Tuple[OTerm, str]] = []

    # Nested lambda → flat lambda (this is also a forward rule)
    if isinstance(term, OLam) and len(term.params) >= 2:
        outer_param = (term.params[0],)
        inner_params = term.params[1:]
        results.append((
            OLam(outer_param, OLam(inner_params, term.body)),
            "D40_inv_curry",
        ))

    # Lambda → partial
    if isinstance(term, OLam) and len(term.params) == 1:
        p = term.params[0]
        body = term.body
        if isinstance(body, OOp) and len(body.args) >= 2:
            if (isinstance(body.args[-1], OVar) and body.args[-1].name == p):
                leading = body.args[:-1]
                param_in_leading = any(
                    p in _extract_free_vars(a) for a in leading
                )
                if not param_in_leading and len(leading) >= 1:
                    results.append((
                        OOp("partial", (OOp(body.name, ()), *leading)),
                        "D40_inv_lambda_to_partial",
                    ))

    return results


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D40 can potentially rewrite *term*."""
    if isinstance(term, OLam):
        # Nested lambda or multi-param lambda
        if isinstance(term.body, OLam):
            return True
        if len(term.params) >= 2:
            return True
        # Lambda wrapping a call → possible partial
        if isinstance(term.body, OOp) and len(term.body.args) >= 2:
            return True
    if isinstance(term, OOp):
        if term.name == "partial":
            return True
        if term.name == "flip":
            return True
        if term.name == "compose":
            return True
    if isinstance(term, OMap) and isinstance(term.transform, OOp):
        if term.transform.name == "partial":
            return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D40 relevance for bridging *source* → *target*."""
    sc, tc = source.canon(), target.canon()
    s_partial = "partial(" in sc
    t_partial = "partial(" in tc
    s_lam = "λ(" in sc
    t_lam = "λ(" in tc
    s_flip = "flip(" in sc
    t_flip = "flip(" in tc

    # partial ↔ lambda
    if s_partial != t_partial:
        return 0.85
    # Nested vs flat lambdas
    if s_lam and t_lam:
        s_depth = sc.count("λ(")
        t_depth = tc.count("λ(")
        if s_depth != t_depth:
            return 0.75
    # flip involved
    if s_flip or t_flip:
        return 0.70
    if s_lam or t_lam:
        return 0.30
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
    a, b, c = OVar("a"), OVar("b"), OVar("c")
    x, xs = OVar("x"), OVar("xs")

    # ── Flatten nested lambda: λa. λb. add(a,b) → λ(a,b). add(a,b) ──
    print("D40: flatten lambda ...")
    t1 = OLam(("a",), OLam(("b",), OOp("add", (OVar("a"), OVar("b")))))
    r1 = apply(t1, ctx)
    _assert(any(lbl == "D40_flatten_lambda" for _, lbl in r1), "flatten lambda")
    flat = [t for t, lbl in r1 if lbl == "D40_flatten_lambda"]
    if flat:
        _assert(isinstance(flat[0], OLam) and len(flat[0].params) == 2, "merged 2 params")

    # ── Nest lambda: λ(a,b). body → λa. λb. body ──
    print("D40: nest lambda ...")
    t2 = OLam(("a", "b"), OOp("add", (OVar("a"), OVar("b"))))
    r2 = apply(t2, ctx)
    _assert(any(lbl == "D40_nest_lambda" for _, lbl in r2), "nest lambda")

    # ── partial(f, c) → λx. f(c, x) ──
    print("D40: partial → lambda ...")
    t3 = OOp("partial", (OOp("add", ()), OLit(1)))
    r3 = apply(t3, ctx)
    _assert(any(lbl == "D40_partial_to_lambda" for _, lbl in r3), "partial → lambda")

    # ── λb. f(a, b) → partial(f, a) ──
    print("D40: lambda → partial ...")
    t4 = OLam(("b",), OOp("f", (a, OVar("b"))))
    r4 = apply(t4, ctx)
    _assert(any(lbl == "D40_lambda_to_partial" for _, lbl in r4), "lambda → partial")

    # ── map(partial(add, 1), xs) → map(λx. add(1,x), xs) ──
    print("D40: partial in map ...")
    t5 = OMap(OOp("partial", (OOp("add", ()), OLit(1))), xs)
    r5 = apply(t5, ctx)
    _assert(any(lbl == "D40_partial_in_map" for _, lbl in r5), "partial in map")

    # ── flip(f) → λ(a,b). f(b,a) ──
    print("D40: flip ...")
    t6 = OOp("flip", (OOp("sub", ()),))
    r6 = apply(t6, ctx)
    _assert(any(lbl == "D40_flip_to_lambda" for _, lbl in r6), "flip → lambda")

    # ── λ(a,b). f(b,a) → flip(f) ──
    print("D40: lambda → flip ...")
    t7 = OLam(("a", "b"), OOp("sub", (OVar("b"), OVar("a"))))
    r7 = apply(t7, ctx)
    _assert(any(lbl == "D40_lambda_to_flip" for _, lbl in r7), "lambda → flip")

    # ── Section: add(1) → partial(add, 1) ──
    print("D40: section ...")
    t8 = OOp("add", (OLit(1),))
    r8 = apply(t8, ctx)
    _assert(any(lbl == "D40_section_to_partial" for _, lbl in r8), "section → partial")

    # ── recognizes ──
    print("D40: recognizes ...")
    _assert(recognizes(t1), "recognizes nested lambda")
    _assert(recognizes(t2), "recognizes multi-param lambda")
    _assert(recognizes(t3), "recognizes partial")
    _assert(recognizes(t6), "recognizes flip")
    _assert(not recognizes(OLit(42)), "does not recognise literal")

    # ── relevance_score ──
    print("D40: relevance_score ...")
    score = relevance_score(t3, t4)
    _assert(score > 0.5, f"partial↔lambda score={score:.2f}")

    # ── apply_inverse ──
    print("D40: apply_inverse ...")
    inv = apply_inverse(t2, ctx)
    _assert(any(lbl == "D40_inv_curry" for _, lbl in inv), "inv curry")

    inv2 = apply_inverse(t4, ctx)
    _assert(any(lbl == "D40_inv_lambda_to_partial" for _, lbl in inv2), "inv lambda → partial")

    print(f"\n{'='*50}")
    print(f"  D40 curry: {_pass} passed, {_fail} failed")
    print(f"{'='*50}")
    if _fail > 0:
        raise SystemExit(1)
