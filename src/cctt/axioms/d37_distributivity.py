"""D37: Distributivity / Factoring Axiom.

Algebraic distribution and factoring laws lifted to OTerm rewrites.

Mathematical foundation:
  In any ring (R, +, ·), multiplication distributes over addition:
    a·b + a·c  =  a·(b + c)          [left distributivity]
    b·a + c·a  =  (b + c)·a          [right distributivity]

  This generalises to higher-order structures:
    • f(x) if c else f(y) ≡ f(x if c else y)   [functor over coproduct]
    • map(f, xs ++ ys) ≡ map(f, xs) ++ map(f, ys) [functor preserves coproduct]
    • fold⊕(xs ++ ys) = fold⊕(xs) ⊕ fold⊕(ys)  [monoid homomorphism]
    • (a+b) if c else (a+d) ≡ a + (b if c else d) [conditional distribution]

Covers:
  • Factor out common multiplicative terms
  • Push function application inside/outside conditionals
  • Map distributes over concatenation
  • Fold distributes over concatenation for monoidal ops
  • Conditional factoring — extract shared sub-expressions from branches
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

AXIOM_NAME = "D37_distributivity"
AXIOM_CATEGORY = "algebraic"

SOUNDNESS_PROOF = r"""
Theorem (Distributivity).
  In any ring (R, +, ·):
    a·b + a·c = a·(b + c)           [left distributivity]

  In any cartesian closed category:
    f(x) if c else f(y) = f(x if c else y)
  because case(c, f(x), f(y)) = f(case(c, x, y)) when f is a morphism.

  For monoid homomorphisms h: (M,⊕) → (N,⊗):
    h(a ⊕ b) = h(a) ⊗ h(b)
  Thus fold⊕(xs ++ ys) = fold⊕(xs) ⊕ fold⊕(ys).

  Conditional distribution:
    (a ⊕ b) if c else (a ⊕ d) = a ⊕ (b if c else d)
  by factoring a from both branches.  ∎
"""

COMPOSES_WITH = ["D17_assoc", "D04_comp_fusion", "D24_eta", "D40_curry"]
REQUIRES: List[str] = []

EXAMPLES = [
    {
        "name": "Factor common multiplier (left)",
        "before": "add(mul(a, b), mul(a, c))",
        "after": "mul(a, add(b, c))",
        "axiom": "D37_factor_left",
    },
    {
        "name": "Factor common multiplier (right)",
        "before": "add(mul(b, a), mul(c, a))",
        "after": "mul(add(b, c), a)",
        "axiom": "D37_factor_right",
    },
    {
        "name": "Push function inside conditional",
        "before": "case(c, f(x), f(y))",
        "after": "f(case(c, x, y))",
        "axiom": "D37_func_into_case",
    },
    {
        "name": "Map distributes over concat",
        "before": "concat(map(f, xs), map(f, ys))",
        "after": "map(f, concat(xs, ys))",
        "axiom": "D37_map_over_concat",
    },
    {
        "name": "Fold distributes over concat (monoid)",
        "before": "add(fold[add](0, xs), fold[add](0, ys))",
        "after": "fold[add](0, concat(xs, ys))",
        "axiom": "D37_fold_over_concat",
    },
    {
        "name": "Conditional factor shared sub-expression",
        "before": "case(c, add(a, b), add(a, d))",
        "after": "add(a, case(c, b, d))",
        "axiom": "D37_case_factor",
    },
]

# ── Ops that distribute over addition-like ops ──
_DISTRIBUTIVE_PAIRS: Dict[str, str] = {
    "mul": "add", "mult": "add", "imul": "iadd",
    "bitand": "bitor",
}

_MONOID_OPS: FrozenSet[str] = frozenset({
    "add", "mul", "mult", "concat", "bitor", "bitand",
    "min", "max", "union", "intersection",
})


@dataclass
class FiberCtx:
    param_duck_types: Dict[str, str] = field(default_factory=dict)

    def is_numeric(self, term: OTerm) -> bool:
        return True


# ═══════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════

def _terms_equal(a: OTerm, b: OTerm) -> bool:
    return a.canon() == b.canon()


def _extract_common_factor_left(t1: OTerm, t2: OTerm, mul_op: str
                                 ) -> Optional[Tuple[OTerm, OTerm, OTerm]]:
    """If t1 = mul(a, b) and t2 = mul(a, c), return (a, b, c)."""
    if (isinstance(t1, OOp) and t1.name == mul_op and len(t1.args) == 2
            and isinstance(t2, OOp) and t2.name == mul_op and len(t2.args) == 2):
        if _terms_equal(t1.args[0], t2.args[0]):
            return (t1.args[0], t1.args[1], t2.args[1])
    return None


def _extract_common_factor_right(t1: OTerm, t2: OTerm, mul_op: str
                                  ) -> Optional[Tuple[OTerm, OTerm, OTerm]]:
    """If t1 = mul(b, a) and t2 = mul(c, a), return (a, b, c)."""
    if (isinstance(t1, OOp) and t1.name == mul_op and len(t1.args) == 2
            and isinstance(t2, OOp) and t2.name == mul_op and len(t2.args) == 2):
        if _terms_equal(t1.args[1], t2.args[1]):
            return (t1.args[1], t1.args[0], t2.args[0])
    return None


def _branches_share_func(case: OCase) -> Optional[Tuple[str, OTerm, OTerm]]:
    """If both branches are f(x), f(y), return (f, x, y)."""
    tb, fb = case.true_branch, case.false_branch
    if (isinstance(tb, OOp) and isinstance(fb, OOp)
            and tb.name == fb.name and len(tb.args) == 1 and len(fb.args) == 1):
        return (tb.name, tb.args[0], fb.args[0])
    return None


def _branches_share_operand(case: OCase, op_name: str
                             ) -> Optional[Tuple[OTerm, OTerm, OTerm]]:
    """If branches are op(a,b) and op(a,d), return (a, b, d)."""
    tb, fb = case.true_branch, case.false_branch
    if (isinstance(tb, OOp) and isinstance(fb, OOp)
            and tb.name == op_name and fb.name == op_name
            and len(tb.args) == 2 and len(fb.args) == 2):
        if _terms_equal(tb.args[0], fb.args[0]):
            return (tb.args[0], tb.args[1], fb.args[1])
        if _terms_equal(tb.args[1], fb.args[1]):
            return (tb.args[1], tb.args[0], fb.args[0])
    return None


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D37 distributivity/factoring rewrites to *term*."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── 1. Factor common term: a*b + a*c → a*(b+c) ──
    if isinstance(term, OOp) and len(term.args) == 2:
        add_op = term.name
        lhs, rhs = term.args
        for mul_op, target_add in _DISTRIBUTIVE_PAIRS.items():
            if add_op == target_add:
                fac = _extract_common_factor_left(lhs, rhs, mul_op)
                if fac is not None:
                    a, b, c = fac
                    results.append((
                        OOp(mul_op, (a, OOp(add_op, (b, c)))),
                        "D37_factor_left",
                    ))
                fac_r = _extract_common_factor_right(lhs, rhs, mul_op)
                if fac_r is not None:
                    a, b, c = fac_r
                    results.append((
                        OOp(mul_op, (OOp(add_op, (b, c)), a)),
                        "D37_factor_right",
                    ))

    # ── 2. Expand: a*(b+c) → a*b + a*c ──
    if isinstance(term, OOp) and len(term.args) == 2:
        mul_op = term.name
        if mul_op in _DISTRIBUTIVE_PAIRS:
            add_op = _DISTRIBUTIVE_PAIRS[mul_op]
            a, inner = term.args
            if isinstance(inner, OOp) and inner.name == add_op and len(inner.args) == 2:
                b, c = inner.args
                results.append((
                    OOp(add_op, (OOp(mul_op, (a, b)), OOp(mul_op, (a, c)))),
                    "D37_expand_left",
                ))
            # Right: (b+c)*a → b*a + c*a
            inner_l, a2 = term.args
            if isinstance(inner_l, OOp) and inner_l.name == add_op and len(inner_l.args) == 2:
                b, c = inner_l.args
                results.append((
                    OOp(add_op, (OOp(mul_op, (b, a2)), OOp(mul_op, (c, a2)))),
                    "D37_expand_right",
                ))

    # ── 3. Push function inside conditional: case(c, f(x), f(y)) → f(case(c, x, y)) ──
    if isinstance(term, OCase):
        shared = _branches_share_func(term)
        if shared is not None:
            fname, x, y = shared
            results.append((
                OOp(fname, (OCase(term.test, x, y),)),
                "D37_func_into_case",
            ))

    # ── 4. Pull function outside conditional: f(case(c, x, y)) → case(c, f(x), f(y)) ──
    if isinstance(term, OOp) and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OCase):
            results.append((
                OCase(inner.test,
                      OOp(term.name, (inner.true_branch,)),
                      OOp(term.name, (inner.false_branch,))),
                "D37_func_out_of_case",
            ))

    # ── 5. Map over concat: concat(map(f,xs), map(f,ys)) → map(f, concat(xs,ys)) ──
    if isinstance(term, OOp) and term.name in ("concat", "add") and len(term.args) == 2:
        lhs, rhs = term.args
        if (isinstance(lhs, OMap) and isinstance(rhs, OMap)
                and _terms_equal(lhs.transform, rhs.transform)
                and lhs.filter_pred is None and rhs.filter_pred is None):
            results.append((
                OMap(lhs.transform, OOp("concat", (lhs.collection, rhs.collection))),
                "D37_map_over_concat",
            ))

    # ── 6. Split map over concat: map(f, concat(xs,ys)) → concat(map(f,xs), map(f,ys)) ──
    if isinstance(term, OMap) and term.filter_pred is None:
        coll = term.collection
        if isinstance(coll, OOp) and coll.name == "concat" and len(coll.args) == 2:
            xs, ys = coll.args
            results.append((
                OOp("concat", (OMap(term.transform, xs), OMap(term.transform, ys))),
                "D37_map_split_concat",
            ))

    # ── 7. Fold over concat (monoid): op(fold[op](e, xs), fold[op](e, ys)) → fold[op](e, concat(xs,ys)) ──
    if isinstance(term, OOp) and term.name in _MONOID_OPS and len(term.args) == 2:
        lhs, rhs = term.args
        if (isinstance(lhs, OFold) and isinstance(rhs, OFold)
                and lhs.op_name == term.name and rhs.op_name == term.name
                and _terms_equal(lhs.init, rhs.init)):
            results.append((
                OFold(term.name, lhs.init, OOp("concat", (lhs.collection, rhs.collection))),
                "D37_fold_over_concat",
            ))

    # ── 8. Conditional factor: case(c, op(a,b), op(a,d)) → op(a, case(c,b,d)) ──
    if isinstance(term, OCase):
        for op_name in _MONOID_OPS:
            shared_op = _branches_share_operand(term, op_name)
            if shared_op is not None:
                a, b, d = shared_op
                results.append((
                    OOp(op_name, (a, OCase(term.test, b, d))),
                    "D37_case_factor",
                ))
                break

    return results


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D37 in reverse: factor → expand, merge → split."""
    results: List[Tuple[OTerm, str]] = []
    # Expand is the inverse of factor — handled in apply as expand rules
    # Pull function out of conditional
    if isinstance(term, OOp) and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OCase):
            results.append((
                OCase(inner.test,
                      OOp(term.name, (inner.true_branch,)),
                      OOp(term.name, (inner.false_branch,))),
                "D37_inv_func_out_of_case",
            ))
    return results


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D37 is potentially applicable."""
    if isinstance(term, OCase):
        return True
    if isinstance(term, OOp) and len(term.args) == 2:
        if term.name in _MONOID_OPS or term.name in _DISTRIBUTIVE_PAIRS:
            return True
        add_op = term.name
        for mul_op, target_add in _DISTRIBUTIVE_PAIRS.items():
            if add_op == target_add:
                return True
    if isinstance(term, OMap):
        if isinstance(term.collection, OOp) and term.collection.name == "concat":
            return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D37 relevance for bridging *source* → *target*."""
    sc, tc = source.canon(), target.canon()
    s_has_mul = "mul(" in sc or "mult(" in sc
    t_has_mul = "mul(" in tc or "mult(" in tc
    s_has_case = "case(" in sc
    t_has_case = "case(" in tc
    s_has_map = "map(" in sc
    t_has_map = "map(" in tc

    if s_has_mul != t_has_mul:
        return 0.85
    if s_has_case and t_has_case:
        return 0.60
    if s_has_map and t_has_map and ("concat" in sc or "concat" in tc):
        return 0.70
    if "fold[" in sc and "fold[" in tc:
        return 0.65
    return 0.10


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
    a, b, c, d = OVar("a"), OVar("b"), OVar("c"), OVar("d")
    xs, ys = OVar("xs"), OVar("ys")
    cond = OVar("cond")

    # ── Factor left: a*b + a*c → a*(b+c) ──
    print("D37: factor left ...")
    t1 = OOp("add", (OOp("mul", (a, b)), OOp("mul", (a, c))))
    r1 = apply(t1, ctx)
    _assert(any(lbl == "D37_factor_left" for _, lbl in r1), "factor left")

    # ── Factor right: b*a + c*a → (b+c)*a ──
    print("D37: factor right ...")
    t2 = OOp("add", (OOp("mul", (b, a)), OOp("mul", (c, a))))
    r2 = apply(t2, ctx)
    _assert(any(lbl == "D37_factor_right" for _, lbl in r2), "factor right")

    # ── Expand left: a*(b+c) → a*b + a*c ──
    print("D37: expand left ...")
    t3 = OOp("mul", (a, OOp("add", (b, c))))
    r3 = apply(t3, ctx)
    _assert(any(lbl == "D37_expand_left" for _, lbl in r3), "expand left")

    # ── Expand right: (b+c)*a → b*a + c*a ──
    print("D37: expand right ...")
    t4 = OOp("mul", (OOp("add", (b, c)), a))
    r4 = apply(t4, ctx)
    _assert(any(lbl == "D37_expand_right" for _, lbl in r4), "expand right")

    # ── Function into case: case(c, f(x), f(y)) → f(case(c, x, y)) ──
    print("D37: func into case ...")
    t5 = OCase(cond, OOp("f", (a,)), OOp("f", (b,)))
    r5 = apply(t5, ctx)
    _assert(any(lbl == "D37_func_into_case" for _, lbl in r5), "func into case")

    # ── Function out of case: f(case(c, x, y)) → case(c, f(x), f(y)) ──
    print("D37: func out of case ...")
    t6 = OOp("f", (OCase(cond, a, b),))
    r6 = apply(t6, ctx)
    _assert(any(lbl == "D37_func_out_of_case" for _, lbl in r6), "func out of case")

    # ── Map over concat ──
    print("D37: map over concat ...")
    f_lam = OLam(("x",), OOp("f", (OVar("x"),)))
    t7 = OOp("concat", (OMap(f_lam, xs), OMap(f_lam, ys)))
    r7 = apply(t7, ctx)
    _assert(any(lbl == "D37_map_over_concat" for _, lbl in r7), "map over concat")

    # ── Map split concat ──
    print("D37: map split concat ...")
    t8 = OMap(f_lam, OOp("concat", (xs, ys)))
    r8 = apply(t8, ctx)
    _assert(any(lbl == "D37_map_split_concat" for _, lbl in r8), "map split concat")

    # ── Fold over concat ──
    print("D37: fold over concat ...")
    t9 = OOp("add", (OFold("add", OLit(0), xs), OFold("add", OLit(0), ys)))
    r9 = apply(t9, ctx)
    _assert(any(lbl == "D37_fold_over_concat" for _, lbl in r9), "fold over concat")

    # ── Case factor: case(c, add(a,b), add(a,d)) → add(a, case(c,b,d)) ──
    print("D37: case factor ...")
    t10 = OCase(cond, OOp("add", (a, b)), OOp("add", (a, d)))
    r10 = apply(t10, ctx)
    _assert(any(lbl == "D37_case_factor" for _, lbl in r10), "case factor")

    # ── recognizes ──
    print("D37: recognizes ...")
    _assert(recognizes(t1), "recognizes add(mul, mul)")
    _assert(recognizes(t5), "recognizes case")
    _assert(not recognizes(OLit(42)), "does not recognise literal")

    # ── relevance_score ──
    print("D37: relevance_score ...")
    score = relevance_score(t1, t3)
    _assert(score > 0.0, f"factor↔expand score={score:.2f} > 0.0")

    # ── apply_inverse ──
    print("D37: apply_inverse ...")
    inv = apply_inverse(t6, ctx)
    _assert(len(inv) >= 1, "inverse func out of case")

    print(f"\n{'='*50}")
    print(f"  D37 distributivity: {_pass} passed, {_fail} failed")
    print(f"{'='*50}")
    if _fail > 0:
        raise SystemExit(1)
