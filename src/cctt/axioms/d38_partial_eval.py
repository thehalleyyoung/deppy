"""D38: Partial Evaluation / Specialization Axiom.

Reduces expressions containing known constants at "compile time"
by substituting and simplifying.

Mathematical foundation:
  Partial evaluation is the first Futamura projection:
    mix(p, s₁) = p_s₁
  where p is a program, s₁ is a static input, and p_s₁ is the
  residual (specialised) program.

  In the OTerm algebra this becomes β-reduction at known positions:
    (λx. body)(c) → body[x := c]   when c is a literal

  Combined with algebraic simplification:
    x + 0 → x          [additive identity]
    x * 1 → x          [multiplicative identity]
    x * 0 → 0          [annihilator]
    True and x → x     [boolean identity]
    filter(λx.True, xs) → xs  [trivial predicate elimination]
    map(λx.x, xs) → xs        [identity function elimination]
    range(0, n, 1) → range(n) [default argument specialisation]

Covers:
  • Constant folding in arithmetic
  • Identity / annihilator elimination
  • Trivial predicate / identity map elimination
  • Default argument specialisation
  • Constant propagation through OTerm trees
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

AXIOM_NAME = "D38_partial_eval"
AXIOM_CATEGORY = "algebraic"

SOUNDNESS_PROOF = r"""
Theorem (Partial Evaluation Correctness — First Futamura Projection).
  Let p be a program and s₁ a static input.  Then:
    ∀ d. ⟦p⟧(s₁, d) = ⟦mix(p, s₁)⟧(d)
  where mix is the partial evaluator and ⟦·⟧ is the denotation.

  Each rule is sound by substitution + algebraic identity:
    • x + 0 = x        by additive identity
    • x * 1 = x        by multiplicative identity
    • x * 0 = 0        by annihilator axiom
    • True ∧ x = x     by boolean algebra
    • filter(⊤, xs) = xs   by predicate logic
    • map(id, xs) = xs     by functor identity law
    • β-reduction: (λx.e)(v) = e[x:=v]  ∎
"""

COMPOSES_WITH = ["D02_beta", "D24_eta", "D17_assoc", "D37_distributivity"]
REQUIRES: List[str] = []

EXAMPLES = [
    {
        "name": "Additive identity",
        "before": "add(x, 0)",
        "after": "x",
        "axiom": "D38_identity_add",
    },
    {
        "name": "Multiplicative identity",
        "before": "mul(x, 1)",
        "after": "x",
        "axiom": "D38_identity_mul",
    },
    {
        "name": "Annihilator",
        "before": "mul(x, 0)",
        "after": "0",
        "axiom": "D38_annihilator",
    },
    {
        "name": "Trivial filter",
        "before": "filter(λx.True, xs)",
        "after": "xs",
        "axiom": "D38_trivial_filter",
    },
    {
        "name": "Identity map",
        "before": "map(λx.x, xs)",
        "after": "xs",
        "axiom": "D38_identity_map",
    },
    {
        "name": "range default args",
        "before": "range(0, n, 1)",
        "after": "range(n)",
        "axiom": "D38_range_default",
    },
    {
        "name": "Constant conditional",
        "before": "case(True, a, b)",
        "after": "a",
        "axiom": "D38_const_case_true",
    },
]

# ── Identity elements and annihilators ──
_IDENTITY: Dict[str, Any] = {
    "add": 0, "iadd": 0, "sub": 0,
    "mul": 1, "mult": 1, "imul": 1,
    "concat": "", "bitor": 0, "bitand": -1, "bitxor": 0,
    "and": True, "or": False,
}

_ANNIHILATOR: Dict[str, Any] = {
    "mul": 0, "mult": 0, "imul": 0,
    "and": False,
}

_ANNIHILATOR_RESULT: Dict[str, Any] = {
    "mul": 0, "mult": 0, "imul": 0,
    "and": False,
}


@dataclass
class FiberCtx:
    param_duck_types: Dict[str, str] = field(default_factory=dict)

    def is_numeric(self, term: OTerm) -> bool:
        return True


# ═══════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════

def _is_identity_lam(lam: OLam) -> bool:
    """Check if lambda is the identity: λx. x."""
    if len(lam.params) == 1:
        body = lam.body
        return isinstance(body, OVar) and body.name == lam.params[0]
    return False


def _is_true_lam(lam: OLam) -> bool:
    """Check if lambda is constantly True: λx. True."""
    return isinstance(lam.body, OLit) and lam.body.value is True


def _is_false_lam(lam: OLam) -> bool:
    """Check if lambda is constantly False: λx. False."""
    return isinstance(lam.body, OLit) and lam.body.value is False


def _try_constant_fold(op: str, args: Tuple[OTerm, ...]) -> Optional[OLit]:
    """Try to fold a fully-constant operation."""
    if not all(isinstance(a, OLit) for a in args):
        return None
    vals = [a.value for a in args]  # type: ignore[union-attr]
    try:
        if op == "add" and len(vals) == 2:
            return OLit(vals[0] + vals[1])
        if op in ("mul", "mult") and len(vals) == 2:
            return OLit(vals[0] * vals[1])
        if op == "sub" and len(vals) == 2:
            return OLit(vals[0] - vals[1])
        if op == "floordiv" and len(vals) == 2 and vals[1] != 0:
            return OLit(vals[0] // vals[1])
        if op == "mod" and len(vals) == 2 and vals[1] != 0:
            return OLit(vals[0] % vals[1])
        if op == "pow" and len(vals) == 2:
            return OLit(vals[0] ** vals[1])
        if op == "u_usub" and len(vals) == 1:
            return OLit(-vals[0])
        if op == "u_not" and len(vals) == 1:
            return OLit(not vals[0])
    except (TypeError, ValueError, OverflowError):
        pass
    return None


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D38 partial evaluation rewrites to *term*."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── 1. Identity elimination: op(x, identity) → x ──
    if isinstance(term, OOp) and len(term.args) == 2:
        identity = _IDENTITY.get(term.name)
        if identity is not None:
            for i in range(2):
                arg = term.args[i]
                other = term.args[1 - i]
                if isinstance(arg, OLit) and arg.value == identity:
                    label = f"D38_identity_{term.name}"
                    results.append((other, label))
                    break

    # ── 2. Annihilator: op(x, annihilator) → result ──
    if isinstance(term, OOp) and len(term.args) == 2:
        annihilator = _ANNIHILATOR.get(term.name)
        if annihilator is not None:
            for i in range(2):
                arg = term.args[i]
                if isinstance(arg, OLit) and arg.value == annihilator:
                    result_val = _ANNIHILATOR_RESULT[term.name]
                    results.append((OLit(result_val), "D38_annihilator"))
                    break

    # ── 3. Constant folding ──
    if isinstance(term, OOp):
        folded = _try_constant_fold(term.name, term.args)
        if folded is not None:
            results.append((folded, "D38_constant_fold"))

    # ── 4. Constant conditional: case(True, a, b) → a ──
    if isinstance(term, OCase):
        if isinstance(term.test, OLit):
            if term.test.value is True or term.test.value == 1:
                results.append((term.true_branch, "D38_const_case_true"))
            elif term.test.value is False or term.test.value == 0:
                results.append((term.false_branch, "D38_const_case_false"))

    # ── 5. Identity map: map(λx.x, xs) → xs ──
    if isinstance(term, OMap) and term.filter_pred is None:
        if isinstance(term.transform, OLam) and _is_identity_lam(term.transform):
            results.append((term.collection, "D38_identity_map"))

    # ── 6. Trivial filter: filter_map(λx.True, f, xs) → map(f, xs) ──
    if isinstance(term, OMap) and term.filter_pred is not None:
        if isinstance(term.filter_pred, OLam) and _is_true_lam(term.filter_pred):
            results.append((
                OMap(term.transform, term.collection),
                "D38_trivial_filter",
            ))
        if isinstance(term.filter_pred, OLam) and _is_false_lam(term.filter_pred):
            results.append((OSeq(()), "D38_false_filter"))

    # ── 7. range(0, n, 1) → range(n) ──
    if isinstance(term, OOp) and term.name == "range":
        if len(term.args) == 3:
            start, stop, step = term.args
            if (isinstance(start, OLit) and start.value == 0
                    and isinstance(step, OLit) and step.value == 1):
                results.append((OOp("range", (stop,)), "D38_range_default"))
        if len(term.args) == 2:
            start, stop = term.args
            if isinstance(start, OLit) and start.value == 0:
                results.append((OOp("range", (stop,)), "D38_range_default_start"))

    # ── 8. Double negation: not(not(x)) → x ──
    if (isinstance(term, OOp) and term.name == "u_not" and len(term.args) == 1
            and isinstance(term.args[0], OOp) and term.args[0].name == "u_not"
            and len(term.args[0].args) == 1):
        results.append((term.args[0].args[0], "D38_double_negation"))

    # ── 9. Idempotent ops: and(x, x) → x, or(x, x) → x ──
    if isinstance(term, OOp) and term.name in ("and", "or") and len(term.args) == 2:
        if term.args[0].canon() == term.args[1].canon():
            results.append((term.args[0], "D38_idempotent"))

    # ── 10. fold with empty collection → init ──
    if isinstance(term, OFold):
        if isinstance(term.collection, OSeq) and len(term.collection.elements) == 0:
            results.append((term.init, "D38_fold_empty"))

    # ── 11. map over empty → empty ──
    if isinstance(term, OMap):
        if isinstance(term.collection, OSeq) and len(term.collection.elements) == 0:
            results.append((OSeq(()), "D38_map_empty"))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D38 in reverse: introduce identities, expand constants."""
    results: List[Tuple[OTerm, str]] = []

    # x → x + 0
    if isinstance(term, OVar):
        results.append((OOp("add", (term, OLit(0))), "D38_inv_add_identity"))
        results.append((OOp("mul", (term, OLit(1))), "D38_inv_mul_identity"))

    # xs → map(λx.x, xs)
    if isinstance(term, OVar):
        results.append((
            OMap(OLam(("_x",), OVar("_x")), term),
            "D38_inv_identity_map",
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D38 can potentially rewrite *term*."""
    if isinstance(term, OOp):
        if term.name in _IDENTITY or term.name in _ANNIHILATOR:
            if any(isinstance(a, OLit) for a in term.args):
                return True
        if all(isinstance(a, OLit) for a in term.args):
            return True
        if term.name == "range":
            return True
        if term.name == "u_not" and len(term.args) == 1:
            if isinstance(term.args[0], OOp) and term.args[0].name == "u_not":
                return True
    if isinstance(term, OCase) and isinstance(term.test, OLit):
        return True
    if isinstance(term, OMap):
        if isinstance(term.transform, OLam) and _is_identity_lam(term.transform):
            return True
        if isinstance(term.filter_pred, OLam):
            return True
    if isinstance(term, OFold) and isinstance(term.collection, OSeq):
        return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D38 relevance for bridging *source* → *target*."""
    sc, tc = source.canon(), target.canon()
    s_depth = sc.count("(")
    t_depth = tc.count("(")
    # Partial eval typically reduces complexity
    if s_depth > t_depth + 2:
        return 0.80
    if any(lit in sc for lit in ("0", "1", "True", "False")):
        return 0.60
    if "map(" in sc and "map(" not in tc:
        return 0.50
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
    x, y = OVar("x"), OVar("y")
    xs = OVar("xs")

    # ── Identity elimination ──
    print("D38: identity elimination ...")
    _assert(any(lbl.startswith("D38_identity") for _, lbl in apply(OOp("add", (x, OLit(0))), ctx)),
            "x+0 → x")
    _assert(any(lbl.startswith("D38_identity") for _, lbl in apply(OOp("mul", (x, OLit(1))), ctx)),
            "x*1 → x")

    # ── Annihilator ──
    print("D38: annihilator ...")
    r_ann = apply(OOp("mul", (x, OLit(0))), ctx)
    _assert(any(lbl == "D38_annihilator" for _, lbl in r_ann), "x*0 → 0")
    ann_term = [t for t, lbl in r_ann if lbl == "D38_annihilator"]
    _assert(ann_term and isinstance(ann_term[0], OLit) and ann_term[0].value == 0, "result is 0")

    # ── Constant folding ──
    print("D38: constant folding ...")
    r_cf = apply(OOp("add", (OLit(3), OLit(4))), ctx)
    _assert(any(lbl == "D38_constant_fold" for _, lbl in r_cf), "3+4 constant fold")
    cf_term = [t for t, lbl in r_cf if lbl == "D38_constant_fold"]
    _assert(cf_term and isinstance(cf_term[0], OLit) and cf_term[0].value == 7, "3+4=7")

    # ── Constant conditional ──
    print("D38: constant conditional ...")
    a, b = OVar("a"), OVar("b")
    r_cc = apply(OCase(OLit(True), a, b), ctx)
    _assert(any(lbl == "D38_const_case_true" for _, lbl in r_cc), "case(True,a,b) → a")
    r_cf2 = apply(OCase(OLit(False), a, b), ctx)
    _assert(any(lbl == "D38_const_case_false" for _, lbl in r_cf2), "case(False,a,b) → b")

    # ── Identity map ──
    print("D38: identity map ...")
    id_map = OMap(OLam(("x",), OVar("x")), xs)
    r_im = apply(id_map, ctx)
    _assert(any(lbl == "D38_identity_map" for _, lbl in r_im), "map(id, xs) → xs")

    # ── Trivial filter ──
    print("D38: trivial filter ...")
    true_filt = OMap(OLam(("x",), OVar("x")), xs, filter_pred=OLam(("x",), OLit(True)))
    r_tf = apply(true_filt, ctx)
    _assert(any(lbl == "D38_trivial_filter" for _, lbl in r_tf), "filter(True, xs) → xs")

    # ── range defaults ──
    print("D38: range defaults ...")
    r_range = apply(OOp("range", (OLit(0), OVar("n"), OLit(1))), ctx)
    _assert(any(lbl == "D38_range_default" for _, lbl in r_range), "range(0,n,1) → range(n)")

    # ── Double negation ──
    print("D38: double negation ...")
    dn = OOp("u_not", (OOp("u_not", (x,)),))
    r_dn = apply(dn, ctx)
    _assert(any(lbl == "D38_double_negation" for _, lbl in r_dn), "not(not(x)) → x")

    # ── Idempotent ──
    print("D38: idempotent ...")
    idem = OOp("and", (x, x))
    r_idem = apply(idem, ctx)
    _assert(any(lbl == "D38_idempotent" for _, lbl in r_idem), "and(x,x) → x")

    # ── Fold empty ──
    print("D38: fold empty ...")
    fe = OFold("add", OLit(0), OSeq(()))
    r_fe = apply(fe, ctx)
    _assert(any(lbl == "D38_fold_empty" for _, lbl in r_fe), "fold(add, 0, []) → 0")

    # ── Map empty ──
    print("D38: map empty ...")
    me = OMap(OLam(("x",), OOp("f", (OVar("x"),))), OSeq(()))
    r_me = apply(me, ctx)
    _assert(any(lbl == "D38_map_empty" for _, lbl in r_me), "map(f, []) → []")

    # ── recognizes ──
    print("D38: recognizes ...")
    _assert(recognizes(OOp("add", (x, OLit(0)))), "recognizes add with lit")
    _assert(recognizes(OCase(OLit(True), a, b)), "recognizes const case")
    _assert(not recognizes(OVar("z")), "does not recognise var")

    # ── relevance_score ──
    print("D38: relevance_score ...")
    score = relevance_score(OOp("add", (x, OLit(0))), x)
    _assert(score > 0.3, f"identity elim relevance={score:.2f}")

    print(f"\n{'='*50}")
    print(f"  D38 partial_eval: {_pass} passed, {_fail} failed")
    print(f"{'='*50}")
    if _fail > 0:
        raise SystemExit(1)
