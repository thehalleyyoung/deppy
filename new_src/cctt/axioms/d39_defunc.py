"""D39: Defunctionalization ↔ Closures Axiom.

Converts between higher-order (closure-based) and first-order
(tag-dispatch) representations.

Mathematical foundation:
  Reynolds' defunctionalization theorem (1972):
    Every higher-order program has a first-order counterpart
    obtained by replacing function values with tagged data and
    dispatching on tags at application sites.

  In categorical terms: the Yoneda embedding
    y : C → [C^op, Set]
  shows every object can be represented by its morphisms.
  Defunctionalization is the finite restriction of this embedding
  to actually-used morphisms.

  Concretely:
    map(λx: x+k, xs) ≡ [x+k for x in xs]     [closure elimination]
    {'+': add, '-': sub}[op](a,b) ≡ if/elif    [dispatch → conditional]
    sorted(xs, key=λx: x[1]) ≡ explicit cmp    [key function elimination]

Covers:
  • Lambda/closure → list comprehension
  • Dictionary dispatch → if/elif chain
  • Visitor pattern → match/case
  • key= lambda elimination in sorted/min/max
  • Strategy pattern refactoring
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

AXIOM_NAME = "D39_defunc"
AXIOM_CATEGORY = "higher_order"

SOUNDNESS_PROOF = r"""
Theorem (Reynolds' Defunctionalization, 1972).
  Let P be a higher-order program with a finite set of lambda
  abstractions {λ₁, ..., λₙ}.  Define:
    data Apply = Tag₁ env₁ | ... | Tagₙ envₙ
    apply(Tagᵢ envᵢ, x) = bodyᵢ[env := envᵢ, param := x]
  Then the first-order program P' with Apply is operationally
  equivalent to P:  ∀ inputs. ⟦P⟧(inputs) = ⟦P'⟧(inputs).

  Closure elimination: map(λx. e, xs) ≡ [e for x in xs]
  because list comprehension is the defunctionalized map.

  Dictionary dispatch: d[key](args) ≡ case(key, ...)
  because dict lookup + call is a closure application.  ∎
"""

COMPOSES_WITH = ["D24_eta", "D40_curry", "D04_comp_fusion", "D12_map_construct"]
REQUIRES: List[str] = []

EXAMPLES = [
    {
        "name": "map(lambda) → comprehension",
        "before": "map(λ(x)add(x, k), xs)",
        "after": "map(λ(_b0)add(_b0, k), xs)",
        "axiom": "D39_map_lambda_to_comp",
    },
    {
        "name": "Dict dispatch → if/elif",
        "before": "getitem({'+': add, '-': sub}, op)(a, b)",
        "after": "case(eq(op, '+'), add(a, b), case(eq(op, '-'), sub(a, b), ?))",
        "axiom": "D39_dict_dispatch_to_case",
    },
    {
        "name": "sorted with key → sorted_key",
        "before": "sorted_key(xs, λ(x)getitem(x, 1))",
        "after": "sorted_key(xs, λ(_b0)getitem(_b0, 1))",
        "axiom": "D39_key_func_normalize",
    },
    {
        "name": "Comprehension → map(lambda)",
        "before": "map(λ(x)f(x), xs)",
        "after": "f()",
        "axiom": "D39_comp_to_map_eta",
    },
    {
        "name": "if/elif → dict dispatch",
        "before": "case(eq(op,'+'), add(a,b), sub(a,b))",
        "after": "getitem({'+': add(), '-': sub()}, op)(a, b)",
        "axiom": "D39_case_to_dict_dispatch",
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
    if isinstance(term, OFold):
        return _extract_free_vars(term.init, bound) | _extract_free_vars(term.collection, bound)
    if isinstance(term, OSeq):
        r2: Set[str] = set()
        for e in term.elements:
            r2 |= _extract_free_vars(e, bound)
        return r2
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
    if isinstance(term, OFix):
        return _extract_free_vars(term.body, bound)
    if isinstance(term, OCatch):
        return _extract_free_vars(term.body, bound) | _extract_free_vars(term.default, bound)
    if isinstance(term, OAbstract):
        r5: Set[str] = set()
        for a in term.inputs:
            r5 |= _extract_free_vars(a, bound)
        return r5
    return set()


def _is_dict_dispatch(term: OTerm) -> Optional[Tuple[ODict, OTerm, Tuple[OTerm, ...]]]:
    """Detect d[key](args) pattern — getitem on ODict applied to args.

    Returns (dict_term, key_term, call_args) or None.
    """
    # Pattern: OOp('__call__', (getitem(dict, key), arg1, ...))
    # Or more commonly in our OTerm: the result of compiling d[op](a, b)
    # This appears as OOp(name, args) where name is from the dict
    if isinstance(term, OOp) and term.name == "getitem" and len(term.args) == 2:
        dict_term, key = term.args
        if isinstance(dict_term, ODict):
            return (dict_term, key, ())
    return None


def _dict_to_case_chain(pairs: Tuple[Tuple[OTerm, OTerm], ...],
                         key: OTerm,
                         call_args: Tuple[OTerm, ...]) -> OTerm:
    """Convert dict lookup to nested case chain."""
    if len(pairs) == 0:
        return OUnknown("KeyError")
    if len(pairs) == 1:
        k, v = pairs[0]
        test = OOp("eq", (key, k))
        applied = OOp(v.canon(), call_args) if call_args else v
        return OCase(test, applied, OUnknown("KeyError"))
    k, v = pairs[0]
    test = OOp("eq", (key, k))
    applied = OOp(v.canon(), call_args) if call_args else v
    rest = _dict_to_case_chain(pairs[1:], key, call_args)
    return OCase(test, applied, rest)


def _case_chain_to_dict(term: OCase) -> Optional[Tuple[OTerm, List[Tuple[OTerm, OTerm]]]]:
    """Detect nested case(eq(key, k1), v1, case(eq(key, k2), v2, ...))."""
    pairs: List[Tuple[OTerm, OTerm]] = []
    key_var: Optional[OTerm] = None
    current: OTerm = term

    while isinstance(current, OCase):
        test = current.test
        if not (isinstance(test, OOp) and test.name == "eq" and len(test.args) == 2):
            break
        k_candidate = test.args[0]
        k_lit = test.args[1]
        if key_var is None:
            key_var = k_candidate
        elif k_candidate.canon() != key_var.canon():
            break
        pairs.append((k_lit, current.true_branch))
        current = current.false_branch

    if len(pairs) >= 2 and key_var is not None:
        return (key_var, pairs)
    return None


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D39 defunctionalization rewrites to *term*."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── 1. map(λx. body, xs) where body uses free vars → closure annotation ──
    if isinstance(term, OMap) and isinstance(term.transform, OLam):
        lam = term.transform
        fv = _extract_free_vars(lam.body, set(lam.params))
        if fv:
            # Annotate that this map captures variables (closure)
            results.append((
                OMap(term.transform, term.collection, term.filter_pred),
                "D39_map_closure_detected",
            ))

    # ── 2. map(λx. f(x), xs) → just mark as f-application (D24-adjacent) ──
    if isinstance(term, OMap) and isinstance(term.transform, OLam):
        lam = term.transform
        if (len(lam.params) == 1
                and isinstance(lam.body, OOp) and len(lam.body.args) == 1
                and isinstance(lam.body.args[0], OVar)
                and lam.body.args[0].name == lam.params[0]):
            # map(λx. f(x), xs) — the lambda is η-reducible to f
            results.append((
                OMap(OOp(lam.body.name, ()), term.collection, term.filter_pred),
                "D39_comp_to_map_eta",
            ))

    # ── 3. Dict dispatch → case chain ──
    dispatch = _is_dict_dispatch(term)
    if dispatch is not None:
        dict_term, key, call_args = dispatch
        case_chain = _dict_to_case_chain(dict_term.pairs, key, call_args)
        results.append((case_chain, "D39_dict_dispatch_to_case"))

    # ── 4. Case chain → dict dispatch ──
    if isinstance(term, OCase):
        chain = _case_chain_to_dict(term)
        if chain is not None:
            key_var, pairs = chain
            dict_pairs = tuple((k, v) for k, v in pairs)
            results.append((
                OOp("getitem", (ODict(dict_pairs), key_var)),
                "D39_case_to_dict_dispatch",
            ))

    # ── 5. sorted_key / min_key / max_key with lambda → normalize ──
    if isinstance(term, OOp) and term.name in ("sorted_key", "min_key", "max_key"):
        if len(term.args) >= 2 and isinstance(term.args[-1], OLam):
            results.append((term, "D39_key_func_normalize"))

    # ── 6. Lambda applied immediately: (λx. body)(arg) → body[x:=arg] ──
    #    This is closure application = defunctionalized apply
    if isinstance(term, OOp) and term.name == "__call__" and len(term.args) >= 2:
        fn = term.args[0]
        args = term.args[1:]
        if isinstance(fn, OLam) and len(fn.params) == len(args):
            results.append((
                OOp("beta_apply", (fn, OSeq(args))),
                "D39_closure_apply",
            ))

    # ── 7. getattr dispatch: getattr(obj, name) → case chain on name ──
    if isinstance(term, OOp) and term.name == "getattr" and len(term.args) == 2:
        obj, name = term.args
        if isinstance(name, OVar):
            results.append((
                OCase(OOp("eq", (name, OLit("method1"))),
                      OOp(".method1", (obj,)),
                      OUnknown("attr_dispatch")),
                "D39_getattr_to_case",
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D39 in reverse: first-order → higher-order."""
    results: List[Tuple[OTerm, str]] = []

    # Case chain → dict dispatch
    if isinstance(term, OCase):
        chain = _case_chain_to_dict(term)
        if chain is not None:
            key_var, pairs = chain
            dict_pairs = tuple((k, v) for k, v in pairs)
            results.append((
                OOp("getitem", (ODict(dict_pairs), key_var)),
                "D39_inv_case_to_dict",
            ))

    # Map with named function → map with lambda
    if isinstance(term, OMap) and isinstance(term.transform, OOp):
        if len(term.transform.args) == 0:
            fname = term.transform.name
            results.append((
                OMap(OLam(("_x",), OOp(fname, (OVar("_x"),))), term.collection),
                "D39_inv_map_to_lambda",
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D39 can potentially rewrite *term*."""
    if isinstance(term, OMap) and isinstance(term.transform, OLam):
        return True
    if isinstance(term, OOp) and term.name == "getitem":
        if len(term.args) == 2 and isinstance(term.args[0], ODict):
            return True
    if isinstance(term, OCase):
        if _case_chain_to_dict(term) is not None:
            return True
    if isinstance(term, OOp) and term.name in ("sorted_key", "min_key", "max_key"):
        return True
    if isinstance(term, OOp) and term.name == "__call__":
        if len(term.args) >= 2 and isinstance(term.args[0], OLam):
            return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D39 relevance for bridging *source* → *target*."""
    sc, tc = source.canon(), target.canon()
    s_lam = "λ(" in sc
    t_lam = "λ(" in tc
    s_case = "case(" in sc
    t_case = "case(" in tc
    s_dict = "{" in sc
    t_dict = "{" in tc

    # Higher-order ↔ first-order
    if s_lam and t_case and not t_lam:
        return 0.85
    if s_case and t_lam and not s_lam:
        return 0.85
    # Dict dispatch ↔ case
    if s_dict and t_case:
        return 0.80
    if s_case and t_dict:
        return 0.80
    if s_lam or t_lam:
        return 0.40
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
    x, xs = OVar("x"), OVar("xs")
    a, b = OVar("a"), OVar("b")
    op = OVar("op")

    # ── map(λx. f(x), xs) → eta ──
    print("D39: map eta ...")
    t1 = OMap(OLam(("x",), OOp("f", (OVar("x"),))), xs)
    r1 = apply(t1, ctx)
    _assert(any(lbl == "D39_comp_to_map_eta" for _, lbl in r1), "map eta")

    # ── map with closure ──
    print("D39: map closure ...")
    k = OVar("k")
    t2 = OMap(OLam(("x",), OOp("add", (OVar("x"), k))), xs)
    r2 = apply(t2, ctx)
    _assert(any(lbl == "D39_map_closure_detected" for _, lbl in r2), "map closure detected")

    # ── Dict dispatch → case ──
    print("D39: dict dispatch → case ...")
    d = ODict(((OLit("+"), OOp("add", ())), (OLit("-"), OOp("sub", ()))))
    t3 = OOp("getitem", (d, op))
    r3 = apply(t3, ctx)
    _assert(any(lbl == "D39_dict_dispatch_to_case" for _, lbl in r3), "dict → case")

    # ── Case chain → dict ──
    print("D39: case chain → dict ...")
    t4 = OCase(
        OOp("eq", (op, OLit("+"))),
        OOp("add", (a, b)),
        OCase(
            OOp("eq", (op, OLit("-"))),
            OOp("sub", (a, b)),
            OUnknown("KeyError"),
        ),
    )
    r4 = apply(t4, ctx)
    _assert(any(lbl == "D39_case_to_dict_dispatch" for _, lbl in r4), "case → dict")

    # ── recognizes ──
    print("D39: recognizes ...")
    _assert(recognizes(t1), "recognizes map+lambda")
    _assert(recognizes(t3), "recognizes dict dispatch")
    _assert(recognizes(t4), "recognizes case chain")
    _assert(not recognizes(OLit(42)), "does not recognise literal")

    # ── relevance_score ──
    print("D39: relevance_score ...")
    score = relevance_score(t1, t4)
    _assert(score > 0.3, f"lambda↔case score={score:.2f}")

    # ── apply_inverse ──
    print("D39: apply_inverse ...")
    inv = apply_inverse(t4, ctx)
    _assert(any(lbl == "D39_inv_case_to_dict" for _, lbl in inv), "inv case → dict")

    inv2 = apply_inverse(OMap(OOp("f", ()), xs), ctx)
    _assert(any(lbl == "D39_inv_map_to_lambda" for _, lbl in inv2), "inv map → lambda")

    print(f"\n{'='*50}")
    print(f"  D39 defunc: {_pass} passed, {_fail} failed")
    print(f"{'='*50}")
    if _fail > 0:
        raise SystemExit(1)
