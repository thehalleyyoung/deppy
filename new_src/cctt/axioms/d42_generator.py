"""D42: Generator ↔ List Materialization Axiom.

Converts between lazy (generator/iterator) and eager (list) evaluation.

Mathematical foundation:
  For terminating computations over finite collections, lazy and eager
  evaluation are denotationally equivalent:
    ⟦gen(f, xs)⟧ = ⟦[f(x) for x in xs]⟧
  when the generator is fully consumed.

  This is the isomorphism between the free monad (lazy) and the
  list monad (eager) restricted to terminating computations:
    Stream(A) ≅ List(A)   for finite, terminating streams.

  Specifically:
    (x for x in xs if p(x))  ≡  [x for x in xs if p(x)]  [single consumption]
    yield-loop  ≡  append-loop + return                     [generator unfolding]
    itertools.chain(a, b)  ≡  a + b                        [for lists]
    itertools.islice(g, n)  ≡  list(g)[:n]                 [for finite g]
    next(iter(xs))  ≡  xs[0]                               [for sequences]
    sum(gen)  ≡  sum(list(gen))                             [fold over gen = fold over list]
    any(gen)  ≡  any(list(gen))                             [short-circuit preserved]

Covers:
  • Generator expression ↔ list comprehension
  • yield loop ↔ append loop
  • itertools.chain ↔ list concatenation
  • itertools.islice ↔ slice
  • next(iter(xs)) ↔ xs[0]
  • Fold over generator ↔ fold over materialized list
  • Lazy/eager isomorphism for terminating computations
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

AXIOM_NAME = "D42_generator"
AXIOM_CATEGORY = "higher_order"

SOUNDNESS_PROOF = r"""
Theorem (Lazy-Eager Isomorphism for Terminating Computations).
  Let f : A → B be a total function and xs : List(A) be finite.
  Then:
    toList(genMap(f, fromList(xs))) = map(f, xs)
  where genMap is the lazy map and map is the eager map.

  More generally, for any fold φ with monoid (M, ⊕, e):
    φ(genMap(f, xs)) = φ(map(f, xs))
  because the fold forces all elements regardless of laziness.

  Generator ↔ List Comprehension:
    (e for x in xs if p(x))  ≡  [e for x in xs if p(x)]
  when the generator is consumed exactly once.

  itertools equivalences (for finite iterables):
    chain(a, b) ≡ a + b         by list concatenation
    islice(g, n) ≡ list(g)[:n]  by prefix extraction
    next(iter(xs)) ≡ xs[0]      by head extraction

  Yield loop unfolding:
    def gen(): for x in xs: yield f(x)
    ≡
    def eager(): result = []; for x in xs: result.append(f(x)); return result
  by induction on xs.  ∎
"""

COMPOSES_WITH = ["D06_lazy_eager", "D04_comp_fusion", "D01_fold_unfold", "D38_partial_eval"]
REQUIRES: List[str] = []

EXAMPLES = [
    {
        "name": "Generator → list comprehension",
        "before": "gen_expr(f, xs)",
        "after": "map(f, xs)",
        "axiom": "D42_gen_to_list",
    },
    {
        "name": "List comprehension → generator",
        "before": "map(f, xs)",
        "after": "gen_expr(f, xs)",
        "axiom": "D42_list_to_gen",
    },
    {
        "name": "chain → concat",
        "before": "itertools.chain(a, b)",
        "after": "concat(a, b)",
        "axiom": "D42_chain_to_concat",
    },
    {
        "name": "next(iter(xs)) → xs[0]",
        "before": "next(iter(xs))",
        "after": "getitem(xs, 0)",
        "axiom": "D42_next_iter_to_index",
    },
    {
        "name": "islice → slice",
        "before": "itertools.islice(xs, n)",
        "after": "slice(xs, 0, n)",
        "axiom": "D42_islice_to_slice",
    },
    {
        "name": "sum(gen) → fold",
        "before": "sum(gen_expr(f, xs))",
        "after": "fold[add](0, map(f, xs))",
        "axiom": "D42_sum_gen_to_fold",
    },
    {
        "name": "list(gen) materialisation",
        "before": "list(gen_expr(f, xs))",
        "after": "map(f, xs)",
        "axiom": "D42_list_materialise",
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

_CHAIN_NAMES: FrozenSet[str] = frozenset({
    "itertools.chain", "chain", "itertools_chain",
})

_ISLICE_NAMES: FrozenSet[str] = frozenset({
    "itertools.islice", "islice", "itertools_islice",
})

_GEN_NAMES: FrozenSet[str] = frozenset({
    "gen_expr", "generator", "genexpr",
})

_FOLD_CONSUMERS: FrozenSet[str] = frozenset({
    "sum", "any", "all", "min", "max", "sorted", "list", "tuple", "set",
    "frozenset", "len",
})


def _is_gen_expr(term: OTerm) -> bool:
    """Check if term represents a generator expression."""
    if isinstance(term, OOp) and term.name in _GEN_NAMES:
        return True
    # OMap with a marker for generator
    if isinstance(term, OMap):
        return True
    return False


def _is_iter_call(term: OTerm) -> Optional[OTerm]:
    """Detect iter(xs) → return xs."""
    if isinstance(term, OOp) and term.name == "iter" and len(term.args) == 1:
        return term.args[0]
    return None


def _is_next_call(term: OTerm) -> Optional[OTerm]:
    """Detect next(x) → return x."""
    if isinstance(term, OOp) and term.name == "next" and len(term.args) == 1:
        return term.args[0]
    return None


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D42 generator↔list materialisation rewrites to *term*."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── 1. chain(a, b) → concat(a, b) ──
    if isinstance(term, OOp) and term.name in _CHAIN_NAMES:
        if len(term.args) == 2:
            results.append((
                OOp("concat", term.args),
                "D42_chain_to_concat",
            ))
        elif len(term.args) > 2:
            # chain(a, b, c) → concat(concat(a, b), c)
            result = term.args[0]
            for arg in term.args[1:]:
                result = OOp("concat", (result, arg))
            results.append((result, "D42_chain_to_concat"))

    # ── 2. concat(a, b) → chain(a, b) ──
    if isinstance(term, OOp) and term.name == "concat" and len(term.args) == 2:
        results.append((
            OOp("itertools.chain", term.args),
            "D42_concat_to_chain",
        ))

    # ── 3. next(iter(xs)) → getitem(xs, 0) ──
    next_arg = _is_next_call(term)
    if next_arg is not None:
        iter_arg = _is_iter_call(next_arg)
        if iter_arg is not None:
            results.append((
                OOp("getitem", (iter_arg, OLit(0))),
                "D42_next_iter_to_index",
            ))

    # ── 4. getitem(xs, 0) → next(iter(xs)) ──
    if isinstance(term, OOp) and term.name == "getitem" and len(term.args) == 2:
        xs, idx = term.args
        if isinstance(idx, OLit) and idx.value == 0:
            results.append((
                OOp("next", (OOp("iter", (xs,)),)),
                "D42_index_to_next_iter",
            ))

    # ── 5. islice(xs, n) → slice(xs, 0, n) ──
    if isinstance(term, OOp) and term.name in _ISLICE_NAMES:
        if len(term.args) == 2:
            xs, n = term.args
            results.append((
                OOp("slice", (xs, OLit(0), n)),
                "D42_islice_to_slice",
            ))
        elif len(term.args) == 3:
            xs, start, stop = term.args
            results.append((
                OOp("slice", (xs, start, stop)),
                "D42_islice_to_slice",
            ))

    # ── 6. slice(xs, 0, n) → islice(xs, n) ──
    if isinstance(term, OOp) and term.name == "slice" and len(term.args) == 3:
        xs, start, stop = term.args
        if isinstance(start, OLit) and start.value == 0:
            results.append((
                OOp("itertools.islice", (xs, stop)),
                "D42_slice_to_islice",
            ))

    # ── 7. list(gen_expr(f, xs)) → map(f, xs) ──
    if isinstance(term, OOp) and term.name == "list" and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name in _GEN_NAMES:
            if len(inner.args) == 2:
                f, xs = inner.args
                results.append((OMap(f, xs), "D42_list_materialise"))
            elif len(inner.args) == 1:
                results.append((inner.args[0], "D42_list_materialise"))
        if isinstance(inner, OMap):
            results.append((inner, "D42_list_materialise"))

    # ── 8. sum/any/all over generator → fold ──
    if isinstance(term, OOp) and term.name in ("sum", "any", "all") and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OMap) and inner.filter_pred is None:
            fold_op = {"sum": "add", "any": "or", "all": "and"}[term.name]
            fold_init = {"sum": OLit(0), "any": OLit(False), "all": OLit(True)}[term.name]
            results.append((
                OFold(fold_op, fold_init, OMap(inner.transform, inner.collection)),
                f"D42_{term.name}_gen_to_fold",
            ))
        if isinstance(inner, OOp) and inner.name in _GEN_NAMES and len(inner.args) == 2:
            fold_op = {"sum": "add", "any": "or", "all": "and"}[term.name]
            fold_init = {"sum": OLit(0), "any": OLit(False), "all": OLit(True)}[term.name]
            f_term, xs = inner.args
            results.append((
                OFold(fold_op, fold_init, OMap(f_term, xs)),
                f"D42_{term.name}_gen_to_fold",
            ))

    # ── 9. Yield loop → map: OFold-based append pattern ──
    if isinstance(term, OFold) and term.op_name in (".append", "append"):
        results.append((
            OMap(OLam(("_e",), OVar("_e")), term.collection),
            "D42_yield_to_map",
        ))

    # ── 10. map(f, xs) → gen_expr(f, xs) — eagerness to laziness ──
    if isinstance(term, OMap) and term.filter_pred is None:
        results.append((
            OOp("gen_expr", (term.transform, term.collection)),
            "D42_list_to_gen",
        ))

    # ── 11. tuple(gen) → tuple(list(gen)) simplification ──
    if isinstance(term, OOp) and term.name == "tuple" and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OMap):
            results.append((
                OOp("tuple", (inner,)),
                "D42_tuple_materialise",
            ))

    # ── 12. sorted(gen) → sorted(list(gen)) ──
    if isinstance(term, OOp) and term.name == "sorted" and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name in _GEN_NAMES:
            if len(inner.args) == 2:
                f, xs = inner.args
                results.append((
                    OOp("sorted", (OMap(f, xs),)),
                    "D42_sorted_materialise",
                ))

    # ── 13. enumerate → zip(range, xs) ──
    if isinstance(term, OOp) and term.name == "enumerate" and len(term.args) == 1:
        xs = term.args[0]
        results.append((
            OOp("zip", (OOp("range", (OOp("len", (xs,)),)), xs)),
            "D42_enumerate_to_zip_range",
        ))

    # ── 14. zip(range(len(xs)), xs) → enumerate(xs) ──
    if isinstance(term, OOp) and term.name == "zip" and len(term.args) == 2:
        first, second = term.args
        if (isinstance(first, OOp) and first.name == "range" and len(first.args) == 1
                and isinstance(first.args[0], OOp) and first.args[0].name == "len"
                and len(first.args[0].args) == 1
                and first.args[0].args[0].canon() == second.canon()):
            results.append((
                OOp("enumerate", (second,)),
                "D42_zip_range_to_enumerate",
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D42 in reverse: list → generator."""
    results: List[Tuple[OTerm, str]] = []

    # map(f, xs) → gen_expr(f, xs)
    if isinstance(term, OMap) and term.filter_pred is None:
        results.append((
            OOp("gen_expr", (term.transform, term.collection)),
            "D42_inv_list_to_gen",
        ))

    # concat → chain
    if isinstance(term, OOp) and term.name == "concat" and len(term.args) == 2:
        results.append((
            OOp("itertools.chain", term.args),
            "D42_inv_concat_to_chain",
        ))

    # getitem(xs, 0) → next(iter(xs))
    if isinstance(term, OOp) and term.name == "getitem" and len(term.args) == 2:
        if isinstance(term.args[1], OLit) and term.args[1].value == 0:
            results.append((
                OOp("next", (OOp("iter", (term.args[0],)),)),
                "D42_inv_index_to_next",
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D42 can potentially rewrite *term*."""
    if isinstance(term, OOp):
        if term.name in _CHAIN_NAMES | _ISLICE_NAMES | _GEN_NAMES:
            return True
        if term.name == "next" and len(term.args) == 1:
            return True
        if term.name == "list" and len(term.args) == 1:
            return True
        if term.name in _FOLD_CONSUMERS and len(term.args) == 1:
            return True
        if term.name == "concat" and len(term.args) == 2:
            return True
        if term.name == "getitem" and len(term.args) == 2:
            if isinstance(term.args[1], OLit) and term.args[1].value == 0:
                return True
        if term.name == "slice":
            return True
        if term.name == "enumerate":
            return True
        if term.name == "zip" and len(term.args) == 2:
            return True
    if isinstance(term, OMap):
        return True
    if isinstance(term, OFold) and term.op_name in (".append", "append"):
        return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D42 relevance for bridging *source* → *target*."""
    sc, tc = source.canon(), target.canon()
    s_gen = any(name in sc for name in ("gen_expr", "chain", "islice", "iter("))
    t_gen = any(name in tc for name in ("gen_expr", "chain", "islice", "iter("))
    s_list = "map(" in sc or "[" in sc or "concat(" in sc
    t_list = "map(" in tc or "[" in tc or "concat(" in tc

    # Generator ↔ list
    if s_gen and t_list:
        return 0.90
    if s_list and t_gen:
        return 0.90
    if s_gen or t_gen:
        return 0.60
    if s_list and t_list:
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
    xs, ys = OVar("xs"), OVar("ys")
    f_lam = OLam(("x",), OOp("f", (OVar("x"),)))
    n = OVar("n")

    # ── chain → concat ──
    print("D42: chain → concat ...")
    t1 = OOp("itertools.chain", (xs, ys))
    r1 = apply(t1, ctx)
    _assert(any(lbl == "D42_chain_to_concat" for _, lbl in r1), "chain → concat")

    # ── concat → chain ──
    print("D42: concat → chain ...")
    t2 = OOp("concat", (xs, ys))
    r2 = apply(t2, ctx)
    _assert(any(lbl == "D42_concat_to_chain" for _, lbl in r2), "concat → chain")

    # ── next(iter(xs)) → xs[0] ──
    print("D42: next(iter) → index ...")
    t3 = OOp("next", (OOp("iter", (xs,)),))
    r3 = apply(t3, ctx)
    _assert(any(lbl == "D42_next_iter_to_index" for _, lbl in r3), "next(iter) → index")

    # ── xs[0] → next(iter(xs)) ──
    print("D42: index → next(iter) ...")
    t4 = OOp("getitem", (xs, OLit(0)))
    r4 = apply(t4, ctx)
    _assert(any(lbl == "D42_index_to_next_iter" for _, lbl in r4), "index → next(iter)")

    # ── islice → slice ──
    print("D42: islice → slice ...")
    t5 = OOp("itertools.islice", (xs, n))
    r5 = apply(t5, ctx)
    _assert(any(lbl == "D42_islice_to_slice" for _, lbl in r5), "islice → slice")

    # ── slice → islice ──
    print("D42: slice → islice ...")
    t6 = OOp("slice", (xs, OLit(0), n))
    r6 = apply(t6, ctx)
    _assert(any(lbl == "D42_slice_to_islice" for _, lbl in r6), "slice → islice")

    # ── list(gen_expr(f, xs)) → map(f, xs) ──
    print("D42: list materialise ...")
    t7 = OOp("list", (OOp("gen_expr", (f_lam, xs)),))
    r7 = apply(t7, ctx)
    _assert(any(lbl == "D42_list_materialise" for _, lbl in r7), "list materialise")

    # ── sum(map(f, xs)) → fold ──
    print("D42: sum gen → fold ...")
    t8 = OOp("sum", (OMap(f_lam, xs),))
    r8 = apply(t8, ctx)
    _assert(any(lbl == "D42_sum_gen_to_fold" for _, lbl in r8), "sum gen → fold")

    # ── map → gen_expr ──
    print("D42: map → gen ...")
    t9 = OMap(f_lam, xs)
    r9 = apply(t9, ctx)
    _assert(any(lbl == "D42_list_to_gen" for _, lbl in r9), "map → gen")

    # ── enumerate ↔ zip(range) ──
    print("D42: enumerate ↔ zip(range) ...")
    t10 = OOp("enumerate", (xs,))
    r10 = apply(t10, ctx)
    _assert(any(lbl == "D42_enumerate_to_zip_range" for _, lbl in r10), "enumerate → zip(range)")

    t11 = OOp("zip", (OOp("range", (OOp("len", (xs,)),)), xs))
    r11 = apply(t11, ctx)
    _assert(any(lbl == "D42_zip_range_to_enumerate" for _, lbl in r11), "zip(range) → enumerate")

    # ── recognizes ──
    print("D42: recognizes ...")
    _assert(recognizes(t1), "recognizes chain")
    _assert(recognizes(t3), "recognizes next")
    _assert(recognizes(t5), "recognizes islice")
    _assert(recognizes(t9), "recognizes map")
    _assert(not recognizes(OLit(42)), "does not recognise literal")

    # ── relevance_score ──
    print("D42: relevance_score ...")
    score = relevance_score(t1, t2)
    _assert(score > 0.5, f"chain↔concat score={score:.2f}")

    # ── apply_inverse ──
    print("D42: apply_inverse ...")
    inv = apply_inverse(t9, ctx)
    _assert(any(lbl == "D42_inv_list_to_gen" for _, lbl in inv), "inv list → gen")

    inv2 = apply_inverse(t2, ctx)
    _assert(any(lbl == "D42_inv_concat_to_chain" for _, lbl in inv2), "inv concat → chain")

    print(f"\n{'='*50}")
    print(f"  D42 generator: {_pass} passed, {_fail} failed")
    print(f"{'='*50}")
    if _fail > 0:
        raise SystemExit(1)
