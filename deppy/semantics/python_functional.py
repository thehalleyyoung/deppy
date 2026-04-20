"""
Deppy Formal Semantics — Functional Combinators and Algebraic Laws
=====================================================================

Formal axioms for Python's functional combinators from the ``builtins``,
``functools``, ``itertools``, and ``operator`` modules.  Each axiom is a
:class:`FormalAxiomEntry` with a machine-checkable :class:`Judgment`.

Monograph references
--------------------
- Ch XX:  Functional Combinators and Algebraic Laws of the Standard Library
- Ch 11:  Generators — free monad over yield (itertools as derived forms)
- Ch 20:  Comprehensions — map/filter correspondence
- Appendix A: typing rules for higher-order operations

Architecture
------------
MapFilterSemantics     — map, filter, zip, enumerate as categorical constructs
ReduceSemantics        — functools.reduce as left fold / catamorphism
ItertoolsSemantics     — chain, product, groupby, permutations, accumulate, …
FunctoolsSemantics     — lru_cache, partial, singledispatch, wraps, total_ordering
OperatorSemantics      — operator module: first-class functions for Python ops

``all_functional_axioms()`` collects every axiom for use by the proof kernel.
"""
from __future__ import annotations

from deppy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    PyObjType, PyIntType, PyCallableType, PyListType,
    PyBoolType, PyNoneType, PyStrType, PyTupleType,
    Var, Literal,
    RefinementType,
)
from deppy.core.formal_ops import (
    Op, OpCall, FormalAxiomEntry, formal_eq, formal_check,
    op_add, op_mul, op_eq, op_len,
    op_map, op_filter, op_fold,
    op_sorted, op_reversed,
    op_le, op_lt, op_ge, op_and, op_not,
    op_getitem,
)


# ── shorthand helpers ─────────────────────────────────────────────

_E = Context()  # empty context
_MODULE = "python.functional"


def _v(name: str) -> Var:
    return Var(name)


def _lit(value: object) -> Literal:
    return Literal(value=value)


def _int_lit(n: int) -> Literal:
    return Literal(value=n)


def _bool_lit(b: bool) -> Literal:
    return Literal(value=b)


def _str_lit(s: str) -> Literal:
    return Literal(value=s)


def _opcall(name: str, *args: SynTerm, module: str = "") -> OpCall:
    return OpCall(Op(name, module), tuple(args))


def _min_op(a: SynTerm, b: SynTerm) -> OpCall:
    return _opcall("min", a, b)


def _list_op(a: SynTerm) -> OpCall:
    return _opcall("list", a)


def _all_op(a: SynTerm) -> OpCall:
    return _opcall("all", a)


def _concat_op(a: SynTerm, b: SynTerm) -> OpCall:
    """List concatenation (xs + ys)."""
    return op_add(a, b)


# ── local Op constructors for stdlib modules ─────────────────────

def _op_reduce(f: SynTerm, xs: SynTerm, z: SynTerm) -> OpCall:
    return OpCall(Op("reduce", "functools"), (f, xs, z))


def _op_reduce_no_init(f: SynTerm, xs: SynTerm) -> OpCall:
    return OpCall(Op("reduce", "functools"), (f, xs))


def _op_chain(xs: SynTerm, ys: SynTerm) -> OpCall:
    return OpCall(Op("chain", "itertools"), (xs, ys))


def _op_chain_from_iterable(xss: SynTerm) -> OpCall:
    return OpCall(Op("chain.from_iterable", "itertools"), (xss,))


def _op_product(xs: SynTerm, ys: SynTerm) -> OpCall:
    return OpCall(Op("product", "itertools"), (xs, ys))


def _op_product_repeat(xs: SynTerm, n: SynTerm) -> OpCall:
    return OpCall(Op("product", "itertools"), (xs,),
                  kwargs=(("repeat", n),))


def _op_groupby(xs: SynTerm, key: SynTerm) -> OpCall:
    return OpCall(Op("groupby", "itertools"), (xs, key))


def _op_permutations(xs: SynTerm, r: SynTerm) -> OpCall:
    return OpCall(Op("permutations", "itertools"), (xs, r))


def _op_combinations(xs: SynTerm, r: SynTerm) -> OpCall:
    return OpCall(Op("combinations", "itertools"), (xs, r))


def _op_combinations_wr(xs: SynTerm, r: SynTerm) -> OpCall:
    return OpCall(Op("combinations_with_replacement", "itertools"), (xs, r))


def _op_accumulate(xs: SynTerm, f: SynTerm, z: SynTerm) -> OpCall:
    return OpCall(Op("accumulate", "itertools"), (xs, f),
                  kwargs=(("initial", z),))


def _op_accumulate_no_init(xs: SynTerm, f: SynTerm) -> OpCall:
    return OpCall(Op("accumulate", "itertools"), (xs, f))


def _op_islice(xs: SynTerm, n: SynTerm) -> OpCall:
    return OpCall(Op("islice", "itertools"), (xs, n))


def _op_takewhile(p: SynTerm, xs: SynTerm) -> OpCall:
    return OpCall(Op("takewhile", "itertools"), (p, xs))


def _op_dropwhile(p: SynTerm, xs: SynTerm) -> OpCall:
    return OpCall(Op("dropwhile", "itertools"), (p, xs))


def _op_repeat(x: SynTerm, n: SynTerm) -> OpCall:
    return OpCall(Op("repeat", "itertools"), (x, n))


def _op_cycle(xs: SynTerm) -> OpCall:
    return OpCall(Op("cycle", "itertools"), (xs,))


def _op_starmap(f: SynTerm, xs: SynTerm) -> OpCall:
    return OpCall(Op("starmap", "itertools"), (f, xs))


def _op_zip_longest(xs: SynTerm, ys: SynTerm, fill: SynTerm) -> OpCall:
    return OpCall(Op("zip_longest", "itertools"), (xs, ys),
                  kwargs=(("fillvalue", fill),))


def _op_partial(f: SynTerm, a: SynTerm) -> OpCall:
    return OpCall(Op("partial", "functools"), (f, a))


def _op_lru_cache(f: SynTerm) -> OpCall:
    return OpCall(Op("lru_cache", "functools"), (f,))


def _op_wraps(f: SynTerm, g: SynTerm) -> OpCall:
    return OpCall(Op("wraps", "functools"), (f, g))


def _op_total_ordering(cls: SynTerm) -> OpCall:
    return OpCall(Op("total_ordering", "functools"), (cls,))


def _op_singledispatch(f: SynTerm) -> OpCall:
    return OpCall(Op("singledispatch", "functools"), (f,))


def _op_zip(xs: SynTerm, ys: SynTerm) -> OpCall:
    return OpCall(Op("zip"), (xs, ys))


def _op_zip_unzip(xs: SynTerm, ys: SynTerm) -> OpCall:
    return OpCall(Op("zip_star"), (xs, ys))


def _op_enumerate(xs: SynTerm) -> OpCall:
    return OpCall(Op("enumerate"), (xs,))


def _op_enumerate_start(xs: SynTerm, k: SynTerm) -> OpCall:
    return OpCall(Op("enumerate"), (xs,), kwargs=(("start", k),))


def _op_sum(xs: SynTerm) -> OpCall:
    return OpCall(Op("sum"), (xs,))


def _op_prod(xs: SynTerm) -> OpCall:
    return OpCall(Op("prod", "math"), (xs,))


def _op_str_join(xs: SynTerm) -> OpCall:
    return _opcall("str.join", _str_lit(""), xs)


def _op_id(x: SynTerm) -> OpCall:
    return _opcall("id_func", x)


def _op_compose(f: SynTerm, g: SynTerm) -> OpCall:
    return _opcall("compose", f, g)


def _op_slice(xs: SynTerm, stop: SynTerm) -> OpCall:
    return _opcall("slice_to", xs, stop)


def _op_apply(f: SynTerm, x: SynTerm) -> OpCall:
    return _opcall("apply1", f, x)


def _op_factorial(n: SynTerm) -> OpCall:
    return _opcall("factorial", n)


def _op_falling_factorial(n: SynTerm, r: SynTerm) -> OpCall:
    return _opcall("falling_factorial", n, r)


def _op_choose(n: SynTerm, r: SynTerm) -> OpCall:
    return _opcall("choose", n, r)


def _op_choose_wr(n: SynTerm, r: SynTerm) -> OpCall:
    return _opcall("choose_with_rep", n, r)


def _op_pow(base: SynTerm, exp: SynTerm) -> OpCall:
    return _opcall("pow", base, exp)


def _op_getattr(obj: SynTerm, attr: SynTerm) -> OpCall:
    return _opcall("getattr", obj, attr)


def _op_operator(name: str, *args: SynTerm) -> OpCall:
    return OpCall(Op(name, "operator"), tuple(args))


def _op_itemgetter(k: SynTerm) -> OpCall:
    return OpCall(Op("itemgetter", "operator"), (k,))


def _op_itemgetter2(k1: SynTerm, k2: SynTerm) -> OpCall:
    return OpCall(Op("itemgetter", "operator"), (k1, k2))


def _op_attrgetter(attr: SynTerm) -> OpCall:
    return OpCall(Op("attrgetter", "operator"), (attr,))


def _op_methodcaller(name: SynTerm, *args: SynTerm) -> OpCall:
    return OpCall(Op("methodcaller", "operator"), (name, *args))


# ═══════════════════════════════════════════════════════════════════
# 1. Map / Filter / Zip Functor Laws
# ═══════════════════════════════════════════════════════════════════

class MapFilterSemantics:
    """map, filter, zip as categorical constructs.

    ``map`` is a functor from (Py → Py) to (List Py → List Py),
    ``filter`` is a sub-functor preserving order, ``zip`` is the
    categorical product on iterables, and ``enumerate`` is a
    natural transformation adding index information.
    """

    def map_axioms(self) -> list[FormalAxiomEntry]:
        """Functor laws for map plus length preservation and pointwise semantics.

        Axioms:
        - map(id, xs) == xs  [identity]
        - map(f∘g, xs) == map(f, map(g, xs))  [composition / functor law]
        - len(list(map(f, xs))) == len(xs)  [length preservation]
        - map(f, []) == []  [empty case]
        - list(map(f, [x1,...,xn])) == [f(x1),...,f(xn)]  [pointwise]
        """
        f, g = _v("f"), _v("g")
        xs = _v("xs")
        x = _v("x")
        axioms: list[FormalAxiomEntry] = []

        # identity: map(id, xs) == xs
        axioms.append(FormalAxiomEntry(
            name="map_identity",
            module=_MODULE,
            params=[("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                _list_op(op_map(_v("id_func"), xs)),
                xs,
                PyListType(),
            ),
            description="map(id, xs) == xs  (functor identity law)",
        ))

        # composition: map(f∘g, xs) == map(f, map(g, xs))
        axioms.append(FormalAxiomEntry(
            name="map_composition",
            module=_MODULE,
            params=[
                ("f", PyCallableType()),
                ("g", PyCallableType()),
                ("xs", PyListType()),
            ],
            conclusion=formal_eq(
                _E,
                op_map(_op_compose(f, g), xs),
                op_map(f, op_map(g, xs)),
                PyListType(),
            ),
            description="map(f∘g, xs) == map(f, map(g, xs))  (functor composition law)",
        ))

        # length preservation: len(list(map(f, xs))) == len(xs)
        axioms.append(FormalAxiomEntry(
            name="map_length_preservation",
            module=_MODULE,
            params=[("f", PyCallableType()), ("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                op_len(_list_op(op_map(f, xs))),
                op_len(xs),
                PyIntType(),
            ),
            description="len(list(map(f, xs))) == len(xs)",
        ))

        # empty case: map(f, []) == []
        axioms.append(FormalAxiomEntry(
            name="map_empty",
            module=_MODULE,
            params=[("f", PyCallableType())],
            conclusion=formal_eq(
                _E,
                _list_op(op_map(f, _lit([]))),
                _lit([]),
                PyListType(),
            ),
            description="map(f, []) == []",
        ))

        # pointwise: map(f, [x]) == [f(x)]
        axioms.append(FormalAxiomEntry(
            name="map_singleton",
            module=_MODULE,
            params=[("f", PyCallableType()), ("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                _list_op(op_map(f, _opcall("singleton_list", x))),
                _opcall("singleton_list", _op_apply(f, x)),
                PyListType(),
            ),
            description="list(map(f, [x])) == [f(x)]  (pointwise, singleton case)",
        ))

        return axioms

    def filter_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for filter as an order-preserving sub-functor.

        Axioms:
        - filter(lambda x: True, xs) == xs  [identity filter]
        - filter(p1 ∧ p2, xs) == filter(p2, filter(p1, xs))  [conjunction]
        - len(list(filter(p, xs))) <= len(xs)  [non-expansion]
        - all(p(x) for x in filter(p, xs))  [correctness]
        - filter preserves order
        """
        p, p1, p2 = _v("p"), _v("p1"), _v("p2")
        xs = _v("xs")
        axioms: list[FormalAxiomEntry] = []

        # identity filter: filter(always_true, xs) == xs
        axioms.append(FormalAxiomEntry(
            name="filter_identity",
            module=_MODULE,
            params=[("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                _list_op(op_filter(_v("always_true"), xs)),
                xs,
                PyListType(),
            ),
            description="filter(lambda x: True, xs) == xs",
        ))

        # conjunction: filter(p1 ∧ p2, xs) == filter(p2, filter(p1, xs))
        axioms.append(FormalAxiomEntry(
            name="filter_conjunction",
            module=_MODULE,
            params=[
                ("p1", PyCallableType()),
                ("p2", PyCallableType()),
                ("xs", PyListType()),
            ],
            conclusion=formal_eq(
                _E,
                _list_op(op_filter(_opcall("pred_and", p1, p2), xs)),
                _list_op(op_filter(p2, op_filter(p1, xs))),
                PyListType(),
            ),
            description="filter(p1 ∧ p2, xs) == filter(p2, filter(p1, xs))",
        ))

        # non-expansion: len(list(filter(p, xs))) <= len(xs)
        axioms.append(FormalAxiomEntry(
            name="filter_non_expansion",
            module=_MODULE,
            params=[("p", PyCallableType()), ("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                op_le(op_len(_list_op(op_filter(p, xs))), op_len(xs)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="len(list(filter(p, xs))) <= len(xs)",
        ))

        # correctness: all(p(x) for x in filter(p, xs))
        axioms.append(FormalAxiomEntry(
            name="filter_correctness",
            module=_MODULE,
            params=[("p", PyCallableType()), ("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                _all_op(_opcall("genexpr_pred_check", p,
                                op_filter(p, xs))),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="all(p(x) for x in filter(p, xs))  (every element satisfies p)",
        ))

        # filter preserves order (elements appear in same relative order)
        axioms.append(FormalAxiomEntry(
            name="filter_preserves_order",
            module=_MODULE,
            params=[("p", PyCallableType()), ("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                _opcall("is_subsequence",
                        _list_op(op_filter(p, xs)), xs),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="filter(p, xs) is a subsequence of xs  (order preservation)",
        ))

        # filter of empty list
        axioms.append(FormalAxiomEntry(
            name="filter_empty",
            module=_MODULE,
            params=[("p", PyCallableType())],
            conclusion=formal_eq(
                _E,
                _list_op(op_filter(p, _lit([]))),
                _lit([]),
                PyListType(),
            ),
            description="filter(p, []) == []",
        ))

        return axioms

    def zip_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for zip as categorical product on iterables.

        Axioms:
        - len(list(zip(xs, ys))) == min(len(xs), len(ys))  [truncation]
        - zip(xs, ys)[i] == (xs[i], ys[i])  [pointwise]
        - zip(*zip(xs, ys)) ≈ (xs[:n], ys[:n]) where n = min(len(xs), len(ys))
        - zip(xs, strict=True) raises if lengths differ
        """
        xs, ys = _v("xs"), _v("ys")
        i = _v("i")
        axioms: list[FormalAxiomEntry] = []

        # truncation length
        axioms.append(FormalAxiomEntry(
            name="zip_length",
            module=_MODULE,
            params=[("xs", PyListType()), ("ys", PyListType())],
            conclusion=formal_eq(
                _E,
                op_len(_list_op(_op_zip(xs, ys))),
                _min_op(op_len(xs), op_len(ys)),
                PyIntType(),
            ),
            description="len(list(zip(xs, ys))) == min(len(xs), len(ys))",
        ))

        # pointwise: zip(xs, ys)[i] == (xs[i], ys[i])
        axioms.append(FormalAxiomEntry(
            name="zip_pointwise",
            module=_MODULE,
            params=[
                ("xs", PyListType()),
                ("ys", PyListType()),
                ("i", PyIntType()),
            ],
            conclusion=formal_eq(
                _E,
                op_getitem(_list_op(_op_zip(xs, ys)), i),
                _opcall("tuple2", op_getitem(xs, i), op_getitem(ys, i)),
                PyTupleType(),
            ),
            description="zip(xs, ys)[i] == (xs[i], ys[i])  (for valid i)",
        ))

        # roundtrip: zip(*zip(xs, ys)) recovers truncated originals
        axioms.append(FormalAxiomEntry(
            name="zip_unzip_roundtrip",
            module=_MODULE,
            params=[("xs", PyListType()), ("ys", PyListType())],
            conclusion=formal_eq(
                _E,
                _op_zip_unzip(xs, ys),
                _opcall("tuple2",
                        _op_slice(xs, _min_op(op_len(xs), op_len(ys))),
                        _op_slice(ys, _min_op(op_len(xs), op_len(ys)))),
                PyTupleType(),
            ),
            description="zip(*zip(xs, ys)) ≈ (xs[:n], ys[:n])  n=min(len(xs), len(ys))",
        ))

        # empty zip
        axioms.append(FormalAxiomEntry(
            name="zip_empty_left",
            module=_MODULE,
            params=[("ys", PyListType())],
            conclusion=formal_eq(
                _E,
                _list_op(_op_zip(_lit([]), ys)),
                _lit([]),
                PyListType(),
            ),
            description="zip([], ys) == []",
        ))

        # zip with strict=True raises on length mismatch
        axioms.append(FormalAxiomEntry(
            name="zip_strict_mismatch",
            module=_MODULE,
            params=[("xs", PyListType()), ("ys", PyListType())],
            conclusion=formal_check(
                _E,
                _opcall("zip_strict_raises",
                        xs, ys,
                        _opcall("ne", op_len(xs), op_len(ys))),
                RefinementType(
                    base_type=PyObjType(),
                    predicate="raises ValueError when len(xs) != len(ys)",
                ),
            ),
            description="zip(xs, ys, strict=True) raises ValueError if lengths differ",
        ))

        return axioms

    def enumerate_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for enumerate as index-augmented iterator.

        Axioms:
        - list(enumerate(xs)) == [(0,xs[0]), (1,xs[1]), ...]
        - list(enumerate(xs, start=k)) == [(k,xs[0]), (k+1,xs[1]), ...]
        - len(list(enumerate(xs))) == len(xs)
        """
        xs = _v("xs")
        k = _v("k")
        i = _v("i")
        axioms: list[FormalAxiomEntry] = []

        # pointwise: enumerate(xs)[i] == (i, xs[i])
        axioms.append(FormalAxiomEntry(
            name="enumerate_pointwise",
            module=_MODULE,
            params=[("xs", PyListType()), ("i", PyIntType())],
            conclusion=formal_eq(
                _E,
                op_getitem(_list_op(_op_enumerate(xs)), i),
                _opcall("tuple2", i, op_getitem(xs, i)),
                PyTupleType(),
            ),
            description="list(enumerate(xs))[i] == (i, xs[i])",
        ))

        # start parameter: enumerate(xs, start=k)[i] == (k+i, xs[i])
        axioms.append(FormalAxiomEntry(
            name="enumerate_start",
            module=_MODULE,
            params=[
                ("xs", PyListType()),
                ("k", PyIntType()),
                ("i", PyIntType()),
            ],
            conclusion=formal_eq(
                _E,
                op_getitem(_list_op(_op_enumerate_start(xs, k)), i),
                _opcall("tuple2", op_add(k, i), op_getitem(xs, i)),
                PyTupleType(),
            ),
            description="enumerate(xs, start=k)[i] == (k+i, xs[i])",
        ))

        # length preservation
        axioms.append(FormalAxiomEntry(
            name="enumerate_length",
            module=_MODULE,
            params=[("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                op_len(_list_op(_op_enumerate(xs))),
                op_len(xs),
                PyIntType(),
            ),
            description="len(list(enumerate(xs))) == len(xs)",
        ))

        return axioms


# ═══════════════════════════════════════════════════════════════════
# 2. functools.reduce as Catamorphism
# ═══════════════════════════════════════════════════════════════════

class ReduceSemantics:
    """functools.reduce as left fold / catamorphism.

    ``reduce(f, xs, z)`` computes ``f(f(f(z, x0), x1), x2)`` — a left fold.
    When ``f`` is associative with identity ``e`` the fold can be parallelized.
    """

    def reduce_axioms(self) -> list[FormalAxiomEntry]:
        """Catamorphism / left-fold axioms for functools.reduce.

        Axioms:
        - reduce(f, [], z) == z  [empty case]
        - reduce(f, [x], z) == f(z, x)  [singleton]
        - reduce(f, xs ++ ys, z) == reduce(f, ys, reduce(f, xs, z))  [split]
        - If f is associative with identity e:
          reduce(f, xs ++ ys, e) == f(reduce(f, xs, e), reduce(f, ys, e))
        - sum(xs) == reduce(operator.add, xs, 0)
        - math.prod(xs) == reduce(operator.mul, xs, 1)
        - ''.join(xs) == reduce(operator.add, xs, '')
        """
        f, g = _v("f"), _v("g")
        xs, ys = _v("xs"), _v("ys")
        x, z = _v("x"), _v("z")
        axioms: list[FormalAxiomEntry] = []

        # empty case: reduce(f, [], z) == z
        axioms.append(FormalAxiomEntry(
            name="reduce_empty",
            module=_MODULE,
            params=[("f", PyCallableType()), ("z", PyObjType())],
            conclusion=formal_eq(
                _E,
                _op_reduce(f, _lit([]), z),
                z,
                PyObjType(),
            ),
            description="reduce(f, [], z) == z  (empty fold is identity)",
        ))

        # singleton: reduce(f, [x], z) == f(z, x)
        axioms.append(FormalAxiomEntry(
            name="reduce_singleton",
            module=_MODULE,
            params=[
                ("f", PyCallableType()),
                ("x", PyObjType()),
                ("z", PyObjType()),
            ],
            conclusion=formal_eq(
                _E,
                _op_reduce(f, _opcall("singleton_list", x), z),
                _opcall("apply2", f, z, x),
                PyObjType(),
            ),
            description="reduce(f, [x], z) == f(z, x)",
        ))

        # split: reduce(f, xs ++ ys, z) == reduce(f, ys, reduce(f, xs, z))
        axioms.append(FormalAxiomEntry(
            name="reduce_split",
            module=_MODULE,
            params=[
                ("f", PyCallableType()),
                ("xs", PyListType()),
                ("ys", PyListType()),
                ("z", PyObjType()),
            ],
            conclusion=formal_eq(
                _E,
                _op_reduce(f, _concat_op(xs, ys), z),
                _op_reduce(f, ys, _op_reduce(f, xs, z)),
                PyObjType(),
            ),
            description="reduce(f, xs ++ ys, z) == reduce(f, ys, reduce(f, xs, z))",
        ))

        # parallel reduce for associative f with identity e
        axioms.append(FormalAxiomEntry(
            name="reduce_parallel_assoc",
            module=_MODULE,
            params=[
                ("f", PyCallableType()),
                ("xs", PyListType()),
                ("ys", PyListType()),
                ("z", PyObjType()),
            ],
            conclusion=formal_eq(
                _E,
                _op_reduce(f, _concat_op(xs, ys), z),
                _opcall("apply2", f,
                        _op_reduce(f, xs, z),
                        _op_reduce(f, ys, z)),
                PyObjType(),
            ),
            description=(
                "reduce(f, xs++ys, e) == f(reduce(f, xs, e), reduce(f, ys, e)) "
                "(f associative with identity e)"
            ),
        ))

        # sum(xs) == reduce(operator.add, xs, 0)
        axioms.append(FormalAxiomEntry(
            name="sum_as_reduce",
            module=_MODULE,
            params=[("xs", PyListType(PyIntType()))],
            conclusion=formal_eq(
                _E,
                _op_sum(xs),
                _op_reduce(
                    _op_operator("add"), xs, _int_lit(0)),
                PyIntType(),
            ),
            description="sum(xs) == reduce(operator.add, xs, 0)",
        ))

        # math.prod(xs) == reduce(operator.mul, xs, 1)
        axioms.append(FormalAxiomEntry(
            name="prod_as_reduce",
            module=_MODULE,
            params=[("xs", PyListType(PyIntType()))],
            conclusion=formal_eq(
                _E,
                _op_prod(xs),
                _op_reduce(
                    _op_operator("mul"), xs, _int_lit(1)),
                PyIntType(),
            ),
            description="math.prod(xs) == reduce(operator.mul, xs, 1)",
        ))

        # ''.join(strs) == reduce(operator.add, strs, '')
        axioms.append(FormalAxiomEntry(
            name="join_as_reduce",
            module=_MODULE,
            params=[("xs", PyListType(PyStrType()))],
            conclusion=formal_eq(
                _E,
                _op_str_join(xs),
                _op_reduce(
                    _op_operator("add"), xs, _str_lit("")),
                PyStrType(),
            ),
            description="''.join(strs) == reduce(operator.add, strs, '')",
        ))

        # reduce without initial value on singleton: reduce(f, [x]) == x
        axioms.append(FormalAxiomEntry(
            name="reduce_no_init_singleton",
            module=_MODULE,
            params=[("f", PyCallableType()), ("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                _op_reduce_no_init(f, _opcall("singleton_list", x)),
                x,
                PyObjType(),
            ),
            description="reduce(f, [x]) == x  (no initial, singleton list)",
        ))

        return axioms


# ═══════════════════════════════════════════════════════════════════
# 3. itertools Combinators
# ═══════════════════════════════════════════════════════════════════

class ItertoolsSemantics:
    """itertools combinators with algebraic laws.

    The itertools module provides lazy stream combinators.  The axioms
    here are stated in terms of the fully-materialised lists (via
    ``list(...)``), which suffices for equational reasoning.
    """

    def chain_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for itertools.chain as coproduct.

        Axioms:
        - list(chain(xs, ys)) == list(xs) + list(ys)  [coproduct]
        - len(list(chain(xs, ys))) == len(list(xs)) + len(list(ys))
        - chain is associative
        - chain.from_iterable(xss) == chain(*xss)
        """
        xs, ys, zs = _v("xs"), _v("ys"), _v("zs")
        xss = _v("xss")
        axioms: list[FormalAxiomEntry] = []

        # coproduct: list(chain(xs, ys)) == list(xs) + list(ys)
        axioms.append(FormalAxiomEntry(
            name="chain_as_concat",
            module=_MODULE,
            params=[("xs", PyListType()), ("ys", PyListType())],
            conclusion=formal_eq(
                _E,
                _list_op(_op_chain(xs, ys)),
                _concat_op(_list_op(xs), _list_op(ys)),
                PyListType(),
            ),
            description="list(chain(xs, ys)) == list(xs) + list(ys)",
        ))

        # length additivity
        axioms.append(FormalAxiomEntry(
            name="chain_length",
            module=_MODULE,
            params=[("xs", PyListType()), ("ys", PyListType())],
            conclusion=formal_eq(
                _E,
                op_len(_list_op(_op_chain(xs, ys))),
                op_add(op_len(_list_op(xs)), op_len(_list_op(ys))),
                PyIntType(),
            ),
            description="len(list(chain(xs, ys))) == len(list(xs)) + len(list(ys))",
        ))

        # associativity
        axioms.append(FormalAxiomEntry(
            name="chain_associative",
            module=_MODULE,
            params=[
                ("xs", PyListType()),
                ("ys", PyListType()),
                ("zs", PyListType()),
            ],
            conclusion=formal_eq(
                _E,
                _list_op(_op_chain(_op_chain(xs, ys), zs)),
                _list_op(_op_chain(xs, _op_chain(ys, zs))),
                PyListType(),
            ),
            description="chain(chain(xs, ys), zs) ≡ chain(xs, chain(ys, zs))",
        ))

        # from_iterable equivalence
        axioms.append(FormalAxiomEntry(
            name="chain_from_iterable",
            module=_MODULE,
            params=[("xss", PyListType(PyListType()))],
            conclusion=formal_eq(
                _E,
                _list_op(_op_chain_from_iterable(xss)),
                _list_op(_opcall("chain_star", xss)),
                PyListType(),
            ),
            description="chain.from_iterable(xss) == chain(*xss)",
        ))

        # identity: chain([], xs) == xs
        axioms.append(FormalAxiomEntry(
            name="chain_left_identity",
            module=_MODULE,
            params=[("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                _list_op(_op_chain(_lit([]), xs)),
                _list_op(xs),
                PyListType(),
            ),
            description="chain([], xs) ≡ xs  (left identity for coproduct)",
        ))

        return axioms

    def product_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for itertools.product as categorical product.

        Axioms:
        - len(list(product(xs, ys))) == len(xs) * len(ys)
        - product contains all (x, y) pairs
        - product(xs, repeat=n): len == len(xs)**n
        """
        xs, ys = _v("xs"), _v("ys")
        n = _v("n")
        axioms: list[FormalAxiomEntry] = []

        # length is multiplicative
        axioms.append(FormalAxiomEntry(
            name="product_length",
            module=_MODULE,
            params=[("xs", PyListType()), ("ys", PyListType())],
            conclusion=formal_eq(
                _E,
                op_len(_list_op(_op_product(xs, ys))),
                op_mul(op_len(xs), op_len(ys)),
                PyIntType(),
            ),
            description="len(list(product(xs, ys))) == len(xs) * len(ys)",
        ))

        # completeness: every (x,y) pair appears
        axioms.append(FormalAxiomEntry(
            name="product_completeness",
            module=_MODULE,
            params=[("xs", PyListType()), ("ys", PyListType())],
            conclusion=formal_eq(
                _E,
                _opcall("all_pairs_in",
                        _list_op(_op_product(xs, ys)), xs, ys),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="product(xs, ys) contains all (x,y) for x∈xs, y∈ys",
        ))

        # repeat: len(list(product(xs, repeat=n))) == len(xs)**n
        axioms.append(FormalAxiomEntry(
            name="product_repeat_length",
            module=_MODULE,
            params=[("xs", PyListType()), ("n", PyIntType())],
            conclusion=formal_eq(
                _E,
                op_len(_list_op(_op_product_repeat(xs, n))),
                _op_pow(op_len(xs), n),
                PyIntType(),
            ),
            description="len(list(product(xs, repeat=n))) == len(xs)**n",
        ))

        # empty product
        axioms.append(FormalAxiomEntry(
            name="product_empty_left",
            module=_MODULE,
            params=[("ys", PyListType())],
            conclusion=formal_eq(
                _E,
                _list_op(_op_product(_lit([]), ys)),
                _lit([]),
                PyListType(),
            ),
            description="product([], ys) == []",
        ))

        return axioms

    def groupby_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for itertools.groupby.

        Axioms:
        - concat(list(g) for k,g in groupby(xs, key)) == xs  [reconstruction]
        - All elements in a group share the same key
        - WARNING: groups consecutive runs only (not global grouping)
        - sorted + groupby gives global grouping
        """
        xs = _v("xs")
        key = _v("key")
        axioms: list[FormalAxiomEntry] = []

        # reconstruction: flattening groups recovers original
        axioms.append(FormalAxiomEntry(
            name="groupby_reconstruction",
            module=_MODULE,
            params=[("xs", PyListType()), ("key", PyCallableType())],
            conclusion=formal_eq(
                _E,
                _opcall("groupby_flatten", _op_groupby(xs, key)),
                _list_op(xs),
                PyListType(),
            ),
            description="concat(groups) == original list  (groupby is a partition)",
        ))

        # key homogeneity: all elements in each group share the same key
        axioms.append(FormalAxiomEntry(
            name="groupby_key_homogeneous",
            module=_MODULE,
            params=[("xs", PyListType()), ("key", PyCallableType())],
            conclusion=formal_eq(
                _E,
                _opcall("groupby_all_same_key", _op_groupby(xs, key), key),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="all elements in each groupby group share the same key value",
        ))

        # consecutive-run warning: groupby only groups consecutive equal keys
        axioms.append(FormalAxiomEntry(
            name="groupby_consecutive_only",
            module=_MODULE,
            params=[("xs", PyListType()), ("key", PyCallableType())],
            conclusion=formal_eq(
                _E,
                _opcall("groupby_is_consecutive_run", _op_groupby(xs, key)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description=(
                "WARNING: groupby groups consecutive runs only, not global grouping"
            ),
        ))

        # sorted + groupby = global grouping
        axioms.append(FormalAxiomEntry(
            name="groupby_after_sort_global",
            module=_MODULE,
            params=[("xs", PyListType()), ("key", PyCallableType())],
            conclusion=formal_eq(
                _E,
                _opcall("is_global_grouping",
                        _op_groupby(
                            _opcall("sorted_by_key", xs, key), key)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="sorted(xs, key=key) then groupby(key) yields global grouping",
        ))

        return axioms

    def permutations_combinations_axioms(self) -> list[FormalAxiomEntry]:
        """Counting axioms for permutations and combinations.

        Axioms:
        - len(list(permutations(xs, r))) == n!/(n-r)!
        - len(list(combinations(xs, r))) == C(n, r)
        - All permutations are distinct orderings
        - All combinations are distinct subsets
        - combinations_with_replacement: C(n+r-1, r)
        """
        xs = _v("xs")
        r = _v("r")
        n = _v("n")
        axioms: list[FormalAxiomEntry] = []

        # permutations count: n!/(n-r)!
        axioms.append(FormalAxiomEntry(
            name="permutations_count",
            module=_MODULE,
            params=[("xs", PyListType()), ("r", PyIntType())],
            conclusion=formal_eq(
                _E,
                op_len(_list_op(_op_permutations(xs, r))),
                _op_falling_factorial(op_len(xs), r),
                PyIntType(),
            ),
            description="len(list(permutations(xs, r))) == n!/(n-r)!  (falling factorial)",
        ))

        # combinations count: C(n, r)
        axioms.append(FormalAxiomEntry(
            name="combinations_count",
            module=_MODULE,
            params=[("xs", PyListType()), ("r", PyIntType())],
            conclusion=formal_eq(
                _E,
                op_len(_list_op(_op_combinations(xs, r))),
                _op_choose(op_len(xs), r),
                PyIntType(),
            ),
            description="len(list(combinations(xs, r))) == C(n, r)",
        ))

        # all permutations are distinct
        axioms.append(FormalAxiomEntry(
            name="permutations_distinct",
            module=_MODULE,
            params=[("xs", PyListType()), ("r", PyIntType())],
            conclusion=formal_eq(
                _E,
                _opcall("all_distinct", _list_op(_op_permutations(xs, r))),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="all permutations are distinct orderings",
        ))

        # all combinations are distinct subsets
        axioms.append(FormalAxiomEntry(
            name="combinations_distinct",
            module=_MODULE,
            params=[("xs", PyListType()), ("r", PyIntType())],
            conclusion=formal_eq(
                _E,
                _opcall("all_distinct", _list_op(_op_combinations(xs, r))),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="all combinations are distinct subsets",
        ))

        # combinations_with_replacement count: C(n+r-1, r)
        axioms.append(FormalAxiomEntry(
            name="combinations_wr_count",
            module=_MODULE,
            params=[("xs", PyListType()), ("r", PyIntType())],
            conclusion=formal_eq(
                _E,
                op_len(_list_op(_op_combinations_wr(xs, r))),
                _op_choose_wr(op_len(xs), r),
                PyIntType(),
            ),
            description="len(combinations_with_replacement(xs, r)) == C(n+r-1, r)",
        ))

        return axioms

    def accumulate_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for itertools.accumulate (scan / running fold).

        Axioms:
        - accumulate is the scan (running fold)
        - list(accumulate(xs, f, initial=z))[-1] == reduce(f, xs, z)
        - len(list(accumulate(xs, initial=z))) == len(xs) + 1
        """
        xs = _v("xs")
        f = _v("f")
        z = _v("z")
        axioms: list[FormalAxiomEntry] = []

        # final element equals fold/reduce
        axioms.append(FormalAxiomEntry(
            name="accumulate_final_is_reduce",
            module=_MODULE,
            params=[
                ("f", PyCallableType()),
                ("xs", PyListType()),
                ("z", PyObjType()),
            ],
            conclusion=formal_eq(
                _E,
                op_getitem(
                    _list_op(_op_accumulate(xs, f, z)),
                    _int_lit(-1)),
                _op_reduce(f, xs, z),
                PyObjType(),
            ),
            description=(
                "list(accumulate(xs, f, initial=z))[-1] == reduce(f, xs, z)"
            ),
        ))

        # length with initial: len(list(accumulate(xs, f, initial=z))) == len(xs) + 1
        axioms.append(FormalAxiomEntry(
            name="accumulate_length_with_initial",
            module=_MODULE,
            params=[
                ("f", PyCallableType()),
                ("xs", PyListType()),
                ("z", PyObjType()),
            ],
            conclusion=formal_eq(
                _E,
                op_len(_list_op(_op_accumulate(xs, f, z))),
                op_add(op_len(xs), _int_lit(1)),
                PyIntType(),
            ),
            description="len(list(accumulate(xs, f, initial=z))) == len(xs) + 1",
        ))

        # first element with initial is z
        axioms.append(FormalAxiomEntry(
            name="accumulate_first_is_initial",
            module=_MODULE,
            params=[
                ("f", PyCallableType()),
                ("xs", PyListType()),
                ("z", PyObjType()),
            ],
            conclusion=formal_eq(
                _E,
                op_getitem(
                    _list_op(_op_accumulate(xs, f, z)),
                    _int_lit(0)),
                z,
                PyObjType(),
            ),
            description="list(accumulate(xs, f, initial=z))[0] == z",
        ))

        # length without initial: len(list(accumulate(xs, f))) == len(xs)
        axioms.append(FormalAxiomEntry(
            name="accumulate_length_no_initial",
            module=_MODULE,
            params=[("f", PyCallableType()), ("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                op_len(_list_op(_op_accumulate_no_init(xs, f))),
                op_len(xs),
                PyIntType(),
            ),
            description="len(list(accumulate(xs, f))) == len(xs)  (no initial value)",
        ))

        return axioms

    def islice_takewhile_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for islice, takewhile, dropwhile, repeat, cycle.

        Axioms:
        - list(islice(xs, n)) == list(xs)[:n]
        - list(takewhile(p, xs)) is a prefix of list(xs)
        - list(dropwhile(p, xs)) is a suffix of list(xs)
        - list(takewhile(p, xs)) + list(dropwhile(p, xs)) == list(xs)
        - len(list(repeat(x, n))) == n
        - cycle(xs) repeats xs infinitely
        """
        xs = _v("xs")
        p = _v("p")
        x = _v("x")
        n = _v("n")
        axioms: list[FormalAxiomEntry] = []

        # islice: list(islice(xs, n)) == list(xs)[:n]
        axioms.append(FormalAxiomEntry(
            name="islice_as_slice",
            module=_MODULE,
            params=[("xs", PyListType()), ("n", PyIntType())],
            conclusion=formal_eq(
                _E,
                _list_op(_op_islice(xs, n)),
                _op_slice(_list_op(xs), n),
                PyListType(),
            ),
            description="list(islice(xs, n)) == list(xs)[:n]",
        ))

        # takewhile prefix
        axioms.append(FormalAxiomEntry(
            name="takewhile_is_prefix",
            module=_MODULE,
            params=[("p", PyCallableType()), ("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                _opcall("is_prefix",
                        _list_op(_op_takewhile(p, xs)),
                        _list_op(xs)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="list(takewhile(p, xs)) is a prefix of list(xs)",
        ))

        # dropwhile suffix
        axioms.append(FormalAxiomEntry(
            name="dropwhile_is_suffix",
            module=_MODULE,
            params=[("p", PyCallableType()), ("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                _opcall("is_suffix",
                        _list_op(_op_dropwhile(p, xs)),
                        _list_op(xs)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="list(dropwhile(p, xs)) is a suffix of list(xs)",
        ))

        # takewhile + dropwhile == original
        axioms.append(FormalAxiomEntry(
            name="takewhile_dropwhile_partition",
            module=_MODULE,
            params=[("p", PyCallableType()), ("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                _concat_op(
                    _list_op(_op_takewhile(p, xs)),
                    _list_op(_op_dropwhile(p, xs))),
                _list_op(xs),
                PyListType(),
            ),
            description=(
                "list(takewhile(p, xs)) + list(dropwhile(p, xs)) == list(xs)"
            ),
        ))

        # all elements in takewhile satisfy p
        axioms.append(FormalAxiomEntry(
            name="takewhile_all_satisfy",
            module=_MODULE,
            params=[("p", PyCallableType()), ("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                _all_op(_opcall("genexpr_pred_check", p,
                                _op_takewhile(p, xs))),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="all(p(x) for x in takewhile(p, xs))",
        ))

        # repeat length: len(list(repeat(x, n))) == n
        axioms.append(FormalAxiomEntry(
            name="repeat_length",
            module=_MODULE,
            params=[("x", PyObjType()), ("n", PyIntType())],
            conclusion=formal_eq(
                _E,
                op_len(_list_op(_op_repeat(x, n))),
                n,
                PyIntType(),
            ),
            description="len(list(repeat(x, n))) == n",
        ))

        # repeat elements: all elements are x
        axioms.append(FormalAxiomEntry(
            name="repeat_all_equal",
            module=_MODULE,
            params=[("x", PyObjType()), ("n", PyIntType())],
            conclusion=formal_eq(
                _E,
                _opcall("all_equal", _list_op(_op_repeat(x, n)), x),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="all(elem == x for elem in repeat(x, n))",
        ))

        # cycle property: cycle(xs) at index i equals xs[i % len(xs)]
        axioms.append(FormalAxiomEntry(
            name="cycle_periodic",
            module=_MODULE,
            params=[("xs", PyListType()), ("i", PyIntType())],
            conclusion=formal_eq(
                _E,
                _opcall("cycle_at", _op_cycle(xs), _v("i")),
                op_getitem(xs, _opcall("mod", _v("i"), op_len(xs))),
                PyObjType(),
            ),
            description="cycle(xs)[i] == xs[i % len(xs)]  (periodic repetition)",
        ))

        return axioms

    def starmap_zip_longest_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for itertools.starmap and zip_longest.

        Axioms:
        - list(starmap(f, xss)) == [f(*t) for t in xss]
        - starmap(f, zip(xs, ys)) ≡ map(lambda x,y: f(x,y), xs, ys)
        - len(list(zip_longest(xs, ys))) == max(len(xs), len(ys))
        """
        f = _v("f")
        xs, ys = _v("xs"), _v("ys")
        xss = _v("xss")
        fill = _v("fill")
        axioms: list[FormalAxiomEntry] = []

        # starmap pointwise
        axioms.append(FormalAxiomEntry(
            name="starmap_pointwise",
            module=_MODULE,
            params=[("f", PyCallableType()), ("xss", PyListType())],
            conclusion=formal_eq(
                _E,
                _list_op(_op_starmap(f, xss)),
                _opcall("listcomp_starmap", f, xss),
                PyListType(),
            ),
            description="list(starmap(f, xss)) == [f(*t) for t in xss]",
        ))

        # starmap length preservation
        axioms.append(FormalAxiomEntry(
            name="starmap_length",
            module=_MODULE,
            params=[("f", PyCallableType()), ("xss", PyListType())],
            conclusion=formal_eq(
                _E,
                op_len(_list_op(_op_starmap(f, xss))),
                op_len(_list_op(xss)),
                PyIntType(),
            ),
            description="len(list(starmap(f, xss))) == len(list(xss))",
        ))

        # zip_longest length is max
        axioms.append(FormalAxiomEntry(
            name="zip_longest_length",
            module=_MODULE,
            params=[
                ("xs", PyListType()),
                ("ys", PyListType()),
                ("fill", PyObjType()),
            ],
            conclusion=formal_eq(
                _E,
                op_len(_list_op(_op_zip_longest(xs, ys, fill))),
                _opcall("max", op_len(xs), op_len(ys)),
                PyIntType(),
            ),
            description="len(list(zip_longest(xs, ys))) == max(len(xs), len(ys))",
        ))

        return axioms


# ═══════════════════════════════════════════════════════════════════
# 4. functools Higher-Order Functions
# ═══════════════════════════════════════════════════════════════════

class FunctoolsSemantics:
    """functools: lru_cache, partial, singledispatch, wraps, total_ordering."""

    def lru_cache_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for functools.lru_cache (memoisation).

        Axioms:
        - lru_cache(f)(x) == f(x)  [correctness: same result]
        - Effect transformation: first call has f's effects, subsequent pure
        - Pure function + lru_cache: idempotent caching
        - WARNING: lru_cache on impure function changes semantics
        - cache_info() returns hits, misses, maxsize, currsize
        - cache_clear() resets the cache
        """
        f = _v("f")
        x = _v("x")
        axioms: list[FormalAxiomEntry] = []

        # correctness: lru_cache(f)(x) == f(x)
        axioms.append(FormalAxiomEntry(
            name="lru_cache_correctness",
            module=_MODULE,
            params=[("f", PyCallableType()), ("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                _opcall("apply1", _op_lru_cache(f), x),
                _op_apply(f, x),
                PyObjType(),
            ),
            description="lru_cache(f)(x) == f(x)  (cached result equals direct call)",
        ))

        # idempotence: lru_cache(lru_cache(f)) is equivalent to lru_cache(f)
        axioms.append(FormalAxiomEntry(
            name="lru_cache_idempotent",
            module=_MODULE,
            params=[("f", PyCallableType()), ("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                _opcall("apply1", _op_lru_cache(_op_lru_cache(f)), x),
                _opcall("apply1", _op_lru_cache(f), x),
                PyObjType(),
            ),
            description="lru_cache(lru_cache(f))(x) == lru_cache(f)(x)  (idempotent)",
        ))

        # cache_clear resets: after cache_clear(), cache_info().currsize == 0
        axioms.append(FormalAxiomEntry(
            name="lru_cache_clear_resets",
            module=_MODULE,
            params=[("f", PyCallableType())],
            conclusion=formal_eq(
                _E,
                _opcall("cache_currsize_after_clear", _op_lru_cache(f)),
                _int_lit(0),
                PyIntType(),
            ),
            description="After cache_clear(), cache_info().currsize == 0",
        ))

        # impurity warning: lru_cache on impure function changes semantics
        axioms.append(FormalAxiomEntry(
            name="lru_cache_impure_warning",
            module=_MODULE,
            params=[("f", PyCallableType())],
            conclusion=formal_check(
                _E,
                _opcall("lru_cache_impure_flag", f),
                RefinementType(
                    base_type=PyBoolType(),
                    predicate=(
                        "WARNING: lru_cache on impure function may suppress side effects"
                    ),
                ),
            ),
            description=(
                "WARNING: lru_cache on impure function changes semantics — "
                "side effects only on first call"
            ),
        ))

        return axioms

    def partial_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for functools.partial (currying / argument binding).

        Axioms:
        - partial(f, a)(b) == f(a, b)
        - partial(partial(f, a), b) == partial(f, a, b)
        - partial(f, **kw1)(**kw2) == f(**kw1, **kw2) (kw2 overrides kw1)
        """
        f = _v("f")
        a, b, c = _v("a"), _v("b"), _v("c")
        axioms: list[FormalAxiomEntry] = []

        # basic: partial(f, a)(b) == f(a, b)
        axioms.append(FormalAxiomEntry(
            name="partial_application",
            module=_MODULE,
            params=[
                ("f", PyCallableType()),
                ("a", PyObjType()),
                ("b", PyObjType()),
            ],
            conclusion=formal_eq(
                _E,
                _opcall("apply1", _op_partial(f, a), b),
                _opcall("apply2", f, a, b),
                PyObjType(),
            ),
            description="partial(f, a)(b) == f(a, b)",
        ))

        # nesting: partial(partial(f, a), b) == partial(f, a, b)
        axioms.append(FormalAxiomEntry(
            name="partial_nesting",
            module=_MODULE,
            params=[
                ("f", PyCallableType()),
                ("a", PyObjType()),
                ("b", PyObjType()),
                ("c", PyObjType()),
            ],
            conclusion=formal_eq(
                _E,
                _opcall("apply1", _op_partial(_op_partial(f, a), b), c),
                _opcall("apply3", f, a, b, c),
                PyObjType(),
            ),
            description="partial(partial(f, a), b)(c) == f(a, b, c)",
        ))

        # kwargs override: partial(f, **kw1)(**kw2) uses kw2 over kw1
        axioms.append(FormalAxiomEntry(
            name="partial_kwargs_override",
            module=_MODULE,
            params=[
                ("f", PyCallableType()),
                ("a", PyObjType()),
                ("b", PyObjType()),
            ],
            conclusion=formal_eq(
                _E,
                _opcall("partial_kwarg_call", f, a, b),
                _opcall("apply_kwarg_merged", f, a, b),
                PyObjType(),
            ),
            description="partial(f, **kw1)(**kw2) == f(**{**kw1, **kw2})  (kw2 overrides)",
        ))

        return axioms

    def singledispatch_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for functools.singledispatch (single-argument dispatch).

        Axioms:
        - singledispatch(f).register(T)(g): dispatch on T calls g
        - Dispatch follows MRO: if T not registered, checks base classes
        - Default (unregistered type) calls the original f
        """
        f, g = _v("f"), _v("g")
        x = _v("x")
        T = _v("T")
        axioms: list[FormalAxiomEntry] = []

        # registered type dispatches to registered impl
        axioms.append(FormalAxiomEntry(
            name="singledispatch_registered",
            module=_MODULE,
            params=[
                ("f", PyCallableType()),
                ("g", PyCallableType()),
                ("T", PyObjType()),
                ("x", PyObjType()),
            ],
            conclusion=formal_eq(
                _E,
                _opcall("singledispatch_call",
                        _op_singledispatch(f), T, g, x),
                _op_apply(g, x),
                PyObjType(),
            ),
            description="singledispatch(f).register(T)(g); dispatch(x:T) calls g(x)",
        ))

        # default fallback: unregistered type calls original f
        axioms.append(FormalAxiomEntry(
            name="singledispatch_default",
            module=_MODULE,
            params=[("f", PyCallableType()), ("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                _opcall("singledispatch_default_call",
                        _op_singledispatch(f), x),
                _op_apply(f, x),
                PyObjType(),
            ),
            description="singledispatch(f)(x) == f(x)  for unregistered type",
        ))

        # MRO dispatch: follows method resolution order
        axioms.append(FormalAxiomEntry(
            name="singledispatch_mro",
            module=_MODULE,
            params=[("f", PyCallableType()), ("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                _opcall("singledispatch_uses_mro",
                        _op_singledispatch(f), x),
                _bool_lit(True),
                PyBoolType(),
            ),
            description=(
                "singledispatch follows MRO: if T not registered, checks base classes"
            ),
        ))

        return axioms

    def wraps_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for functools.wraps (wrapper metadata copying).

        Axioms:
        - wraps(f)(g).__name__ == f.__name__
        - wraps(f)(g).__doc__ == f.__doc__
        - wraps(f)(g).__wrapped__ is f
        """
        f, g = _v("f"), _v("g")
        axioms: list[FormalAxiomEntry] = []

        # __name__ is copied
        axioms.append(FormalAxiomEntry(
            name="wraps_copies_name",
            module=_MODULE,
            params=[("f", PyCallableType()), ("g", PyCallableType())],
            conclusion=formal_eq(
                _E,
                _op_getattr(_op_wraps(f, g), _str_lit("__name__")),
                _op_getattr(f, _str_lit("__name__")),
                PyStrType(),
            ),
            description="wraps(f)(g).__name__ == f.__name__",
        ))

        # __doc__ is copied
        axioms.append(FormalAxiomEntry(
            name="wraps_copies_doc",
            module=_MODULE,
            params=[("f", PyCallableType()), ("g", PyCallableType())],
            conclusion=formal_eq(
                _E,
                _op_getattr(_op_wraps(f, g), _str_lit("__doc__")),
                _op_getattr(f, _str_lit("__doc__")),
                PyStrType(),
            ),
            description="wraps(f)(g).__doc__ == f.__doc__",
        ))

        # __wrapped__ attribute points to original
        axioms.append(FormalAxiomEntry(
            name="wraps_sets_wrapped",
            module=_MODULE,
            params=[("f", PyCallableType()), ("g", PyCallableType())],
            conclusion=formal_eq(
                _E,
                _op_getattr(_op_wraps(f, g), _str_lit("__wrapped__")),
                f,
                PyCallableType(),
            ),
            description="wraps(f)(g).__wrapped__ is f",
        ))

        return axioms

    def total_ordering_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for functools.total_ordering.

        Axioms:
        - @total_ordering: given __eq__ and one of __lt__/__le__/__gt__/__ge__,
          generates the other three
        - Generated comparisons are consistent: a < b ↔ not (a >= b)
        - Generated comparisons respect transitivity
        """
        a, b, c = _v("a"), _v("b"), _v("c")
        cls = _v("cls")
        axioms: list[FormalAxiomEntry] = []

        # consistency: a < b ↔ ¬(a >= b)
        axioms.append(FormalAxiomEntry(
            name="total_ordering_lt_ge_consistent",
            module=_MODULE,
            params=[("cls", PyObjType()), ("a", PyObjType()), ("b", PyObjType())],
            conclusion=formal_eq(
                _E,
                _opcall("total_ord_lt", cls, a, b),
                op_not(_opcall("total_ord_ge", cls, a, b)),
                PyBoolType(),
            ),
            description=(
                "@total_ordering: a < b ↔ not (a >= b)  (generated consistency)"
            ),
        ))

        # consistency: a <= b ↔ ¬(a > b)
        axioms.append(FormalAxiomEntry(
            name="total_ordering_le_gt_consistent",
            module=_MODULE,
            params=[("cls", PyObjType()), ("a", PyObjType()), ("b", PyObjType())],
            conclusion=formal_eq(
                _E,
                _opcall("total_ord_le", cls, a, b),
                op_not(_opcall("total_ord_gt", cls, a, b)),
                PyBoolType(),
            ),
            description=(
                "@total_ordering: a <= b ↔ not (a > b)  (generated consistency)"
            ),
        ))

        # transitivity: a < b ∧ b < c → a < c
        axioms.append(FormalAxiomEntry(
            name="total_ordering_transitivity",
            module=_MODULE,
            params=[
                ("cls", PyObjType()),
                ("a", PyObjType()),
                ("b", PyObjType()),
                ("c", PyObjType()),
            ],
            conclusion=formal_eq(
                _E,
                _opcall("total_ord_transitive", cls, a, b, c),
                _bool_lit(True),
                PyBoolType(),
            ),
            description=(
                "@total_ordering: a < b ∧ b < c → a < c  (transitivity)"
            ),
        ))

        # completeness: exactly one of a<b, a==b, a>b holds (trichotomy)
        axioms.append(FormalAxiomEntry(
            name="total_ordering_trichotomy",
            module=_MODULE,
            params=[("cls", PyObjType()), ("a", PyObjType()), ("b", PyObjType())],
            conclusion=formal_eq(
                _E,
                _opcall("total_ord_trichotomy", cls, a, b),
                _bool_lit(True),
                PyBoolType(),
            ),
            description=(
                "@total_ordering: exactly one of a<b, a==b, a>b  (trichotomy)"
            ),
        ))

        return axioms


# ═══════════════════════════════════════════════════════════════════
# 5. operator Module
# ═══════════════════════════════════════════════════════════════════

class OperatorSemantics:
    """operator module: first-class functions for Python operators.

    The ``operator`` module lifts Python's infix operators to named
    callables, enabling point-free composition with ``map``, ``reduce``,
    ``sorted(key=...)``, etc.
    """

    def operator_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms relating operator.X to the corresponding dunder/infix.

        Axioms:
        - operator.add(a, b) == a + b
        - operator.mul(a, b) == a * b
        - operator.itemgetter(k)(d) == d[k]
        - operator.attrgetter(attr)(obj) == getattr(obj, attr)
        - operator.methodcaller(name, *args)(obj) == getattr(obj, name)(*args)
        - operator.not_(x) == not x
        - itemgetter(k1, k2)(d) == (d[k1], d[k2])
        """
        a, b = _v("a"), _v("b")
        k, k1, k2 = _v("k"), _v("k1"), _v("k2")
        d = _v("d")
        obj = _v("obj")
        attr = _v("attr")
        name = _v("name")
        x = _v("x")
        axioms: list[FormalAxiomEntry] = []

        # operator.add(a, b) == a + b
        axioms.append(FormalAxiomEntry(
            name="operator_add",
            module=_MODULE,
            params=[("a", PyObjType()), ("b", PyObjType())],
            conclusion=formal_eq(
                _E,
                _op_operator("add", a, b),
                op_add(a, b),
                PyObjType(),
            ),
            description="operator.add(a, b) == a + b",
        ))

        # operator.mul(a, b) == a * b
        axioms.append(FormalAxiomEntry(
            name="operator_mul",
            module=_MODULE,
            params=[("a", PyObjType()), ("b", PyObjType())],
            conclusion=formal_eq(
                _E,
                _op_operator("mul", a, b),
                op_mul(a, b),
                PyObjType(),
            ),
            description="operator.mul(a, b) == a * b",
        ))

        # operator.eq(a, b) == (a == b)
        axioms.append(FormalAxiomEntry(
            name="operator_eq",
            module=_MODULE,
            params=[("a", PyObjType()), ("b", PyObjType())],
            conclusion=formal_eq(
                _E,
                _op_operator("eq", a, b),
                op_eq(a, b),
                PyBoolType(),
            ),
            description="operator.eq(a, b) == (a == b)",
        ))

        # operator.not_(x) == not x
        axioms.append(FormalAxiomEntry(
            name="operator_not",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                _op_operator("not_", x),
                op_not(x),
                PyBoolType(),
            ),
            description="operator.not_(x) == not x",
        ))

        # operator.itemgetter(k)(d) == d[k]
        axioms.append(FormalAxiomEntry(
            name="operator_itemgetter_single",
            module=_MODULE,
            params=[("k", PyObjType()), ("d", PyObjType())],
            conclusion=formal_eq(
                _E,
                _opcall("apply1", _op_itemgetter(k), d),
                op_getitem(d, k),
                PyObjType(),
            ),
            description="operator.itemgetter(k)(d) == d[k]",
        ))

        # operator.itemgetter(k1, k2)(d) == (d[k1], d[k2])
        axioms.append(FormalAxiomEntry(
            name="operator_itemgetter_multi",
            module=_MODULE,
            params=[
                ("k1", PyObjType()),
                ("k2", PyObjType()),
                ("d", PyObjType()),
            ],
            conclusion=formal_eq(
                _E,
                _opcall("apply1", _op_itemgetter2(k1, k2), d),
                _opcall("tuple2", op_getitem(d, k1), op_getitem(d, k2)),
                PyTupleType(),
            ),
            description="operator.itemgetter(k1, k2)(d) == (d[k1], d[k2])",
        ))

        # operator.attrgetter(attr)(obj) == getattr(obj, attr)
        axioms.append(FormalAxiomEntry(
            name="operator_attrgetter",
            module=_MODULE,
            params=[("attr", PyStrType()), ("obj", PyObjType())],
            conclusion=formal_eq(
                _E,
                _opcall("apply1", _op_attrgetter(attr), obj),
                _op_getattr(obj, attr),
                PyObjType(),
            ),
            description="operator.attrgetter(attr)(obj) == getattr(obj, attr)",
        ))

        # operator.methodcaller(name, *args)(obj) == getattr(obj, name)(*args)
        axioms.append(FormalAxiomEntry(
            name="operator_methodcaller",
            module=_MODULE,
            params=[("name", PyStrType()), ("obj", PyObjType())],
            conclusion=formal_eq(
                _E,
                _opcall("apply1", _op_methodcaller(name), obj),
                _opcall("apply0", _op_getattr(obj, name)),
                PyObjType(),
            ),
            description="operator.methodcaller(name)(obj) == getattr(obj, name)()",
        ))

        # operator.lt(a, b) == (a < b)
        axioms.append(FormalAxiomEntry(
            name="operator_lt",
            module=_MODULE,
            params=[("a", PyObjType()), ("b", PyObjType())],
            conclusion=formal_eq(
                _E,
                _op_operator("lt", a, b),
                op_lt(a, b),
                PyBoolType(),
            ),
            description="operator.lt(a, b) == (a < b)",
        ))

        # operator.le(a, b) == (a <= b)
        axioms.append(FormalAxiomEntry(
            name="operator_le",
            module=_MODULE,
            params=[("a", PyObjType()), ("b", PyObjType())],
            conclusion=formal_eq(
                _E,
                _op_operator("le", a, b),
                op_le(a, b),
                PyBoolType(),
            ),
            description="operator.le(a, b) == (a <= b)",
        ))

        return axioms


# ═══════════════════════════════════════════════════════════════════
# 6. Collect all
# ═══════════════════════════════════════════════════════════════════

def all_functional_axioms() -> list[FormalAxiomEntry]:
    """Return every functional combinator axiom.

    Collects axioms from MapFilterSemantics, ReduceSemantics,
    ItertoolsSemantics, FunctoolsSemantics, and OperatorSemantics.
    """
    axioms: list[FormalAxiomEntry] = []

    mf = MapFilterSemantics()
    axioms.extend(mf.map_axioms())
    axioms.extend(mf.filter_axioms())
    axioms.extend(mf.zip_axioms())
    axioms.extend(mf.enumerate_axioms())

    rd = ReduceSemantics()
    axioms.extend(rd.reduce_axioms())

    it = ItertoolsSemantics()
    axioms.extend(it.chain_axioms())
    axioms.extend(it.product_axioms())
    axioms.extend(it.groupby_axioms())
    axioms.extend(it.permutations_combinations_axioms())
    axioms.extend(it.accumulate_axioms())
    axioms.extend(it.islice_takewhile_axioms())
    axioms.extend(it.starmap_zip_longest_axioms())

    ft = FunctoolsSemantics()
    axioms.extend(ft.lru_cache_axioms())
    axioms.extend(ft.partial_axioms())
    axioms.extend(ft.singledispatch_axioms())
    axioms.extend(ft.wraps_axioms())
    axioms.extend(ft.total_ordering_axioms())

    op = OperatorSemantics()
    axioms.extend(op.operator_axioms())

    return axioms


# ═══════════════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════════════

def _self_test() -> None:
    """Smoke-test the functional axiom library."""
    errors: list[str] = []

    def _assert(cond: bool, msg: str) -> None:
        if not cond:
            errors.append(msg)

    all_ax = all_functional_axioms()

    # 1. Non-trivial count (we expect ~80+ axioms)
    _assert(len(all_ax) >= 70,
            f"Expected ≥70 axioms, got {len(all_ax)}")

    # 2. Every axiom has a name and correct module
    for ax in all_ax:
        _assert(bool(ax.name),
                f"Axiom has empty name: {ax}")
        _assert(ax.module == _MODULE,
                f"Axiom {ax.name} has wrong module: {ax.module}")

    # 3. No duplicate names
    names = [ax.name for ax in all_ax]
    dupes = [n for n in names if names.count(n) > 1]
    _assert(not dupes,
            f"Duplicate axiom names: {set(dupes)}")

    # 4. Every axiom has a conclusion that is a Judgment
    for ax in all_ax:
        _assert(ax.conclusion is not None,
                f"Axiom {ax.name} has no conclusion")
        _assert(isinstance(ax.conclusion, Judgment),
                f"Axiom {ax.name}: conclusion is {type(ax.conclusion)}, "
                f"expected Judgment")

    # 5. Every axiom has a description
    for ax in all_ax:
        _assert(bool(ax.description),
                f"Axiom {ax.name} has empty description")

    # 6. Equality axioms have left and right
    for ax in all_ax:
        if ax.conclusion.kind == JudgmentKind.EQUAL:
            _assert(ax.conclusion.left is not None,
                    f"{ax.name} missing left")
            _assert(ax.conclusion.right is not None,
                    f"{ax.name} missing right")

    # 7. Spot-check specific axioms exist
    name_set = set(names)
    for expected in [
        "map_identity", "map_composition", "map_length_preservation",
        "filter_identity", "filter_conjunction", "filter_non_expansion",
        "zip_length", "zip_pointwise",
        "enumerate_pointwise", "enumerate_length",
        "reduce_empty", "reduce_singleton", "reduce_split",
        "sum_as_reduce", "prod_as_reduce", "join_as_reduce",
        "chain_as_concat", "chain_associative",
        "product_length", "product_completeness",
        "groupby_reconstruction", "groupby_consecutive_only",
        "permutations_count", "combinations_count",
        "accumulate_final_is_reduce", "accumulate_length_with_initial",
        "islice_as_slice", "takewhile_dropwhile_partition",
        "repeat_length", "cycle_periodic",
        "lru_cache_correctness", "lru_cache_idempotent",
        "partial_application", "partial_nesting",
        "singledispatch_registered", "singledispatch_default",
        "wraps_copies_name", "wraps_sets_wrapped",
        "total_ordering_lt_ge_consistent", "total_ordering_transitivity",
        "operator_add", "operator_mul", "operator_itemgetter_single",
        "operator_attrgetter", "operator_methodcaller",
    ]:
        _assert(expected in name_set,
                f"Missing expected axiom: {expected}")

    # 8. Per-class axiom counts
    mf = MapFilterSemantics()
    _assert(len(mf.map_axioms()) >= 4,
            f"Need ≥4 map axioms, got {len(mf.map_axioms())}")
    _assert(len(mf.filter_axioms()) >= 5,
            f"Need ≥5 filter axioms, got {len(mf.filter_axioms())}")
    _assert(len(mf.zip_axioms()) >= 4,
            f"Need ≥4 zip axioms, got {len(mf.zip_axioms())}")
    _assert(len(mf.enumerate_axioms()) >= 3,
            f"Need ≥3 enumerate axioms, got {len(mf.enumerate_axioms())}")

    rd = ReduceSemantics()
    _assert(len(rd.reduce_axioms()) >= 7,
            f"Need ≥7 reduce axioms, got {len(rd.reduce_axioms())}")

    it = ItertoolsSemantics()
    _assert(len(it.chain_axioms()) >= 4,
            f"Need ≥4 chain axioms, got {len(it.chain_axioms())}")
    _assert(len(it.product_axioms()) >= 3,
            f"Need ≥3 product axioms, got {len(it.product_axioms())}")
    _assert(len(it.groupby_axioms()) >= 3,
            f"Need ≥3 groupby axioms, got {len(it.groupby_axioms())}")
    _assert(len(it.permutations_combinations_axioms()) >= 4,
            f"Need ≥4 perm/comb axioms, got "
            f"{len(it.permutations_combinations_axioms())}")
    _assert(len(it.accumulate_axioms()) >= 3,
            f"Need ≥3 accumulate axioms, got {len(it.accumulate_axioms())}")
    _assert(len(it.islice_takewhile_axioms()) >= 6,
            f"Need ≥6 islice/takewhile axioms, got "
            f"{len(it.islice_takewhile_axioms())}")

    ft = FunctoolsSemantics()
    _assert(len(ft.lru_cache_axioms()) >= 3,
            f"Need ≥3 lru_cache axioms, got {len(ft.lru_cache_axioms())}")
    _assert(len(ft.partial_axioms()) >= 3,
            f"Need ≥3 partial axioms, got {len(ft.partial_axioms())}")
    _assert(len(ft.singledispatch_axioms()) >= 2,
            f"Need ≥2 singledispatch axioms, got "
            f"{len(ft.singledispatch_axioms())}")
    _assert(len(ft.wraps_axioms()) >= 3,
            f"Need ≥3 wraps axioms, got {len(ft.wraps_axioms())}")
    _assert(len(ft.total_ordering_axioms()) >= 3,
            f"Need ≥3 total_ordering axioms, got "
            f"{len(ft.total_ordering_axioms())}")

    op = OperatorSemantics()
    _assert(len(op.operator_axioms()) >= 8,
            f"Need ≥8 operator axioms, got {len(op.operator_axioms())}")

    # Print results
    if errors:
        print(f"FAILED — {len(errors)} error(s):")
        for e in errors:
            print(f"  ✗ {e}")
        raise AssertionError(f"{len(errors)} self-test(s) failed")
    else:
        print(f"OK — all {len(all_ax)} axioms validated "
              f"({len(names)} unique names, 0 errors)")


if __name__ == "__main__":
    _self_test()
