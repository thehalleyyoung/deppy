"""
SynHoPy Formal Semantics — Python Data Model
==============================================

Formal axioms for Python's core data types: the numeric tower, strings,
lists, dicts, sets, tuples, and truthiness.  Each axiom is a
``FormalAxiomEntry`` with machine-checkable content expressed in the
SynHoPy kernel term language.

Monograph references
--------------------
- Ch 5:  Pure Functions and Refinement Types — sorted, binary search, merge sort
- Ch 16: Dict — dict as namespace, dynamic attrs, module dict
- Ch 20: Comprehensions — as data constructors
- Ch 22: Strings — free monoids, f-strings, regex, encoding/decoding
- Appendix A: typing rules for all data operations

Architecture
------------
NumericSemantics   — bool <: int <: float <: complex, arithmetic
StringSemantics    — free-monoid axioms, slicing, encoding
ListSemantics      — mutable sequences, sorting, slicing
DictSemantics      — finite maps, insertion order, merge
SetSemantics       — unordered collections, lattice ops
TupleSemantics     — immutable sequences, unpacking
BooleanSemantics   — truthiness, short-circuit evaluation

``all_data_axioms()`` collects every axiom for use by the proof kernel.
"""
from __future__ import annotations

from synhopy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    PyObjType, PyIntType, PyFloatType, PyStrType, PyBoolType,
    PyNoneType, PyListType, PyDictType, PySetType, PyTupleType,
    Var, Literal,
)
from synhopy.core.formal_ops import (
    Op, OpCall, FormalAxiomEntry, formal_eq,
    op_add, op_sub, op_mul, op_truediv, op_floordiv, op_mod, op_pow, op_neg, op_abs,
    op_eq, op_ne, op_lt, op_le, op_gt, op_ge,
    op_len, op_contains, op_getitem, op_setitem,
    op_append, op_extend, op_pop, op_sort, op_sorted, op_reversed,
    op_dict_get, op_dict_keys, op_dict_values, op_dict_items,
    op_set_add, op_set_union, op_set_intersection,
    op_str_concat, op_str_join, op_str_split,
    op_bool, op_int, op_float, op_hash,
    op_and, op_or, op_not,
)

# ── shorthand helpers ─────────────────────────────────────────────

_E = Context()  # empty context

def _v(name: str) -> Var:
    return Var(name)

def _lit(value: object) -> Literal:
    return Literal(value=value)

def _int_lit(n: int) -> Literal:
    return Literal(value=n)

def _str_lit(s: str) -> Literal:
    return Literal(value=s)

def _bool_lit(b: bool) -> Literal:
    return Literal(value=b)

def _opcall(name: str, *args: SynTerm) -> OpCall:
    return OpCall(Op(name), tuple(args))

_MODULE = "python.data"


# ═══════════════════════════════════════════════════════════════════
# 1. Numeric Tower
# ═══════════════════════════════════════════════════════════════════

class NumericSemantics:
    """Python's numeric tower: bool <: int <: float <: complex.

    Covers exact integer arithmetic (unbounded precision), IEEE 754
    float semantics, type coercions, and the standard algebraic
    identities that the proof kernel may appeal to.
    """

    # ── subtyping chain ───────────────────────────────────────────

    def numeric_tower_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for the numeric tower and arithmetic identities."""
        a, b, c = _v("a"), _v("b"), _v("c")
        zero, one = _int_lit(0), _int_lit(1)
        axioms: list[FormalAxiomEntry] = []

        # — subtyping —
        axioms.append(FormalAxiomEntry(
            name="bool_subtype_int",
            module=_MODULE,
            params=[],
            conclusion=Judgment(
                kind=JudgmentKind.SUBTYPE, context=_E,
                left=_lit(PyBoolType()), right=_lit(PyIntType()),
            ),
            description="bool <: int  (True=1, False=0)",
        ))
        axioms.append(FormalAxiomEntry(
            name="int_subtype_float",
            module=_MODULE,
            params=[],
            conclusion=Judgment(
                kind=JudgmentKind.SUBTYPE, context=_E,
                left=_lit(PyIntType()), right=_lit(PyFloatType()),
            ),
            description="int <: float  (exact for small ints)",
        ))

        # — commutativity —
        axioms.append(FormalAxiomEntry(
            name="add_commutative",
            module=_MODULE,
            params=[("a", PyIntType()), ("b", PyIntType())],
            conclusion=formal_eq(_E, op_add(a, b), op_add(b, a), PyIntType()),
            description="a + b == b + a",
        ))
        axioms.append(FormalAxiomEntry(
            name="mul_commutative",
            module=_MODULE,
            params=[("a", PyIntType()), ("b", PyIntType())],
            conclusion=formal_eq(_E, op_mul(a, b), op_mul(b, a), PyIntType()),
            description="a * b == b * a",
        ))

        # — associativity —
        axioms.append(FormalAxiomEntry(
            name="add_associative",
            module=_MODULE,
            params=[("a", PyIntType()), ("b", PyIntType()), ("c", PyIntType())],
            conclusion=formal_eq(
                _E,
                op_add(op_add(a, b), c),
                op_add(a, op_add(b, c)),
                PyIntType(),
            ),
            description="(a + b) + c == a + (b + c)",
        ))
        axioms.append(FormalAxiomEntry(
            name="mul_associative",
            module=_MODULE,
            params=[("a", PyIntType()), ("b", PyIntType()), ("c", PyIntType())],
            conclusion=formal_eq(
                _E,
                op_mul(op_mul(a, b), c),
                op_mul(a, op_mul(b, c)),
                PyIntType(),
            ),
            description="(a * b) * c == a * (b * c)",
        ))

        # — distributivity —
        axioms.append(FormalAxiomEntry(
            name="mul_distributes_over_add",
            module=_MODULE,
            params=[("a", PyIntType()), ("b", PyIntType()), ("c", PyIntType())],
            conclusion=formal_eq(
                _E,
                op_mul(a, op_add(b, c)),
                op_add(op_mul(a, b), op_mul(a, c)),
                PyIntType(),
            ),
            description="a * (b + c) == a * b + a * c",
        ))

        # — identity elements —
        axioms.append(FormalAxiomEntry(
            name="add_identity",
            module=_MODULE,
            params=[("a", PyIntType())],
            conclusion=formal_eq(_E, op_add(a, zero), a, PyIntType()),
            description="a + 0 == a",
        ))
        axioms.append(FormalAxiomEntry(
            name="mul_identity",
            module=_MODULE,
            params=[("a", PyIntType())],
            conclusion=formal_eq(_E, op_mul(a, one), a, PyIntType()),
            description="a * 1 == a",
        ))

        # — negation —
        axioms.append(FormalAxiomEntry(
            name="add_inverse",
            module=_MODULE,
            params=[("a", PyIntType())],
            conclusion=formal_eq(_E, op_add(a, op_neg(a)), zero, PyIntType()),
            description="a + (-a) == 0",
        ))

        # — abs —
        axioms.append(FormalAxiomEntry(
            name="abs_nonneg",
            module=_MODULE,
            params=[("a", PyIntType())],
            conclusion=formal_eq(
                _E,
                op_ge(op_abs(a), zero),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="abs(a) >= 0",
        ))

        # — integer division invariant —
        axioms.append(FormalAxiomEntry(
            name="divmod_identity",
            module=_MODULE,
            params=[("a", PyIntType()), ("b", PyIntType())],
            conclusion=formal_eq(
                _E,
                op_add(op_mul(op_floordiv(a, b), b), op_mod(a, b)),
                a,
                PyIntType(),
            ),
            description="a // b * b + a % b == a  (for b != 0)",
        ))

        # — divmod consistency —
        axioms.append(FormalAxiomEntry(
            name="divmod_eq",
            module=_MODULE,
            params=[("a", PyIntType()), ("b", PyIntType())],
            conclusion=formal_eq(
                _E,
                _opcall("divmod", a, b),
                _opcall("tuple", op_floordiv(a, b), op_mod(a, b)),
                PyTupleType((PyIntType(), PyIntType())),
            ),
            description="divmod(a, b) == (a // b, a % b)",
        ))

        # — modulo bound (b > 0) —
        axioms.append(FormalAxiomEntry(
            name="mod_bound_positive",
            module=_MODULE,
            params=[("a", PyIntType()), ("b", PyIntType())],
            conclusion=formal_eq(
                _E,
                op_and(
                    op_ge(op_mod(a, b), zero),
                    op_lt(op_mod(a, b), b),
                ),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="0 <= a % b < b  (for b > 0)",
        ))

        # — pow with modulus —
        axioms.append(FormalAxiomEntry(
            name="pow_mod",
            module=_MODULE,
            params=[("a", PyIntType()), ("b", PyIntType()), ("m", PyIntType())],
            conclusion=formal_eq(
                _E,
                _opcall("pow3", a, b, _v("m")),
                op_mod(op_pow(a, b), _v("m")),
                PyIntType(),
            ),
            description="pow(a, b, m) == pow(a, b) % m  (for ints)",
        ))

        return axioms

    # ── coercions ─────────────────────────────────────────────────

    def coercion_axioms(self) -> list[FormalAxiomEntry]:
        """Type coercion axioms between numeric types."""
        x = _v("x")
        axioms: list[FormalAxiomEntry] = []

        axioms.append(FormalAxiomEntry(
            name="int_of_true",
            module=_MODULE,
            params=[],
            conclusion=formal_eq(
                _E, op_int(_bool_lit(True)), _int_lit(1), PyIntType(),
            ),
            description="int(True) == 1",
        ))
        axioms.append(FormalAxiomEntry(
            name="int_of_false",
            module=_MODULE,
            params=[],
            conclusion=formal_eq(
                _E, op_int(_bool_lit(False)), _int_lit(0), PyIntType(),
            ),
            description="int(False) == 0",
        ))
        axioms.append(FormalAxiomEntry(
            name="bool_of_zero",
            module=_MODULE,
            params=[],
            conclusion=formal_eq(
                _E, op_bool(_int_lit(0)), _bool_lit(False), PyBoolType(),
            ),
            description="bool(0) == False",
        ))
        axioms.append(FormalAxiomEntry(
            name="int_truncates_float",
            module=_MODULE,
            params=[("x", PyFloatType())],
            conclusion=formal_eq(
                _E,
                op_int(x),
                _opcall("trunc", x),
                PyIntType(),
            ),
            description="int(float_val) truncates toward zero",
        ))

        return axioms


# ═══════════════════════════════════════════════════════════════════
# 2. String Semantics
# ═══════════════════════════════════════════════════════════════════

class StringSemantics:
    """Strings as free monoids over Unicode code points.

    The axioms here treat ``str`` as a free monoid with concatenation
    as the binary operation and ``""`` as the identity.  Additional
    axioms cover slicing, searching, casing, and encoding/decoding
    (Ch 22 of the monograph).
    """

    def string_axioms(self) -> list[FormalAxiomEntry]:
        """Core string axioms (free-monoid + derived operations)."""
        a, b, c = _v("a"), _v("b"), _v("c")
        s, t = _v("s"), _v("t")
        sep, prefix, suffix = _v("sep"), _v("prefix"), _v("suffix")
        i, j = _v("i"), _v("j")
        x = _v("x")
        empty = _str_lit("")
        axioms: list[FormalAxiomEntry] = []

        # — monoid identity —
        axioms.append(FormalAxiomEntry(
            name="str_concat_left_identity",
            module=_MODULE,
            params=[("s", PyStrType())],
            conclusion=formal_eq(_E, op_str_concat(empty, s), s, PyStrType()),
            description='"" + s == s',
        ))
        axioms.append(FormalAxiomEntry(
            name="str_concat_right_identity",
            module=_MODULE,
            params=[("s", PyStrType())],
            conclusion=formal_eq(_E, op_str_concat(s, empty), s, PyStrType()),
            description='s + "" == s',
        ))

        # — monoid associativity —
        axioms.append(FormalAxiomEntry(
            name="str_concat_assoc",
            module=_MODULE,
            params=[("a", PyStrType()), ("b", PyStrType()), ("c", PyStrType())],
            conclusion=formal_eq(
                _E,
                op_str_concat(op_str_concat(a, b), c),
                op_str_concat(a, op_str_concat(b, c)),
                PyStrType(),
            ),
            description="(a + b) + c == a + (b + c)  (string concat is associative)",
        ))

        # — len homomorphism —
        axioms.append(FormalAxiomEntry(
            name="str_len_concat",
            module=_MODULE,
            params=[("a", PyStrType()), ("b", PyStrType())],
            conclusion=formal_eq(
                _E,
                op_len(op_str_concat(a, b)),
                op_add(op_len(a), op_len(b)),
                PyIntType(),
            ),
            description="len(a + b) == len(a) + len(b)",
        ))
        axioms.append(FormalAxiomEntry(
            name="str_len_empty",
            module=_MODULE,
            params=[],
            conclusion=formal_eq(_E, op_len(empty), _int_lit(0), PyIntType()),
            description='len("") == 0',
        ))

        # — startswith / endswith —
        axioms.append(FormalAxiomEntry(
            name="str_startswith_prefix",
            module=_MODULE,
            params=[("s", PyStrType()), ("prefix", PyStrType())],
            conclusion=formal_eq(
                _E,
                _opcall("str.startswith", s, prefix),
                op_eq(
                    op_getitem(s, _opcall("slice", _int_lit(0), op_len(prefix))),
                    prefix,
                ),
                PyBoolType(),
            ),
            description="s.startswith(prefix) ↔ s[:len(prefix)] == prefix",
        ))
        axioms.append(FormalAxiomEntry(
            name="str_endswith_suffix",
            module=_MODULE,
            params=[("s", PyStrType()), ("suffix", PyStrType())],
            conclusion=formal_eq(
                _E,
                _opcall("str.endswith", s, suffix),
                op_eq(
                    op_getitem(s, _opcall("slice", op_neg(op_len(suffix)), _lit(None))),
                    suffix,
                ),
                PyBoolType(),
            ),
            description="s.endswith(suffix) ↔ s[-len(suffix):] == suffix  (non-empty suffix)",
        ))

        # — f-string identity —
        axioms.append(FormalAxiomEntry(
            name="fstring_eq_str",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                _opcall("fstring", x),
                _opcall("__str__", x),
                PyStrType(),
            ),
            description='f"{x}" == str(x)',
        ))

        # — encode / decode roundtrip —
        axioms.append(FormalAxiomEntry(
            name="str_encode_decode_roundtrip",
            module=_MODULE,
            params=[("s", PyStrType())],
            conclusion=formal_eq(
                _E,
                _opcall("bytes.decode",
                        _opcall("str.encode", s, _str_lit("utf-8")),
                        _str_lit("utf-8")),
                s,
                PyStrType(),
            ),
            description='s.encode("utf-8").decode("utf-8") == s',
        ))

        # — split / join roundtrip —
        axioms.append(FormalAxiomEntry(
            name="str_split_join_roundtrip",
            module=_MODULE,
            params=[("s", PyStrType()), ("sep", PyStrType())],
            conclusion=formal_eq(
                _E,
                op_str_join(sep, op_str_split(s, sep)),
                s,
                PyStrType(),
            ),
            description="sep.join(s.split(sep)) == s",
        ))

        # — replace exhaustive —
        axioms.append(FormalAxiomEntry(
            name="str_replace_removes_old",
            module=_MODULE,
            params=[("s", PyStrType()), ("old", PyStrType()), ("new", PyStrType())],
            conclusion=formal_eq(
                _E,
                op_eq(
                    _opcall("str.count",
                            _opcall("str.replace", s, _v("old"), _v("new")),
                            _v("old")),
                    _int_lit(0),
                ),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="s.replace(old, new).count(old) == 0  (when old not in new)",
        ))

        # — strip is idempotent —
        axioms.append(FormalAxiomEntry(
            name="str_strip_idempotent",
            module=_MODULE,
            params=[("s", PyStrType())],
            conclusion=formal_eq(
                _E,
                _opcall("str.strip", _opcall("str.strip", s)),
                _opcall("str.strip", s),
                PyStrType(),
            ),
            description="s.strip().strip() == s.strip()",
        ))

        return axioms


# ═══════════════════════════════════════════════════════════════════
# 3. List Semantics
# ═══════════════════════════════════════════════════════════════════

class ListSemantics:
    """Lists as mutable sequences.

    Axioms cover length invariants, element access, mutation
    (append/extend/pop/insert/remove), sorting (Ch 5), and
    the standard sequence algebra (concatenation, repetition).
    """

    def list_axioms(self) -> list[FormalAxiomEntry]:
        """Core list axioms."""
        xs, ys = _v("xs"), _v("ys")
        x, e = _v("x"), _v("e")
        i, n = _v("i"), _v("n")
        axioms: list[FormalAxiomEntry] = []
        empty_list = _opcall("list")

        # — empty length —
        axioms.append(FormalAxiomEntry(
            name="list_len_empty",
            module=_MODULE,
            params=[],
            conclusion=formal_eq(
                _E, op_len(empty_list), _int_lit(0), PyIntType(),
            ),
            description="len([]) == 0",
        ))

        # — append length —
        axioms.append(FormalAxiomEntry(
            name="list_append_len",
            module=_MODULE,
            params=[("xs", PyListType()), ("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_len(op_append(xs, x)),
                op_add(op_len(xs), _int_lit(1)),
                PyIntType(),
            ),
            description="len after append increases by 1",
        ))

        # — append last element —
        axioms.append(FormalAxiomEntry(
            name="list_append_last",
            module=_MODULE,
            params=[("xs", PyListType()), ("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_getitem(op_append(xs, x), _int_lit(-1)),
                x,
                PyObjType(),
            ),
            description="(xs.append(x))[-1] == x",
        ))

        # — extend length —
        axioms.append(FormalAxiomEntry(
            name="list_extend_len",
            module=_MODULE,
            params=[("xs", PyListType()), ("ys", PyListType())],
            conclusion=formal_eq(
                _E,
                op_len(op_extend(xs, ys)),
                op_add(op_len(xs), op_len(ys)),
                PyIntType(),
            ),
            description="len after extend == len(xs) + len(ys)",
        ))

        # — concat length —
        axioms.append(FormalAxiomEntry(
            name="list_concat_len",
            module=_MODULE,
            params=[("xs", PyListType()), ("ys", PyListType())],
            conclusion=formal_eq(
                _E,
                op_len(op_add(xs, ys)),
                op_add(op_len(xs), op_len(ys)),
                PyIntType(),
            ),
            description="len(xs + ys) == len(xs) + len(ys)",
        ))

        # — repeat length —
        axioms.append(FormalAxiomEntry(
            name="list_repeat_len",
            module=_MODULE,
            params=[("xs", PyListType()), ("n", PyIntType())],
            conclusion=formal_eq(
                _E,
                op_len(op_mul(xs, n)),
                op_mul(op_len(xs), n),
                PyIntType(),
            ),
            description="len(xs * n) == len(xs) * n",
        ))

        # — pop decreases length —
        axioms.append(FormalAxiomEntry(
            name="list_pop_len",
            module=_MODULE,
            params=[("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                op_len(_opcall("list.pop_result_list", xs)),
                op_sub(op_len(xs), _int_lit(1)),
                PyIntType(),
            ),
            description="len after pop decreases by 1",
        ))

        # — containment —
        axioms.append(FormalAxiomEntry(
            name="list_contains_any",
            module=_MODULE,
            params=[("xs", PyListType()), ("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_contains(xs, x),
                _opcall("any", _opcall("genexpr",
                        op_eq(e, x), e, xs)),
                PyBoolType(),
            ),
            description="x in xs ↔ any(e == x for e in xs)",
        ))

        # — sorted is sorted —
        axioms.append(FormalAxiomEntry(
            name="sorted_is_sorted",
            module=_MODULE,
            params=[("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                _opcall("is_sorted", op_sorted(xs)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="sorted(xs) is sorted",
        ))

        # — sorted is idempotent —
        axioms.append(FormalAxiomEntry(
            name="sorted_idempotent",
            module=_MODULE,
            params=[("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                op_sorted(op_sorted(xs)),
                op_sorted(xs),
                PyListType(),
            ),
            description="sorted(sorted(xs)) == sorted(xs)",
        ))

        # — sorted is permutation (same length) —
        axioms.append(FormalAxiomEntry(
            name="sorted_same_len",
            module=_MODULE,
            params=[("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                op_len(op_sorted(xs)),
                op_len(xs),
                PyIntType(),
            ),
            description="len(sorted(xs)) == len(xs)  (permutation preserves length)",
        ))

        # — reversed is involution —
        axioms.append(FormalAxiomEntry(
            name="reversed_involution",
            module=_MODULE,
            params=[("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                _opcall("list", op_reversed(_opcall("list", op_reversed(xs)))),
                xs,
                PyListType(),
            ),
            description="list(reversed(list(reversed(xs)))) == xs",
        ))

        # — min is element and lower bound —
        axioms.append(FormalAxiomEntry(
            name="min_in_list",
            module=_MODULE,
            params=[("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                op_contains(xs, _opcall("min", xs)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="min(xs) in xs",
        ))
        axioms.append(FormalAxiomEntry(
            name="max_in_list",
            module=_MODULE,
            params=[("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                op_contains(xs, _opcall("max", xs)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="max(xs) in xs",
        ))

        # — sum as fold —
        axioms.append(FormalAxiomEntry(
            name="sum_is_fold",
            module=_MODULE,
            params=[("xs", PyListType(PyIntType()))],
            conclusion=formal_eq(
                _E,
                _opcall("sum", xs),
                _opcall("fold", Op("__add__"), _int_lit(0), xs),
                PyIntType(),
            ),
            description="sum(xs) == fold(+, 0, xs)",
        ))

        # — range length —
        axioms.append(FormalAxiomEntry(
            name="range_len",
            module=_MODULE,
            params=[("n", PyIntType())],
            conclusion=formal_eq(
                _E,
                op_len(_opcall("range", n)),
                _opcall("max", _int_lit(0), n),
                PyIntType(),
            ),
            description="len(range(n)) == max(0, n)",
        ))

        # — insert semantics —
        axioms.append(FormalAxiomEntry(
            name="list_insert_len",
            module=_MODULE,
            params=[("xs", PyListType()), ("i", PyIntType()), ("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_len(_opcall("list.insert", xs, i, x)),
                op_add(op_len(xs), _int_lit(1)),
                PyIntType(),
            ),
            description="len after insert increases by 1",
        ))
        axioms.append(FormalAxiomEntry(
            name="list_insert_element",
            module=_MODULE,
            params=[("xs", PyListType()), ("i", PyIntType()), ("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_getitem(_opcall("list.insert", xs, i, x), i),
                x,
                PyObjType(),
            ),
            description="xs.insert(i, x) puts x at index i",
        ))

        return axioms

    def slice_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for list slicing."""
        xs = _v("xs")
        i, j = _v("i"), _v("j")
        axioms: list[FormalAxiomEntry] = []

        # — full slice is shallow copy —
        axioms.append(FormalAxiomEntry(
            name="list_full_slice_eq",
            module=_MODULE,
            params=[("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                op_getitem(xs, _opcall("slice", _lit(None), _lit(None))),
                xs,
                PyListType(),
            ),
            description="xs[:] == xs  (shallow copy, equal by value)",
        ))

        # — reverse slice —
        axioms.append(FormalAxiomEntry(
            name="list_reverse_slice",
            module=_MODULE,
            params=[("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                op_getitem(xs, _opcall("slice", _lit(None), _lit(None), _int_lit(-1))),
                _opcall("list", op_reversed(xs)),
                PyListType(),
            ),
            description="xs[::-1] == list(reversed(xs))",
        ))

        # — slice length —
        axioms.append(FormalAxiomEntry(
            name="list_slice_len",
            module=_MODULE,
            params=[("xs", PyListType()), ("i", PyIntType()), ("j", PyIntType())],
            conclusion=formal_eq(
                _E,
                op_len(op_getitem(xs, _opcall("slice", i, j))),
                _opcall("max", _int_lit(0),
                        _opcall("min", j, op_len(xs)),
                ),
                PyIntType(),
            ),
            description="len(xs[i:j]) bounded by j - i and len(xs)",
        ))

        return axioms


# ═══════════════════════════════════════════════════════════════════
# 4. Dict Semantics
# ═══════════════════════════════════════════════════════════════════

class DictSemantics:
    """Dicts as finite maps with insertion-order preservation (Python 3.7+).

    Axioms cover read-after-write, deletion, merge (``|``),
    ``.get`` with defaults, and the ``dict ↔ items`` isomorphism
    (Ch 16 of the monograph).
    """

    def dict_axioms(self) -> list[FormalAxiomEntry]:
        """Core dict axioms."""
        d, d1, d2 = _v("d"), _v("d1"), _v("d2")
        k, v, default = _v("k"), _v("v"), _v("default")
        axioms: list[FormalAxiomEntry] = []
        empty_dict = _opcall("dict")

        # — empty length —
        axioms.append(FormalAxiomEntry(
            name="dict_len_empty",
            module=_MODULE,
            params=[],
            conclusion=formal_eq(
                _E, op_len(empty_dict), _int_lit(0), PyIntType(),
            ),
            description="len({}) == 0",
        ))

        # — read after write —
        axioms.append(FormalAxiomEntry(
            name="dict_read_after_write",
            module=_MODULE,
            params=[("d", PyDictType()), ("k", PyObjType()), ("v", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_getitem(op_setitem(d, k, v), k),
                v,
                PyObjType(),
            ),
            description="d[k] after d[k]=v gives v  (latest write wins)",
        ))

        # — contains after write —
        axioms.append(FormalAxiomEntry(
            name="dict_contains_after_write",
            module=_MODULE,
            params=[("d", PyDictType()), ("k", PyObjType()), ("v", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_contains(op_setitem(d, k, v), k),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="k in d after d[k]=v is True",
        ))

        # — not contains after delete —
        axioms.append(FormalAxiomEntry(
            name="dict_not_contains_after_del",
            module=_MODULE,
            params=[("d", PyDictType()), ("k", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_contains(_opcall("__delitem__", d, k), k),
                _bool_lit(False),
                PyBoolType(),
            ),
            description="k not in d after del d[k]",
        ))

        # — get with default —
        axioms.append(FormalAxiomEntry(
            name="dict_get_present",
            module=_MODULE,
            params=[("d", PyDictType()), ("k", PyObjType()), ("v", PyObjType()),
                    ("default", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_dict_get(op_setitem(d, k, v), k, default),
                v,
                PyObjType(),
            ),
            description="d.get(k, default) == v when k was just set to v",
        ))

        # — merge override —
        axioms.append(FormalAxiomEntry(
            name="dict_merge_override",
            module=_MODULE,
            params=[("d1", PyDictType()), ("d2", PyDictType()),
                    ("k", PyObjType()), ("v", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_getitem(
                    _opcall("dict.__or__", d1, op_setitem(d2, k, v)),
                    k,
                ),
                v,
                PyObjType(),
            ),
            description="(d1 | d2): values from d2 override d1",
        ))

        # — items roundtrip —
        axioms.append(FormalAxiomEntry(
            name="dict_items_roundtrip",
            module=_MODULE,
            params=[("d", PyDictType())],
            conclusion=formal_eq(
                _E,
                _opcall("dict", op_dict_items(d)),
                d,
                PyDictType(),
            ),
            description="dict(d.items()) == d",
        ))

        # — setdefault present —
        axioms.append(FormalAxiomEntry(
            name="dict_setdefault_present",
            module=_MODULE,
            params=[("d", PyDictType()), ("k", PyObjType()), ("v", PyObjType()),
                    ("default", PyObjType())],
            conclusion=formal_eq(
                _E,
                _opcall("dict.setdefault", op_setitem(d, k, v), k, default),
                v,
                PyObjType(),
            ),
            description="d.setdefault(k, default) returns d[k] when k present",
        ))

        # — pop returns value —
        axioms.append(FormalAxiomEntry(
            name="dict_pop_returns_value",
            module=_MODULE,
            params=[("d", PyDictType()), ("k", PyObjType()), ("v", PyObjType())],
            conclusion=formal_eq(
                _E,
                _opcall("dict.pop", op_setitem(d, k, v), k),
                v,
                PyObjType(),
            ),
            description="d.pop(k) returns d[k]",
        ))

        # — unpack merge equivalence —
        axioms.append(FormalAxiomEntry(
            name="dict_unpack_eq_merge",
            module=_MODULE,
            params=[("d1", PyDictType()), ("d2", PyDictType())],
            conclusion=formal_eq(
                _E,
                _opcall("dict_unpack", d1, d2),
                _opcall("dict.__or__", d1, d2),
                PyDictType(),
            ),
            description="{**d1, **d2} == d1 | d2",
        ))

        return axioms


# ═══════════════════════════════════════════════════════════════════
# 5. Set Semantics
# ═══════════════════════════════════════════════════════════════════

class SetSemantics:
    """Sets as unordered collections with unique elements.

    Axioms capture the lattice structure (union, intersection,
    difference, symmetric difference) and the subset ordering.
    """

    def set_axioms(self) -> list[FormalAxiomEntry]:
        """Core set axioms."""
        s, s1, s2 = _v("s"), _v("s1"), _v("s2")
        x = _v("x")
        xs = _v("xs")
        axioms: list[FormalAxiomEntry] = []

        # — add containment —
        axioms.append(FormalAxiomEntry(
            name="set_add_contains",
            module=_MODULE,
            params=[("s", PySetType()), ("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_contains(op_set_add(s, x), x),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="x in (s | {x}) is True",
        ))

        # — union commutativity —
        axioms.append(FormalAxiomEntry(
            name="set_union_commutative",
            module=_MODULE,
            params=[("s1", PySetType()), ("s2", PySetType())],
            conclusion=formal_eq(
                _E,
                op_set_union(s1, s2),
                op_set_union(s2, s1),
                PySetType(),
            ),
            description="s1 | s2 == s2 | s1",
        ))

        # — intersection commutativity —
        axioms.append(FormalAxiomEntry(
            name="set_intersection_commutative",
            module=_MODULE,
            params=[("s1", PySetType()), ("s2", PySetType())],
            conclusion=formal_eq(
                _E,
                op_set_intersection(s1, s2),
                op_set_intersection(s2, s1),
                PySetType(),
            ),
            description="s1 & s2 == s2 & s1",
        ))

        # — union associativity —
        axioms.append(FormalAxiomEntry(
            name="set_union_associative",
            module=_MODULE,
            params=[("s1", PySetType()), ("s2", PySetType()), ("s", PySetType())],
            conclusion=formal_eq(
                _E,
                op_set_union(op_set_union(s1, s2), s),
                op_set_union(s1, op_set_union(s2, s)),
                PySetType(),
            ),
            description="(s1 | s2) | s3 == s1 | (s2 | s3)",
        ))

        # — symmetric difference —
        axioms.append(FormalAxiomEntry(
            name="set_symmetric_diff",
            module=_MODULE,
            params=[("s1", PySetType()), ("s2", PySetType())],
            conclusion=formal_eq(
                _E,
                _opcall("set.__xor__", s1, s2),
                _opcall("set.__sub__",
                        op_set_union(s1, s2),
                        op_set_intersection(s1, s2)),
                PySetType(),
            ),
            description="s1 ^ s2 == (s1 | s2) - (s1 & s2)",
        ))

        # — difference semantics —
        axioms.append(FormalAxiomEntry(
            name="set_diff_not_in",
            module=_MODULE,
            params=[("s1", PySetType()), ("s2", PySetType()), ("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_contains(_opcall("set.__sub__", s1, s2), x),
                op_and(op_contains(s1, x), op_not(op_contains(s2, x))),
                PyBoolType(),
            ),
            description="x in (s1 - s2) ↔ x in s1 and x not in s2",
        ))

        # — subset —
        axioms.append(FormalAxiomEntry(
            name="set_subset_intersection",
            module=_MODULE,
            params=[("s1", PySetType()), ("s2", PySetType())],
            conclusion=formal_eq(
                _E,
                _opcall("set.__le__", s1, s2),
                op_eq(op_set_intersection(s1, s2), s1),
                PyBoolType(),
            ),
            description="s1 <= s2 ↔ s1 & s2 == s1",
        ))

        # — deduplication —
        axioms.append(FormalAxiomEntry(
            name="set_dedup",
            module=_MODULE,
            params=[("xs", PyListType())],
            conclusion=formal_eq(
                _E,
                op_le(op_len(_opcall("set", xs)), op_len(xs)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="len(set(xs)) <= len(xs)",
        ))

        # — frozenset is hashable —
        axioms.append(FormalAxiomEntry(
            name="frozenset_hashable",
            module=_MODULE,
            params=[("s", PySetType())],
            conclusion=Judgment(
                kind=JudgmentKind.TYPE_CHECK,
                context=_E,
                term=op_hash(_opcall("frozenset", s)),
                type_=PyIntType(),
            ),
            description="frozenset(s) is hashable  (hash returns int)",
        ))

        # — union idempotence —
        axioms.append(FormalAxiomEntry(
            name="set_union_idempotent",
            module=_MODULE,
            params=[("s", PySetType())],
            conclusion=formal_eq(
                _E,
                op_set_union(s, s),
                s,
                PySetType(),
            ),
            description="s | s == s",
        ))

        return axioms


# ═══════════════════════════════════════════════════════════════════
# 6. Tuple Semantics
# ═══════════════════════════════════════════════════════════════════

class TupleSemantics:
    """Tuples as immutable sequences.

    Because tuples are frozen, the axioms are purely equational —
    no mutation post-conditions are needed.
    """

    def tuple_axioms(self) -> list[FormalAxiomEntry]:
        """Core tuple axioms."""
        t1, t2 = _v("t1"), _v("t2")
        x, y = _v("x"), _v("y")
        axioms: list[FormalAxiomEntry] = []

        # — concat length —
        axioms.append(FormalAxiomEntry(
            name="tuple_concat_len",
            module=_MODULE,
            params=[("t1", PyTupleType()), ("t2", PyTupleType())],
            conclusion=formal_eq(
                _E,
                op_len(op_add(t1, t2)),
                op_add(op_len(t1), op_len(t2)),
                PyIntType(),
            ),
            description="len(t1 + t2) == len(t1) + len(t2)",
        ))

        # — single-element tuple —
        axioms.append(FormalAxiomEntry(
            name="tuple_singleton_len",
            module=_MODULE,
            params=[("x", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_len(_opcall("tuple_of", x)),
                _int_lit(1),
                PyIntType(),
            ),
            description="len((x,)) == 1",
        ))

        # — unpacking —
        axioms.append(FormalAxiomEntry(
            name="tuple_unpack_pair",
            module=_MODULE,
            params=[("x", PyObjType()), ("y", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_getitem(_opcall("tuple_of", x, y), _int_lit(0)),
                x,
                PyObjType(),
            ),
            description="(x, y)[0] == x  (tuple unpacking)",
        ))
        axioms.append(FormalAxiomEntry(
            name="tuple_unpack_pair_snd",
            module=_MODULE,
            params=[("x", PyObjType()), ("y", PyObjType())],
            conclusion=formal_eq(
                _E,
                op_getitem(_opcall("tuple_of", x, y), _int_lit(1)),
                y,
                PyObjType(),
            ),
            description="(x, y)[1] == y",
        ))

        # — tuple hashability (elements must be hashable) —
        axioms.append(FormalAxiomEntry(
            name="tuple_hashable",
            module=_MODULE,
            params=[("x", PyObjType()), ("y", PyObjType())],
            conclusion=Judgment(
                kind=JudgmentKind.TYPE_CHECK,
                context=_E,
                term=op_hash(_opcall("tuple_of", x, y)),
                type_=PyIntType(),
            ),
            description="hash((x, y)) : int  (when elements are hashable)",
        ))

        # — named tuple field access —
        axioms.append(FormalAxiomEntry(
            name="namedtuple_field_eq_index",
            module=_MODULE,
            params=[("nt", PyTupleType())],
            conclusion=formal_eq(
                _E,
                _opcall("getattr", _v("nt"), _str_lit("_field_0")),
                op_getitem(_v("nt"), _int_lit(0)),
                PyObjType(),
            ),
            description="nt.field == nt[index]  (named tuple access)",
        ))

        return axioms


# ═══════════════════════════════════════════════════════════════════
# 7. Boolean / Truthiness Semantics
# ═══════════════════════════════════════════════════════════════════

class BooleanSemantics:
    """Python truthiness rules.

    Python's ``bool()`` coercion is non-trivial: falsy values include
    ``None``, zero numerics, empty containers, and objects with
    ``__bool__`` returning ``False`` or ``__len__`` returning ``0``.
    The short-circuit semantics of ``and``/``or`` are also axiomatised.
    """

    def truthiness_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for Python's truthiness protocol."""
        a, b = _v("a"), _v("b")
        axioms: list[FormalAxiomEntry] = []

        # — falsy atoms —
        for val, desc in [
            (None,  "bool(None) == False"),
            (0,     "bool(0) == False"),
            (0.0,   "bool(0.0) == False"),
            ("",    'bool("") == False'),
            (False, "bool(False) == False"),
        ]:
            axioms.append(FormalAxiomEntry(
                name=f"bool_falsy_{type(val).__name__}_{val!r}",
                module=_MODULE,
                params=[],
                conclusion=formal_eq(
                    _E,
                    op_bool(_lit(val)),
                    _bool_lit(False),
                    PyBoolType(),
                ),
                description=desc,
            ))

        # — empty containers are falsy —
        for container_name, op_name in [
            ("list",  "list"),
            ("dict",  "dict"),
            ("set",   "set"),
            ("tuple", "tuple"),
        ]:
            axioms.append(FormalAxiomEntry(
                name=f"bool_falsy_empty_{container_name}",
                module=_MODULE,
                params=[],
                conclusion=formal_eq(
                    _E,
                    op_bool(_opcall(op_name)),
                    _bool_lit(False),
                    PyBoolType(),
                ),
                description=f"bool({container_name}()) == False  (empty container)",
            ))

        # — non-empty container is truthy (via len > 0) —
        axioms.append(FormalAxiomEntry(
            name="bool_truthy_nonempty",
            module=_MODULE,
            params=[("a", PyObjType())],
            conclusion=formal_eq(
                _E,
                _opcall("implies",
                        op_gt(op_len(a), _int_lit(0)),
                        op_eq(op_bool(a), _bool_lit(True))),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="len(x) > 0 → bool(x) == True  (non-empty is truthy)",
        ))

        # — short-circuit and —
        axioms.append(FormalAxiomEntry(
            name="and_short_circuit_false",
            module=_MODULE,
            params=[("a", PyObjType()), ("b", PyObjType())],
            conclusion=formal_eq(
                _E,
                _opcall("implies",
                        op_eq(op_bool(a), _bool_lit(False)),
                        op_eq(op_and(a, b), a)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="a and b → a when a is falsy  (short-circuit)",
        ))

        # — short-circuit or —
        axioms.append(FormalAxiomEntry(
            name="or_short_circuit_true",
            module=_MODULE,
            params=[("a", PyObjType()), ("b", PyObjType())],
            conclusion=formal_eq(
                _E,
                _opcall("implies",
                        op_eq(op_bool(a), _bool_lit(True)),
                        op_eq(op_or(a, b), a)),
                _bool_lit(True),
                PyBoolType(),
            ),
            description="a or b → a when a is truthy  (short-circuit)",
        ))

        # — bool(True) == True (idempotent) —
        axioms.append(FormalAxiomEntry(
            name="bool_idempotent",
            module=_MODULE,
            params=[("a", PyBoolType())],
            conclusion=formal_eq(
                _E, op_bool(a), a, PyBoolType(),
            ),
            description="bool(bool_val) == bool_val  (idempotent)",
        ))

        # — not involution —
        axioms.append(FormalAxiomEntry(
            name="not_involution",
            module=_MODULE,
            params=[("a", PyBoolType())],
            conclusion=formal_eq(
                _E, op_not(op_not(a)), a, PyBoolType(),
            ),
            description="not (not a) == a",
        ))

        # — De Morgan —
        axioms.append(FormalAxiomEntry(
            name="de_morgan_and",
            module=_MODULE,
            params=[("a", PyBoolType()), ("b", PyBoolType())],
            conclusion=formal_eq(
                _E,
                op_not(op_and(a, b)),
                op_or(op_not(a), op_not(b)),
                PyBoolType(),
            ),
            description="not (a and b) == (not a) or (not b)",
        ))
        axioms.append(FormalAxiomEntry(
            name="de_morgan_or",
            module=_MODULE,
            params=[("a", PyBoolType()), ("b", PyBoolType())],
            conclusion=formal_eq(
                _E,
                op_not(op_or(a, b)),
                op_and(op_not(a), op_not(b)),
                PyBoolType(),
            ),
            description="not (a or b) == (not a) and (not b)",
        ))

        return axioms


# ═══════════════════════════════════════════════════════════════════
# 8. Collect all axioms
# ═══════════════════════════════════════════════════════════════════

def all_data_axioms() -> list[FormalAxiomEntry]:
    """Return every data-model axiom for use by the proof kernel."""
    axioms: list[FormalAxiomEntry] = []

    num = NumericSemantics()
    axioms.extend(num.numeric_tower_axioms())
    axioms.extend(num.coercion_axioms())

    axioms.extend(StringSemantics().string_axioms())

    lst = ListSemantics()
    axioms.extend(lst.list_axioms())
    axioms.extend(lst.slice_axioms())

    axioms.extend(DictSemantics().dict_axioms())
    axioms.extend(SetSemantics().set_axioms())
    axioms.extend(TupleSemantics().tuple_axioms())
    axioms.extend(BooleanSemantics().truthiness_axioms())

    return axioms


# ═══════════════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════════════

def _self_test() -> None:
    """Smoke-test the axiom library."""
    all_ax = all_data_axioms()

    # 1. non-trivial count
    assert len(all_ax) >= 60, f"Expected ≥60 axioms, got {len(all_ax)}"

    # 2. every axiom has a name and module
    for ax in all_ax:
        assert ax.name, f"Axiom missing name: {ax}"
        assert ax.module == _MODULE, f"Axiom {ax.name} has wrong module {ax.module}"

    # 3. no duplicate names
    names = [ax.name for ax in all_ax]
    dupes = [n for n in names if names.count(n) > 1]
    assert not dupes, f"Duplicate axiom names: {set(dupes)}"

    # 4. every axiom has a conclusion
    for ax in all_ax:
        assert ax.conclusion is not None, f"Axiom {ax.name} has no conclusion"
        assert isinstance(ax.conclusion, Judgment), (
            f"Axiom {ax.name}: conclusion is {type(ax.conclusion)}, expected Judgment"
        )

    # 5. spot-check specific axioms exist
    name_set = set(names)
    for expected in [
        "add_commutative", "mul_distributes_over_add",
        "str_concat_assoc", "str_len_empty",
        "list_append_len", "sorted_idempotent",
        "dict_read_after_write", "dict_items_roundtrip",
        "set_union_commutative", "set_symmetric_diff",
        "tuple_concat_len", "tuple_unpack_pair",
        "bool_falsy_NoneType_None", "not_involution",
        "de_morgan_and", "de_morgan_or",
    ]:
        assert expected in name_set, f"Missing expected axiom: {expected}"

    # 6. check judgment kinds are correct for subtype axioms
    for ax in all_ax:
        if "subtype" in ax.name:
            assert ax.conclusion.kind == JudgmentKind.SUBTYPE, (
                f"{ax.name} should be SUBTYPE judgment"
            )

    # 7. check equality axioms have left and right
    for ax in all_ax:
        if ax.conclusion.kind == JudgmentKind.EQUAL:
            assert ax.conclusion.left is not None, f"{ax.name} missing left"
            assert ax.conclusion.right is not None, f"{ax.name} missing right"

    # 8. per-class axiom counts
    num = NumericSemantics()
    assert len(num.numeric_tower_axioms()) >= 12, "Need ≥12 numeric tower axioms"
    assert len(num.coercion_axioms()) >= 4, "Need ≥4 coercion axioms"
    assert len(StringSemantics().string_axioms()) >= 8, "Need ≥8 string axioms"
    lst = ListSemantics()
    assert len(lst.list_axioms()) >= 15, "Need ≥15 list axioms"
    assert len(lst.slice_axioms()) >= 2, "Need ≥2 slice axioms"
    assert len(DictSemantics().dict_axioms()) >= 8, "Need ≥8 dict axioms"
    assert len(SetSemantics().set_axioms()) >= 8, "Need ≥8 set axioms"
    assert len(TupleSemantics().tuple_axioms()) >= 5, "Need ≥5 tuple axioms"
    assert len(BooleanSemantics().truthiness_axioms()) >= 10, "Need ≥10 bool axioms"

    print(f"✓ python_data self-test passed — {len(all_ax)} axioms verified")


if __name__ == "__main__":
    _self_test()
