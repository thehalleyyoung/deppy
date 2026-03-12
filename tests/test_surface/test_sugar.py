"""Tests for the syntactic sugar module — Pythonic dependent types."""

import pytest

from deppy.surface.sugar import (
    # Type aliases
    Int, Float, Str, Bool, NoneType, Bytes,
    _SimpleType, _ParametricType,
    # Variables
    Var, v, x, y, n, Return,
    _TermExpr, _SugarPred,
    # Predicate shorthands
    Eq, Neq, Lt, Gt, Leq, Geq,
    And, Or, Not,
    Len, Shape, Rank, Idx,
    # Conversion
    to_predicate, _term_to_str,
    # Builders
    Ref, Fn, Pair, Dep,
    # Type shortcuts
    Nat, Pos, BoundedInt, Sized, NonEmptyOf, Vec, Tensor, Opt,
    # Decorators
    FunctionSpec, extract_spec, fn, checked, ContractViolation,
    # Pretty-printing
    pretty,
    # Resolution
    _resolve_type,
)
from deppy.types.base import TypeBase, ANY_TYPE, ListType
from deppy.types.refinement import (
    RefinementType, ComparisonPred, ComparisonOp,
    ConjunctionPred, DisjunctionPred, NotPred,
    QualifiedType, NonNull,
)
from deppy.types.dependent import PiType, SigmaType, MultiPiType


# ═══════════════════════════════════════════════════════════════════════════════
# Type aliases
# ═══════════════════════════════════════════════════════════════════════════════


class TestSimpleType:
    def test_primitives_exist(self):
        assert Int.name == "int"
        assert Float.name == "float"
        assert Str.name == "str"
        assert Bool.name == "bool"
        assert NoneType.name == "None"
        assert Bytes.name == "bytes"

    def test_is_type_base(self):
        assert isinstance(Int, TypeBase)
        assert isinstance(Float, TypeBase)

    def test_repr(self):
        assert repr(Int) == "int"
        assert repr(Float) == "float"

    def test_substitute_identity(self):
        assert Int.substitute({}) is Int

    def test_substitute_match(self):
        result = Int.substitute({"int": Float})
        assert result is Float

    def test_free_variables_empty(self):
        assert Int.free_variables() == frozenset()

    def test_frozen(self):
        with pytest.raises(AttributeError):
            Int._name = "changed"  # type: ignore


class TestParametricType:
    def test_creation(self):
        t = _ParametricType("List", (Int,))
        assert t.base == "List"
        assert t.args == (Int,)

    def test_repr(self):
        t = _ParametricType("Dict", (Str, Int))
        assert repr(t) == "Dict[str, int]"

    def test_substitute(self):
        t = _ParametricType("List", (Int,))
        result = t.substitute({"int": Float})
        assert isinstance(result, _ParametricType)

    def test_free_variables(self):
        t = _ParametricType("List", (Int,))
        assert t.free_variables() == frozenset()


# ═══════════════════════════════════════════════════════════════════════════════
# Var and operators
# ═══════════════════════════════════════════════════════════════════════════════


class TestVar:
    def test_name(self):
        var = Var("x")
        assert var.name == "x"

    def test_repr(self):
        assert repr(Var("x")) == "x"

    def test_common_vars(self):
        assert v.name == "v"
        assert x.name == "x"
        assert y.name == "y"
        assert n.name == "n"
        assert Return.name == "__return__"

    def test_gt(self):
        p = v > 0
        assert isinstance(p, _SugarPred)
        assert p.op == "gt"

    def test_ge(self):
        p = v >= 0
        assert isinstance(p, _SugarPred)
        assert p.op == "ge"

    def test_lt(self):
        p = v < 10
        assert isinstance(p, _SugarPred)
        assert p.op == "lt"

    def test_le(self):
        p = v <= 10
        assert isinstance(p, _SugarPred)
        assert p.op == "le"

    def test_eq(self):
        p = (v == 5)
        assert isinstance(p, _SugarPred)
        assert p.op == "eq"

    def test_ne(self):
        p = (v != 0)
        assert isinstance(p, _SugarPred)
        assert p.op == "ne"

    def test_add(self):
        t = v + 1
        assert isinstance(t, _TermExpr)
        assert t.op == "add"

    def test_sub(self):
        t = v - 1
        assert isinstance(t, _TermExpr)
        assert t.op == "sub"

    def test_mul(self):
        t = v * 2
        assert isinstance(t, _TermExpr)
        assert t.op == "mul"

    def test_mod(self):
        t = v % 2
        assert isinstance(t, _TermExpr)
        assert t.op == "mod"

    def test_frozen(self):
        with pytest.raises(AttributeError):
            v._name = "changed"  # type: ignore


class TestTermExpr:
    def test_comparison_from_term(self):
        t = v + 1
        p = t > 0
        assert isinstance(p, _SugarPred)
        assert p.op == "gt"

    def test_ge_from_term(self):
        t = v + 1
        p = t >= 0
        assert isinstance(p, _SugarPred)
        assert p.op == "ge"

    def test_eq_from_term(self):
        t = v + 1
        p = (t == 5)
        assert isinstance(p, _SugarPred)
        assert p.op == "eq"

    def test_repr(self):
        t = v + 1
        assert "add" in repr(t)


# ═══════════════════════════════════════════════════════════════════════════════
# Sugar predicates
# ═══════════════════════════════════════════════════════════════════════════════


class TestSugarPred:
    def test_and(self):
        p = (v > 0) & (v < 100)
        assert p.op == "and"

    def test_or(self):
        p = (v > 0) | (v < 100)
        assert p.op == "or"

    def test_not(self):
        p = ~(v > 0)
        assert p.op == "not"

    def test_repr_gt(self):
        p = v > 0
        assert ">" in repr(p)

    def test_repr_and(self):
        p = (v > 0) & (v < 100)
        assert "∧" in repr(p)

    def test_repr_not(self):
        p = ~(v > 0)
        assert "¬" in repr(p)


class TestPredicateShorthands:
    def test_eq(self):
        p = Eq(v, 5)
        assert p.op == "eq"

    def test_neq(self):
        p = Neq(v, 0)
        assert p.op == "ne"

    def test_lt(self):
        p = Lt(v, 10)
        assert p.op == "lt"

    def test_gt(self):
        p = Gt(v, 0)
        assert p.op == "gt"

    def test_leq(self):
        p = Leq(v, 100)
        assert p.op == "le"

    def test_geq(self):
        p = Geq(v, 0)
        assert p.op == "ge"

    def test_and_multi(self):
        p = And(v > 0, v < 10, v != 5)
        assert p.op == "and"
        # Nested: ((v>0 & v<10) & v!=5)
        assert p.left.op == "and"

    def test_and_single(self):
        p = And(v > 0)
        assert p.op == "gt"

    def test_and_empty(self):
        with pytest.raises(ValueError, match="at least one"):
            And()

    def test_or_multi(self):
        p = Or(v > 0, v < -10)
        assert p.op == "or"

    def test_or_empty(self):
        with pytest.raises(ValueError, match="at least one"):
            Or()

    def test_not_fn(self):
        p = Not(v > 0)
        assert p.op == "not"


class TestTermFunctions:
    def test_len(self):
        t = Len(v)
        assert isinstance(t, _TermExpr)
        assert t.op == "len"

    def test_shape(self):
        t = Shape(v)
        assert isinstance(t, _TermExpr)
        assert t.op == "shape"

    def test_shape_with_dim(self):
        t = Shape(v, 0)
        assert t.right == 0

    def test_rank(self):
        t = Rank(v)
        assert isinstance(t, _TermExpr)
        assert t.op == "rank"

    def test_idx(self):
        t = Idx(v, 0)
        assert isinstance(t, _TermExpr)
        assert t.op == "idx"

    def test_len_comparison(self):
        p = Len(v) > 0
        assert isinstance(p, _SugarPred)
        assert p.op == "gt"


# ═══════════════════════════════════════════════════════════════════════════════
# to_predicate conversion
# ═══════════════════════════════════════════════════════════════════════════════


class TestToPredicate:
    def test_gt(self):
        p = to_predicate(v > 0)
        assert isinstance(p, ComparisonPred)
        assert p.op == ComparisonOp.GT
        assert p.lhs == "v"
        assert p.rhs == "0"

    def test_ge(self):
        p = to_predicate(v >= 0)
        assert isinstance(p, ComparisonPred)
        assert p.op == ComparisonOp.GE

    def test_lt(self):
        p = to_predicate(v < 10)
        assert isinstance(p, ComparisonPred)
        assert p.op == ComparisonOp.LT

    def test_le(self):
        p = to_predicate(v <= 10)
        assert isinstance(p, ComparisonPred)
        assert p.op == ComparisonOp.LE

    def test_eq(self):
        p = to_predicate(v == 5)
        assert isinstance(p, ComparisonPred)
        assert p.op == ComparisonOp.EQ

    def test_ne(self):
        p = to_predicate(v != 0)
        assert isinstance(p, ComparisonPred)
        assert p.op == ComparisonOp.NE

    def test_and(self):
        p = to_predicate((v > 0) & (v < 100))
        assert isinstance(p, ConjunctionPred)

    def test_or(self):
        p = to_predicate((v > 0) | (v < -10))
        assert isinstance(p, DisjunctionPred)

    def test_not(self):
        p = to_predicate(~(v > 0))
        assert isinstance(p, NotPred)

    def test_term_in_comparison(self):
        p = to_predicate(Len(v) > 0)
        assert isinstance(p, ComparisonPred)
        assert "len" in p.lhs

    def test_unknown_op_raises(self):
        bad = _SugarPred("xor", v, x)
        with pytest.raises(ValueError, match="Unknown"):
            to_predicate(bad)


class TestTermToStr:
    def test_var(self):
        assert _term_to_str(Var("x")) == "x"

    def test_literal(self):
        assert _term_to_str(42) == "42"

    def test_term_expr(self):
        t = v + 1
        s = _term_to_str(t)
        assert "v" in s
        assert "add" in s
        assert "1" in s


# ═══════════════════════════════════════════════════════════════════════════════
# Builder: Ref
# ═══════════════════════════════════════════════════════════════════════════════


class TestRef:
    def test_basic(self):
        t = Ref[int, v > 0]
        assert isinstance(t, RefinementType)
        assert t.binder == "v"
        assert isinstance(t.base, _SimpleType)
        assert t.base.name == "int"

    def test_compound_pred(self):
        t = Ref[int, (v > 0) & (v < 100)]
        assert isinstance(t, RefinementType)
        assert isinstance(t.predicate, ConjunctionPred)

    def test_wrong_arity(self):
        with pytest.raises(TypeError, match="Ref requires"):
            Ref[int]

    def test_repr(self):
        assert repr(Ref) == "Ref"


# ═══════════════════════════════════════════════════════════════════════════════
# Builder: Fn
# ═══════════════════════════════════════════════════════════════════════════════


class TestFn:
    def test_simple(self):
        t = Fn[int, str]
        assert isinstance(t, PiType)
        assert isinstance(t.return_type, _SimpleType)

    def test_named_param(self):
        t = Fn[("n", int), str]
        assert isinstance(t, PiType)
        assert t.param_name == "n"

    def test_multi_param(self):
        t = Fn[("x", int), ("y", int), int]
        assert isinstance(t, MultiPiType)
        assert len(t.params) == 2

    def test_not_tuple(self):
        with pytest.raises(TypeError, match="Fn requires"):
            Fn[int]

    def test_repr(self):
        assert repr(Fn) == "Fn"


# ═══════════════════════════════════════════════════════════════════════════════
# Builder: Pair
# ═══════════════════════════════════════════════════════════════════════════════


class TestPair:
    def test_simple(self):
        t = Pair[int, str]
        assert isinstance(t, SigmaType)
        assert t.fst_name == "_fst"

    def test_named(self):
        t = Pair[("n", int), str]
        assert isinstance(t, SigmaType)
        assert t.fst_name == "n"

    def test_wrong_arity(self):
        with pytest.raises(TypeError, match="Pair requires"):
            Pair[int, str, bool]

    def test_repr(self):
        assert repr(Pair) == "Pair"


# ═══════════════════════════════════════════════════════════════════════════════
# Builder: Dep
# ═══════════════════════════════════════════════════════════════════════════════


class TestDep:
    def test_two_args(self):
        name, ty = Dep["n", int]
        assert name == "n"
        assert isinstance(ty, _SimpleType)

    def test_three_args(self):
        name, ty = Dep["n", int, v > 0]
        assert name == "n"
        assert isinstance(ty, RefinementType)
        assert ty.binder == "n"

    def test_wrong_arity(self):
        with pytest.raises(TypeError, match="Dep requires"):
            Dep["a", "b", "c", "d"]

    def test_not_tuple(self):
        with pytest.raises(TypeError, match="Dep requires"):
            Dep["n"]

    def test_repr(self):
        assert repr(Dep) == "Dep"


# ═══════════════════════════════════════════════════════════════════════════════
# Type shortcuts
# ═══════════════════════════════════════════════════════════════════════════════


class TestNatPos:
    def test_nat_is_refinement(self):
        assert isinstance(Nat, RefinementType)
        assert Nat.binder == "v"
        assert isinstance(Nat.predicate, ComparisonPred)
        assert Nat.predicate.op == ComparisonOp.GE

    def test_pos_is_refinement(self):
        assert isinstance(Pos, RefinementType)
        assert Pos.predicate.op == ComparisonOp.GT


class TestBoundedInt:
    def test_basic(self):
        t = BoundedInt(0, 255)
        assert isinstance(t, RefinementType)
        assert isinstance(t.predicate, ConjunctionPred)

    def test_custom_base(self):
        t = BoundedInt(0.0, 1.0, float)
        assert isinstance(t, RefinementType)
        assert t.base.name == "float"


class TestSized:
    def test_basic(self):
        t = Sized(v > 0)
        assert isinstance(t, RefinementType)
        assert t.base.name == "Sequence"

    def test_with_element(self):
        t = Sized(v > 0, int)
        assert isinstance(t, RefinementType)
        assert isinstance(t.base, ListType)


class TestNonEmptyOf:
    def test_basic(self):
        t = NonEmptyOf[list]
        assert isinstance(t, RefinementType)
        assert "len" in str(t.predicate)

    def test_list_int(self):
        t = NonEmptyOf[Int]
        assert isinstance(t, RefinementType)
        assert t.base is Int

    def test_repr(self):
        assert repr(NonEmptyOf) == "NonEmptyOf"


class TestVec:
    def test_with_length(self):
        t = Vec[int, 3]
        assert isinstance(t, RefinementType)
        assert "len" in str(t.predicate)
        assert "3" in str(t.predicate)

    def test_dependent_length(self):
        t = Vec[int, "n"]
        assert isinstance(t, RefinementType)
        assert "n" in str(t.predicate)

    def test_no_length(self):
        t = Vec[int]
        assert isinstance(t, ListType)

    def test_repr(self):
        assert repr(Vec) == "Vec"


class TestTensor:
    def test_basic(self):
        t = Tensor[float, 3, 4]
        assert isinstance(t, RefinementType)
        assert "shape" in str(t.predicate)
        assert "(3, 4)" in str(t.predicate)

    def test_dependent(self):
        t = Tensor[float, "batch", "hidden"]
        assert isinstance(t, RefinementType)
        assert "batch" in str(t.predicate)

    def test_wrong_arity(self):
        with pytest.raises(TypeError, match="Tensor requires"):
            Tensor[float]

    def test_repr(self):
        assert repr(Tensor) == "Tensor"


class TestOpt:
    def test_basic(self):
        t = Opt[int]
        assert isinstance(t, QualifiedType)
        assert len(t.qualifiers) == 1
        assert isinstance(t.qualifiers[0], NonNull)

    def test_repr(self):
        assert repr(Opt) == "Opt"


# ═══════════════════════════════════════════════════════════════════════════════
# Type resolution
# ═══════════════════════════════════════════════════════════════════════════════


class TestResolveType:
    def test_type_base_passthrough(self):
        assert _resolve_type(Int) is Int

    def test_python_int(self):
        t = _resolve_type(int)
        assert isinstance(t, _SimpleType)
        assert t.name == "int"

    def test_python_float(self):
        t = _resolve_type(float)
        assert t.name == "float"

    def test_string(self):
        t = _resolve_type("MyClass")
        assert isinstance(t, _SimpleType)
        assert t.name == "MyClass"

    def test_class(self):
        class Foo:
            pass
        t = _resolve_type(Foo)
        assert isinstance(t, _SimpleType)
        assert t.name == "Foo"

    def test_fallback(self):
        t = _resolve_type(42)
        assert isinstance(t, _SimpleType)


# ═══════════════════════════════════════════════════════════════════════════════
# Decorator: @fn
# ═══════════════════════════════════════════════════════════════════════════════


class TestFnDecorator:
    def test_basic(self):
        @fn
        def add(x: int, y: int) -> int:
            return x + y

        assert hasattr(add, "__deppy_spec__")
        spec = add.__deppy_spec__
        assert spec.name == "add"
        assert len(spec.params) == 2
        assert spec.params[0][0] == "x"

    def test_no_annotations(self):
        @fn
        def bare(x, y):
            return x + y

        spec = bare.__deppy_spec__
        assert len(spec.params) == 2
        assert spec.params[0][1] is ANY_TYPE

    def test_refinement_annotation(self):
        @fn
        def positive_fn(n: Pos) -> int:
            return n

        spec = positive_fn.__deppy_spec__
        assert isinstance(spec.params[0][1], RefinementType)

    def test_return_type(self):
        @fn
        def identity(x: int) -> int:
            return x

        spec = identity.__deppy_spec__
        assert spec.return_type.name == "int"

    def test_function_still_works(self):
        @fn
        def add(x: int, y: int) -> int:
            return x + y
        assert add(2, 3) == 5


class TestExtractSpec:
    def test_basic(self):
        def foo(x: int, y: str) -> bool:
            pass

        spec = extract_spec(foo)
        assert spec.name == "foo"
        assert len(spec.params) == 2
        assert spec.params[0] == ("x", Int)
        assert spec.params[1] == ("y", Str)

    def test_to_pi_type_single(self):
        def f(x: int) -> int:
            pass

        spec = extract_spec(f)
        pi = spec.to_pi_type()
        assert isinstance(pi, PiType)

    def test_to_pi_type_multi(self):
        def f(x: int, y: int) -> int:
            pass

        spec = extract_spec(f)
        pi = spec.to_pi_type()
        assert isinstance(pi, MultiPiType)

    def test_to_pi_type_empty(self):
        def f() -> int:
            pass

        spec = extract_spec(f)
        pi = spec.to_pi_type()
        assert isinstance(pi, _SimpleType)

    def test_is_dependent_false(self):
        def f(x: int) -> int:
            pass

        spec = extract_spec(f)
        assert not spec.is_dependent

    def test_skips_self(self):
        def method(self, x: int) -> int:
            pass

        spec = extract_spec(method)
        assert len(spec.params) == 1
        assert spec.params[0][0] == "x"


class TestFunctionSpec:
    def test_repr(self):
        def f(x: int) -> int:
            pass

        spec = extract_spec(f)
        r = repr(spec)
        assert "FunctionSpec" in r
        assert "f" in r
        assert "x" in r


# ═══════════════════════════════════════════════════════════════════════════════
# Decorator: @checked
# ═══════════════════════════════════════════════════════════════════════════════


class TestCheckedDecorator:
    def test_passes_valid(self):
        @checked
        def inc(n: Pos) -> int:
            return n + 1

        assert inc(5) == 6

    def test_fails_invalid(self):
        @checked
        def inc(n: Pos) -> int:
            return n + 1

        with pytest.raises(ContractViolation) as exc_info:
            inc(0)
        assert exc_info.value.param == "n"
        assert exc_info.value.value == 0

    def test_negative_fails(self):
        @checked
        def inc(n: Pos) -> int:
            return n + 1

        with pytest.raises(ContractViolation):
            inc(-5)

    def test_has_spec(self):
        @checked
        def f(x: int) -> int:
            return x

        assert hasattr(f, "__deppy_spec__")

    def test_bounded_check(self):
        byte_type = BoundedInt(0, 255)

        @checked
        def to_byte(n: byte_type) -> int:
            return n

        assert to_byte(128) == 128
        with pytest.raises(ContractViolation):
            to_byte(256)
        with pytest.raises(ContractViolation):
            to_byte(-1)

    def test_non_empty_check(self):
        ne_list = NonEmptyOf[list]

        @checked
        def head(xs: ne_list) -> int:
            return xs[0]

        assert head([1, 2, 3]) == 1
        with pytest.raises(ContractViolation):
            head([])

    def test_preserves_name(self):
        @checked
        def my_func(x: int) -> int:
            return x

        assert my_func.__name__ == "my_func"


class TestContractViolation:
    def test_message(self):
        e = ContractViolation("x", 42, Pos)
        assert "x" in str(e)
        assert "42" in str(e)

    def test_attributes(self):
        e = ContractViolation("x", 42, Pos)
        assert e.param == "x"
        assert e.value == 42
        assert e.refinement is Pos


# ═══════════════════════════════════════════════════════════════════════════════
# Pretty-printing
# ═══════════════════════════════════════════════════════════════════════════════


class TestPretty:
    def test_nat(self):
        s = pretty(Nat)
        assert "v" in s
        assert "int" in s
        assert ">=" in s

    def test_pos(self):
        s = pretty(Pos)
        assert ">" in s
        assert "int" in s

    def test_pi(self):
        t = PiType("n", Int, Str)
        s = pretty(t)
        assert "n" in s
        assert "int" in s
        assert "->" in s
        assert "str" in s

    def test_multi_pi(self):
        t = MultiPiType((("x", Int), ("y", Int)), Str)
        s = pretty(t)
        assert "x" in s
        assert "y" in s
        assert "->" in s

    def test_sigma_named(self):
        t = SigmaType("n", Int, Str)
        s = pretty(t)
        assert "n" in s
        assert "int" in s

    def test_sigma_unnamed(self):
        t = SigmaType("_fst", Int, Str)
        s = pretty(t)
        assert "×" in s

    def test_refinement(self):
        s = pretty(Ref[int, v > 0])
        assert "{" in s
        assert "v" in s
        assert "int" in s
        assert "|" in s

    def test_qualified(self):
        s = pretty(Opt[int])
        assert "int" in s
        assert "NonNull" in s

    def test_simple_type(self):
        assert pretty(Int) == "int"
        assert pretty(Float) == "float"

    def test_parametric(self):
        t = _ParametricType("Dict", (Str, Int))
        s = pretty(t)
        assert "Dict" in s
        assert "str" in s
        assert "int" in s

    def test_vec_with_length(self):
        t = Vec[int, 3]
        s = pretty(t)
        assert "List" in s
        assert "len" in s

    def test_fn_builder_pretty(self):
        t = Fn[("n", Nat), Int]
        s = pretty(t)
        assert "n" in s
        assert "->" in s

    def test_bounded_pretty(self):
        t = BoundedInt(0, 255)
        s = pretty(t)
        assert "int" in s
        assert ">=" in s
        assert "<=" in s


# ═══════════════════════════════════════════════════════════════════════════════
# Integration: combining sugar components
# ═══════════════════════════════════════════════════════════════════════════════


class TestIntegration:
    def test_dep_in_fn(self):
        """Dep bindings can be used in Fn."""
        binding = Dep["n", int]
        t = Fn[binding, Int]
        assert isinstance(t, PiType)
        assert t.param_name == "n"

    def test_dep_in_pair(self):
        """Dep bindings can be used in Pair."""
        binding = Dep["n", int]
        t = Pair[binding, Int]
        assert isinstance(t, SigmaType)
        assert t.fst_name == "n"

    def test_nested_refinement_in_fn(self):
        """Refined types work in Fn params."""
        t = Fn[("n", Pos), Int]
        assert isinstance(t, PiType)
        assert isinstance(t.param_type, RefinementType)

    def test_vec_in_fn(self):
        """Vec types work in Fn."""
        t = Fn[("xs", Vec[int, 3]), Int]
        assert isinstance(t, PiType)
        assert isinstance(t.param_type, RefinementType)

    def test_tensor_in_fn(self):
        """Tensor types work in Fn."""
        t = Fn[("t", Tensor[float, 3, 4]), Float]
        assert isinstance(t, PiType)
        assert isinstance(t.param_type, RefinementType)

    def test_full_dependent_type(self):
        """Build a full dependent function type with sugar."""
        # (n: Nat) -> Vec[int, n]
        t = Fn[("n", Nat), Vec[int, "n"]]
        assert isinstance(t, PiType)
        assert t.param_name == "n"
        assert isinstance(t.return_type, RefinementType)
        assert "n" in str(t.return_type.predicate)

    def test_checked_with_nat(self):
        """@checked works with Nat."""
        @checked
        def f(n: Nat) -> int:
            return n

        assert f(0) == 0
        assert f(5) == 5
        with pytest.raises(ContractViolation):
            f(-1)

    def test_pretty_complex(self):
        """Pretty-print a complex type."""
        t = Fn[("n", Nat), Vec[int, "n"]]
        s = pretty(t)
        assert "n" in s
        assert "->" in s

    def test_predicate_roundtrip(self):
        """Sugar predicate → real predicate → use in refinement."""
        sp = (v > 0) & (v < 100)
        pred = to_predicate(sp)
        t = RefinementType(Int, "v", pred)
        assert isinstance(t, RefinementType)
        assert isinstance(t.predicate, ConjunctionPred)
