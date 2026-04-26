"""Phase U6 — comprehensive type-translator coverage.

The translator should render *every* importable Python typing-system
construct rather than defaulting to opaque axioms.  Each test below
locks down a specific shape; together they enumerate the surface area
the translator commits to.
"""
from __future__ import annotations

import pytest

from deppy.lean.type_translation import (
    Context, TypeVarSpec,
    translate_annotation_str,
)


# ─────────────────────────────────────────────────────────────────────
# Scalars and built-ins
# ─────────────────────────────────────────────────────────────────────

class TestScalars:
    @pytest.mark.parametrize("py,lean", [
        ("int", "Int"),
        ("float", "Float"),
        ("str", "String"),
        ("bool", "Bool"),
        ("bytes", "ByteArray"),
        ("bytearray", "ByteArray"),
        ("complex", "Complex"),
        ("None", "Unit"),
        ("object", "α"),
        ("Any", "α"),
    ])
    def test_scalar(self, py: str, lean: str) -> None:
        assert translate_annotation_str(py).lean == lean


# ─────────────────────────────────────────────────────────────────────
# Generic containers — every typing alias and collections.abc form
# ─────────────────────────────────────────────────────────────────────

class TestGenericContainers:
    @pytest.mark.parametrize("py", [
        "list[int]", "List[int]",
        "Iterable[int]", "Iterator[int]",
        "Sequence[int]", "MutableSequence[int]",
        "Generator[int]", "Container[int]",
        "Reversible[int]", "Collection[int]",
        "AbstractSet[int]", "MutableSet[int]",
    ])
    def test_list_like_translates_to_list(self, py: str) -> None:
        assert translate_annotation_str(py).lean == "(List Int)"

    @pytest.mark.parametrize("py", [
        "dict[str, int]", "Dict[str, int]",
        "Mapping[str, int]", "MutableMapping[str, int]",
        "OrderedDict[str, int]",
        "defaultdict[str, int]", "Counter[str, int]",
    ])
    def test_dict_like_translates_to_hashmap(self, py: str) -> None:
        assert translate_annotation_str(py).lean == "(Std.HashMap String Int)"

    def test_tuple_homogeneous(self) -> None:
        assert translate_annotation_str(
            "tuple[int, ...]"
        ).lean == "(List Int)"

    def test_tuple_heterogeneous(self) -> None:
        assert translate_annotation_str(
            "tuple[int, str, bool]"
        ).lean == "(Int × String × Bool)"

    @pytest.mark.parametrize("py", [
        "set[int]", "frozenset[int]", "Set[int]", "FrozenSet[int]",
    ])
    def test_set_like(self, py: str) -> None:
        assert translate_annotation_str(py).lean == "(List Int)"

    def test_async_types(self) -> None:
        assert translate_annotation_str(
            "Awaitable[int]"
        ).lean == "(Task Int)"
        assert translate_annotation_str(
            "Coroutine[int]"
        ).lean == "(Task Int)"
        assert translate_annotation_str(
            "AsyncIterable[int]"
        ).lean == "(Task Int)"


# ─────────────────────────────────────────────────────────────────────
# Unions — recursive, not opaque
# ─────────────────────────────────────────────────────────────────────

class TestUnions:
    def test_pep604_pair(self) -> None:
        assert translate_annotation_str(
            "int | str"
        ).lean == "(Sum Int String)"

    def test_pep604_triple_recursive(self) -> None:
        assert translate_annotation_str(
            "int | str | bytes"
        ).lean == "(Sum (Sum Int String) ByteArray)"

    def test_pep604_long(self) -> None:
        # 5-element union nests four times.
        r = translate_annotation_str("int | str | bytes | float | bool")
        assert r.lean == "(Sum (Sum (Sum (Sum Int String) ByteArray) Float) Bool)"
        # No opaque axiom emitted.
        assert not any("Deppy_Union" in d for d in r.aux_decls)

    def test_typing_union(self) -> None:
        assert translate_annotation_str(
            "Union[int, str]"
        ).lean == "(Sum Int String)"
        assert translate_annotation_str(
            "Union[int, str, bytes]"
        ).lean == "(Sum (Sum Int String) ByteArray)"

    def test_optional_alone(self) -> None:
        assert translate_annotation_str(
            "Optional[int]"
        ).lean == "(Option Int)"
        assert translate_annotation_str(
            "int | None"
        ).lean == "(Option Int)"

    def test_optional_of_union(self) -> None:
        assert translate_annotation_str(
            "int | str | None"
        ).lean == "(Option (Sum Int String))"
        assert translate_annotation_str(
            "Optional[int | str]"
        ).lean == "(Option (Sum Int String))"


# ─────────────────────────────────────────────────────────────────────
# Callable — direct, higher-order, ParamSpec / Concatenate
# ─────────────────────────────────────────────────────────────────────

class TestCallable:
    def test_simple(self) -> None:
        assert translate_annotation_str(
            "Callable[[int, int], int]"
        ).lean == "(Int → Int → Int)"

    def test_no_args(self) -> None:
        assert translate_annotation_str(
            "Callable[[], int]"
        ).lean == "(Unit → Int)"

    def test_ellipsis_args(self) -> None:
        r = translate_annotation_str("Callable[..., int]")
        assert "α" in r.lean
        assert "Int" in r.lean

    def test_higher_order(self) -> None:
        r = translate_annotation_str(
            "Callable[[Callable[[int], int]], int]"
        )
        assert r.lean == "((Int → Int) → Int)"

    def test_callable_returning_optional(self) -> None:
        assert translate_annotation_str(
            "Callable[[int], int | None]"
        ).lean == "(Int → (Option Int))"

    def test_concatenate_form(self) -> None:
        """Phase U6: ``Callable[Concatenate[A, P], R]`` translates
        with the concrete prefix and an ``α`` for the variadic."""
        r = translate_annotation_str(
            "Callable[Concatenate[int, P], str]"
        )
        # Front prefix is ``int``, ParamSpec ``P`` is ``α``.
        assert r.lean == "(Int → α → String)"


# ─────────────────────────────────────────────────────────────────────
# Annotated / Final / ClassVar / NewType / Self / TypedDict markers
# ─────────────────────────────────────────────────────────────────────

class TestStrippedQualifiers:
    @pytest.mark.parametrize("py,expected", [
        ("Annotated[int, 'metadata']", "Int"),
        ("Annotated[list[int], 'note', 'extra']", "(List Int)"),
        ("Final[int]", "Int"),
        ("Final[list[int]]", "(List Int)"),
        ("ClassVar[int]", "Int"),
        ("ClassVar[Optional[int]]", "(Option Int)"),
        ("Required[int]", "Int"),
        ("NotRequired[str]", "String"),
    ])
    def test_qualifier_strips(self, py: str, expected: str) -> None:
        assert translate_annotation_str(py).lean == expected

    def test_typeguard_is_bool(self) -> None:
        assert translate_annotation_str("TypeGuard[int]").lean == "Bool"
        assert translate_annotation_str("TypeIs[str]").lean == "Bool"


# ─────────────────────────────────────────────────────────────────────
# Literal
# ─────────────────────────────────────────────────────────────────────

class TestLiteral:
    def test_int_literals(self) -> None:
        assert translate_annotation_str(
            "Literal[1, 2, 3]"
        ).lean == "Int"

    def test_str_literals(self) -> None:
        assert translate_annotation_str(
            "Literal['x', 'y']"
        ).lean == "String"

    def test_bool_literals(self) -> None:
        assert translate_annotation_str(
            "Literal[True, False]"
        ).lean == "Bool"

    def test_heterogeneous_falls_back(self) -> None:
        r = translate_annotation_str("Literal[1, 'a']")
        assert "Deppy_" in r.lean


# ─────────────────────────────────────────────────────────────────────
# TypeVar / NewType / TypeAlias context
# ─────────────────────────────────────────────────────────────────────

class TestContextDriven:
    def test_typevar_unbound_is_polymorphic(self) -> None:
        ctx = Context(type_vars={"T": TypeVarSpec(name="T")})
        r = translate_annotation_str("T", context=ctx)
        assert r.lean.startswith("Deppy_TypeVar_T")

    def test_typevar_bound_uses_bound_type(self) -> None:
        ctx = Context(type_vars={
            "N": TypeVarSpec(name="N", bound="int"),
        })
        assert translate_annotation_str("N", context=ctx).lean == "Int"

    def test_typevar_constrained_uses_union(self) -> None:
        ctx = Context(type_vars={
            "S": TypeVarSpec(name="S", constraints=["int", "str"]),
        })
        r = translate_annotation_str("S", context=ctx)
        assert r.lean == "(Sum Int String)"

    def test_paramspec_translates_to_arrow(self) -> None:
        ctx = Context(type_vars={
            "P": TypeVarSpec(name="P", is_param_spec=True),
        })
        r = translate_annotation_str("P", context=ctx)
        assert r.lean == "(α → β)"

    def test_newtype_unwraps_to_underlying(self) -> None:
        ctx = Context(new_types={"UserId": "int"})
        assert translate_annotation_str(
            "UserId", context=ctx,
        ).lean == "Int"

    def test_typealias_resolves(self) -> None:
        ctx = Context(type_aliases={"JSONValue": "int | str | list[int]"})
        r = translate_annotation_str("JSONValue", context=ctx)
        # Union of the three components.
        assert "Sum" in r.lean
        assert "List Int" in r.lean

    def test_self_uses_enclosing_class(self) -> None:
        ctx = Context(enclosing_class="MyService")
        r = translate_annotation_str("Self", context=ctx)
        assert "Deppy_MyService" in r.lean

    def test_known_class_emits_axiom_once(self) -> None:
        ctx = Context(known_classes={"MyClass"})
        r = translate_annotation_str("list[MyClass]", context=ctx)
        # MyClass appears as a single axiom decl.
        decls = [d for d in r.aux_decls if "Deppy_MyClass" in d]
        assert len(decls) == 1

    def test_module_source_extraction(self) -> None:
        src = """\
from typing import TypeVar, NewType, TypeAlias, ParamSpec

T = TypeVar('T')
N = TypeVar('N', bound=int)
S = TypeVar('S', int, str)
P = ParamSpec('P')
UserId = NewType('UserId', int)
JSONValue: TypeAlias = int | str

class MyClass:
    pass
"""
        ctx = Context.from_module_source(src)
        assert "T" in ctx.type_vars
        assert "N" in ctx.type_vars
        assert ctx.type_vars["N"].bound == "int"
        assert "S" in ctx.type_vars
        assert ctx.type_vars["S"].constraints == ["int", "str"]
        assert "P" in ctx.type_vars
        assert ctx.type_vars["P"].is_param_spec
        assert "UserId" in ctx.new_types
        assert ctx.new_types["UserId"] == "int"
        assert "JSONValue" in ctx.type_aliases
        assert "MyClass" in ctx.known_classes


# ─────────────────────────────────────────────────────────────────────
# Generic / Protocol markers + Type[T]
# ─────────────────────────────────────────────────────────────────────

class TestSpecialMarkers:
    def test_generic_marker(self) -> None:
        # ``Generic[T]`` rendered as ``α`` (polymorphic).
        assert translate_annotation_str("Generic[int]").lean == "α"

    def test_protocol_marker(self) -> None:
        r = translate_annotation_str("Protocol")
        assert "Deppy_" in r.lean

    def test_type_of(self) -> None:
        assert translate_annotation_str(
            "Type[int]"
        ).lean == "(Type_of Int)"


# ─────────────────────────────────────────────────────────────────────
# Forward references and dotted names
# ─────────────────────────────────────────────────────────────────────

class TestForwardAndDotted:
    def test_string_forward_ref(self) -> None:
        # PEP 484 forward ref.
        assert translate_annotation_str(
            "'int'"
        ).lean == "Int"

    def test_dotted_typing_alias(self) -> None:
        # ``typing.List[int]`` should match the ``List`` family.
        assert translate_annotation_str(
            "typing.List[int]"
        ).lean == "(List Int)"

    def test_collections_abc_dotted(self) -> None:
        assert translate_annotation_str(
            "collections.abc.Iterable[int]"
        ).lean == "(List Int)"


# ─────────────────────────────────────────────────────────────────────
# Deeply nested
# ─────────────────────────────────────────────────────────────────────

class TestNested:
    def test_list_of_dict_of_optional(self) -> None:
        r = translate_annotation_str(
            "list[dict[str, int | None]]"
        )
        assert r.lean == "(List (Std.HashMap String (Option Int)))"

    def test_callable_returning_dict_of_callable(self) -> None:
        r = translate_annotation_str(
            "Callable[[int], dict[str, Callable[[bool], int]]]"
        )
        assert r.lean == "(Int → (Std.HashMap String (Bool → Int)))"

    def test_union_of_callables(self) -> None:
        r = translate_annotation_str(
            "Callable[[int], int] | Callable[[str], str]"
        )
        assert r.lean == "(Sum (Int → Int) (String → String))"
