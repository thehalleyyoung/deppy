"""Audit fix #10 — per-type ``hasattr`` Z3 encoding.

Tests the :class:`HasattrTable`, the union-handling helpers, and the
end-to-end integration with the Z3 encoder so that
``hasattr(x: int, 'append')`` returns ``BoolVal(False)`` (not the
old blanket ``BoolVal(True)``).
"""
from __future__ import annotations

import pytest

z3 = pytest.importorskip("z3")

from deppy.core.hasattr_encoding import (
    HasattrTable,
    Tristate,
    encode_hasattr,
    encode_hasattr_union,
    parse_union_type,
)


# ─────────────────────────────────────────────────────────────────────
#  HasattrTable
# ─────────────────────────────────────────────────────────────────────


class TestHasattrTable:
    def setup_method(self):
        self.table = HasattrTable.default()

    def test_int_has_abs(self):
        assert self.table.has_attribute("int", "__abs__") is Tristate.YES

    def test_int_does_not_have_append(self):
        assert self.table.has_attribute("int", "append") is Tristate.NO

    def test_list_has_append(self):
        assert self.table.has_attribute("list", "append") is Tristate.YES

    def test_list_does_not_have_keys(self):
        assert self.table.has_attribute("list", "keys") is Tristate.NO

    def test_dict_has_keys(self):
        assert self.table.has_attribute("dict", "keys") is Tristate.YES

    def test_dict_does_not_have_append(self):
        assert self.table.has_attribute("dict", "append") is Tristate.NO

    def test_str_has_upper(self):
        assert self.table.has_attribute("str", "upper") is Tristate.YES

    def test_str_does_not_have_append(self):
        assert self.table.has_attribute("str", "append") is Tristate.NO

    def test_set_has_add(self):
        assert self.table.has_attribute("set", "add") is Tristate.YES

    def test_frozenset_does_not_have_add(self):
        assert self.table.has_attribute("frozenset", "add") is Tristate.NO

    def test_unknown_type_is_unknown(self):
        assert self.table.has_attribute("MyClass", "anything") is Tristate.UNKNOWN

    def test_universal_attrs_present_on_all_types(self):
        for ty in ("int", "str", "list", "dict", "set"):
            assert self.table.has_attribute(ty, "__class__") is Tristate.YES
            assert self.table.has_attribute(ty, "__init__") is Tristate.YES

    def test_aliases_resolve_to_canonical(self):
        # ``List`` / ``Dict`` / ``Mapping`` are typing aliases.
        assert self.table.has_attribute("List", "append") is Tristate.YES
        assert self.table.has_attribute("Dict", "keys") is Tristate.YES
        assert self.table.has_attribute("Mapping", "keys") is Tristate.YES

    def test_optional_alias_is_object(self):
        # ``Optional`` alone has no information (it's a constructor;
        # the actual hasattr depends on the inner type).  Returning
        # OBJECT means only the universal attributes are guaranteed.
        assert self.table.has_attribute("Optional", "anything") is Tristate.NO
        assert self.table.has_attribute("Optional", "__class__") is Tristate.YES


class TestUnionAndIntersection:
    def setup_method(self):
        self.table = HasattrTable.default()

    def test_disjunction_yes_when_any_arm_has(self):
        assert self.table.disjunction(["int", "str"], "upper") is Tristate.YES

    def test_disjunction_no_when_all_arms_lack(self):
        assert self.table.disjunction(["int", "float"], "upper") is Tristate.NO

    def test_disjunction_unknown_when_arm_unknown(self):
        assert self.table.disjunction(["int", "MyClass"], "anything") is Tristate.UNKNOWN

    def test_conjunction_yes_when_all_arms_have(self):
        # Both list and tuple have __len__.
        assert self.table.conjunction(["list", "tuple"], "__len__") is Tristate.YES

    def test_conjunction_no_when_any_arm_lacks(self):
        assert self.table.conjunction(["list", "int"], "append") is Tristate.NO


class TestExtensibility:
    def test_with_class_adds_user_type(self):
        t = HasattrTable.default()
        t2 = t.with_class("MyClass", ["foo", "bar"])
        assert t2.has_attribute("MyClass", "foo") is Tristate.YES
        assert t2.has_attribute("MyClass", "bar") is Tristate.YES
        # Non-listed attribute → NO (object attrs still YES).
        assert t2.has_attribute("MyClass", "baz") is Tristate.NO
        assert t2.has_attribute("MyClass", "__init__") is Tristate.YES

    def test_default_unmodified_after_with_class(self):
        t = HasattrTable.default()
        t.with_class("MyClass", ["foo"])
        # Original table still doesn't know about MyClass.
        assert t.has_attribute("MyClass", "foo") is Tristate.UNKNOWN


# ─────────────────────────────────────────────────────────────────────
#  parse_union_type
# ─────────────────────────────────────────────────────────────────────


class TestParseUnionType:
    def test_bare_name(self):
        assert parse_union_type("int") == ["int"]

    def test_pep_604_union(self):
        assert sorted(parse_union_type("int | str")) == ["int", "str"]

    def test_optional(self):
        result = parse_union_type("Optional[int]")
        assert "int" in result
        assert "None" in result

    def test_typing_union(self):
        result = parse_union_type("Union[int, str, float]")
        assert sorted(result) == ["float", "int", "str"]

    def test_strip_generic(self):
        assert parse_union_type("list[int]") == ["list"]

    def test_complex_union_strips_generic(self):
        result = parse_union_type("list[int] | dict[str, int]")
        assert sorted(result) == ["dict", "list"]

    def test_unparseable_returns_empty(self):
        assert parse_union_type("") == []

    def test_parens(self):
        assert parse_union_type("(int)") == ["int"]


# ─────────────────────────────────────────────────────────────────────
#  Z3 encoding integration
# ─────────────────────────────────────────────────────────────────────


class TestEncodeHasattr:
    def test_int_has_abs_returns_true(self):
        result = encode_hasattr(
            "int", "__abs__", sort_name="x", z3_module=z3,
        )
        # Should simplify to True.
        assert z3.simplify(result).eq(z3.BoolVal(True))

    def test_int_does_not_have_append_returns_false(self):
        result = encode_hasattr(
            "int", "append", sort_name="x", z3_module=z3,
        )
        assert z3.simplify(result).eq(z3.BoolVal(False))

    def test_list_append_returns_true(self):
        result = encode_hasattr(
            "list", "append", sort_name="xs", z3_module=z3,
        )
        assert z3.simplify(result).eq(z3.BoolVal(True))

    def test_unknown_type_returns_uninterpreted(self):
        result = encode_hasattr(
            "MyClass", "foo", sort_name="x", z3_module=z3,
        )
        # Not BoolVal(True) or False.
        assert not z3.simplify(result).eq(z3.BoolVal(True))
        assert not z3.simplify(result).eq(z3.BoolVal(False))

    def test_uninterp_cache_makes_predicates_equal(self):
        cache = {}
        a = encode_hasattr(
            "MyClass", "foo", sort_name="x", z3_module=z3,
            uninterp_cache=cache,
        )
        b = encode_hasattr(
            "MyClass", "foo", sort_name="x", z3_module=z3,
            uninterp_cache=cache,
        )
        # Same atom — Z3 sees them as identical.
        assert a.eq(b)

    def test_uninterp_cache_separates_different_keys(self):
        cache = {}
        a = encode_hasattr(
            "MyClass", "foo", sort_name="x", z3_module=z3,
            uninterp_cache=cache,
        )
        b = encode_hasattr(
            "MyClass", "bar", sort_name="x", z3_module=z3,
            uninterp_cache=cache,
        )
        assert not a.eq(b)


class TestEncodeHasattrUnion:
    def test_union_with_yes_arm_returns_true(self):
        result = encode_hasattr_union(
            ["int", "str"], "upper", sort_name="x", z3_module=z3,
        )
        assert z3.simplify(result).eq(z3.BoolVal(True))

    def test_union_with_all_no_arms_returns_false(self):
        result = encode_hasattr_union(
            ["int", "float"], "upper", sort_name="x", z3_module=z3,
        )
        assert z3.simplify(result).eq(z3.BoolVal(False))

    def test_union_with_unknown_arm_returns_uninterpreted(self):
        result = encode_hasattr_union(
            ["int", "MyClass"], "foo", sort_name="x", z3_module=z3,
        )
        # Uninterpreted — neither True nor False.
        assert not z3.simplify(result).eq(z3.BoolVal(True))
        assert not z3.simplify(result).eq(z3.BoolVal(False))


# ─────────────────────────────────────────────────────────────────────
#  Integration with check_implication — the headline regression
# ─────────────────────────────────────────────────────────────────────


class TestZ3CheckImplicationIntegration:
    """Audit fix #10 invariant: ``hasattr(x: int, 'append')`` must NOT
    be valid in the SMT encoding.  Before the fix it was, because the
    encoder collapsed every hasattr to True.
    """

    def test_int_does_not_have_append(self):
        from deppy.core.z3_encoder import check_implication
        verdict, _ = check_implication(
            premise="True",
            conclusion="hasattr(x, 'append')",
            binders={"x": "int"},
        )
        # ``hasattr(x: int, 'append')`` is FALSE; the implication
        # ``True → False`` should not validate.
        assert verdict is False

    def test_list_does_have_append(self):
        from deppy.core.z3_encoder import check_implication
        verdict, _ = check_implication(
            premise="True",
            conclusion="hasattr(xs, 'append')",
            binders={"xs": "list[int]"},
        )
        assert verdict is True

    def test_dict_does_have_keys(self):
        from deppy.core.z3_encoder import check_implication
        verdict, _ = check_implication(
            premise="True",
            conclusion="hasattr(d, 'keys')",
            binders={"d": "dict[str, int]"},
        )
        assert verdict is True

    def test_dict_does_not_have_append(self):
        from deppy.core.z3_encoder import check_implication
        verdict, _ = check_implication(
            premise="True",
            conclusion="hasattr(d, 'append')",
            binders={"d": "dict"},
        )
        assert verdict is False

    def test_str_has_upper(self):
        from deppy.core.z3_encoder import check_implication
        verdict, _ = check_implication(
            premise="True",
            conclusion="hasattr(s, 'upper')",
            binders={"s": "str"},
        )
        assert verdict is True

    def test_int_does_not_have_upper(self):
        from deppy.core.z3_encoder import check_implication
        verdict, _ = check_implication(
            premise="True",
            conclusion="hasattr(x, 'upper')",
            binders={"x": "int"},
        )
        assert verdict is False
