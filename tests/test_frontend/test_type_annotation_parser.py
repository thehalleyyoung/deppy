"""Tests for deppy.frontend.type_annotation_parser -- annotation parsing.

Exercises parsing of primitive types, Optional, Union, List, Dict, Tuple,
Callable, Literal, forward references, torch.Tensor, and string annotations.
"""

from __future__ import annotations

import ast
import pytest

from deppy.frontend.type_annotation_parser import (
    AnnotationParser,
    ForwardRef,
    TypeVarRef,
    parse_annotation,
    parse_annotation_string,
    parse_function_annotations,
)
from deppy.types.base import (
    ANY_TYPE,
    BOOL_TYPE,
    BYTES_TYPE,
    COMPLEX_TYPE,
    FLOAT_TYPE,
    INT_TYPE,
    NEVER_TYPE,
    NONE_TYPE,
    STR_TYPE,
    CallableType,
    ClassType,
    DictType,
    FrozenSetType,
    ListType,
    LiteralType,
    OptionalType,
    PrimitiveType,
    SetType,
    TensorType,
    TupleType,
    TypeBase,
    UnionType,
)


# ===================================================================
# Helpers
# ===================================================================

def _parse(annotation_str: str) -> TypeBase:
    """Parse a string annotation."""
    return parse_annotation_string(annotation_str)


def _parse_node(source: str) -> TypeBase:
    """Parse an annotation AST node from a variable annotation."""
    tree = ast.parse(f"x: {source}", mode="exec")
    ann_assign = tree.body[0]
    return parse_annotation(ann_assign.annotation)


# ===================================================================
# TestPrimitiveTypes
# ===================================================================

class TestPrimitiveTypes:
    """Test parsing of primitive/builtin type annotations."""

    def test_int(self):
        ty = _parse_node("int")
        assert ty == INT_TYPE

    def test_str(self):
        ty = _parse_node("str")
        assert ty == STR_TYPE

    def test_float(self):
        ty = _parse_node("float")
        assert ty == FLOAT_TYPE

    def test_bool(self):
        ty = _parse_node("bool")
        assert ty == BOOL_TYPE

    def test_bytes(self):
        ty = _parse_node("bytes")
        assert ty == BYTES_TYPE

    def test_complex(self):
        ty = _parse_node("complex")
        assert ty == COMPLEX_TYPE

    def test_none(self):
        ty = _parse_node("None")
        assert ty == NONE_TYPE

    def test_any(self):
        ty = _parse_node("Any")
        assert ty == ANY_TYPE

    def test_no_annotation_returns_any(self):
        parser = AnnotationParser()
        ty = parser.parse(None)
        assert ty == ANY_TYPE

    def test_never(self):
        ty = _parse("Never")
        assert ty == NEVER_TYPE

    def test_noreturn(self):
        ty = _parse("NoReturn")
        assert ty == NEVER_TYPE


# ===================================================================
# TestOptionalAndUnion
# ===================================================================

class TestOptionalAndUnion:
    """Test Optional and Union parsing."""

    def test_optional_int(self):
        ty = _parse_node("Optional[int]")
        assert isinstance(ty, OptionalType)
        assert ty.inner == INT_TYPE

    def test_optional_str(self):
        ty = _parse_node("Optional[str]")
        assert isinstance(ty, OptionalType)
        assert ty.inner == STR_TYPE

    def test_union_two_types(self):
        ty = _parse_node("Union[int, str]")
        assert isinstance(ty, UnionType)

    def test_union_three_types(self):
        ty = _parse_node("Union[int, str, float]")
        assert isinstance(ty, UnionType)

    def test_pipe_union(self):
        ty = _parse_node("int | str")
        assert isinstance(ty, UnionType)

    def test_union_with_none_is_optional(self):
        ty = _parse_node("Union[int, None]")
        # Should be treated as a union including None
        assert isinstance(ty, (UnionType, OptionalType))


# ===================================================================
# TestContainerTypes
# ===================================================================

class TestContainerTypes:
    """Test List, Dict, Tuple, Set, FrozenSet parsing."""

    def test_list_int(self):
        ty = _parse_node("List[int]")
        assert isinstance(ty, ListType)
        assert ty.element == INT_TYPE

    def test_list_bare(self):
        ty = _parse_node("list")
        assert isinstance(ty, ListType)

    def test_dict_str_int(self):
        ty = _parse_node("Dict[str, int]")
        assert isinstance(ty, DictType)
        assert ty.key == STR_TYPE
        assert ty.value == INT_TYPE

    def test_dict_bare(self):
        ty = _parse_node("dict")
        assert isinstance(ty, DictType)

    def test_tuple_two_elts(self):
        ty = _parse_node("Tuple[int, str]")
        assert isinstance(ty, TupleType)
        assert len(ty.elements) == 2
        assert ty.elements[0] == INT_TYPE
        assert ty.elements[1] == STR_TYPE

    def test_tuple_variadic(self):
        ty = _parse_node("Tuple[int, ...]")
        assert isinstance(ty, TupleType)
        assert ty.variadic is True

    def test_set_int(self):
        ty = _parse_node("Set[int]")
        assert isinstance(ty, SetType)
        assert ty.element == INT_TYPE

    def test_frozenset_str(self):
        ty = _parse_node("FrozenSet[str]")
        assert isinstance(ty, FrozenSetType)

    def test_nested_container(self):
        ty = _parse_node("List[Dict[str, int]]")
        assert isinstance(ty, ListType)
        assert isinstance(ty.element, DictType)

    def test_lowercase_list(self):
        ty = _parse_node("list[int]")
        assert isinstance(ty, ListType)

    def test_lowercase_dict(self):
        ty = _parse_node("dict[str, int]")
        assert isinstance(ty, DictType)


# ===================================================================
# TestCallableType
# ===================================================================

class TestCallableType:
    """Test Callable annotation parsing."""

    def test_callable_basic(self):
        ty = _parse_node("Callable[[int, str], bool]")
        assert isinstance(ty, CallableType)
        assert len(ty.param_types) == 2
        assert ty.param_types[0] == INT_TYPE
        assert ty.param_types[1] == STR_TYPE
        assert ty.return_type == BOOL_TYPE

    def test_callable_no_params(self):
        ty = _parse_node("Callable[[], int]")
        assert isinstance(ty, CallableType)
        assert len(ty.param_types) == 0
        assert ty.return_type == INT_TYPE

    def test_callable_ellipsis_params(self):
        ty = _parse_node("Callable[..., int]")
        assert isinstance(ty, CallableType)
        assert ty.return_type == INT_TYPE


# ===================================================================
# TestSpecialTypes
# ===================================================================

class TestSpecialTypes:
    """Test special type constructs: Literal, ClassVar, Final, etc."""

    def test_literal_int(self):
        ty = _parse_node("Literal[1, 2, 3]")
        assert isinstance(ty, LiteralType)
        assert 1 in ty.values
        assert 2 in ty.values

    def test_literal_string(self):
        ty = _parse_node("Literal['a', 'b']")
        assert isinstance(ty, LiteralType)
        assert "a" in ty.values

    def test_classvar_strips(self):
        ty = _parse_node("ClassVar[int]")
        assert ty == INT_TYPE

    def test_final_strips(self):
        ty = _parse_node("Final[str]")
        assert ty == STR_TYPE

    def test_annotated_strips(self):
        ty = _parse_node("Annotated[int, 'metadata']")
        assert ty == INT_TYPE


# ===================================================================
# TestTorchTypes
# ===================================================================

class TestTorchTypes:
    """Test torch.Tensor type parsing."""

    def test_tensor_name(self):
        ty = _parse_node("Tensor")
        assert isinstance(ty, TensorType)

    def test_torch_tensor(self):
        parser = AnnotationParser()
        tree = ast.parse("x: torch.Tensor", mode="exec")
        ann = tree.body[0].annotation
        ty = parser.parse(ann)
        assert isinstance(ty, TensorType)

    def test_torch_float_tensor(self):
        parser = AnnotationParser()
        tree = ast.parse("x: torch.FloatTensor", mode="exec")
        ann = tree.body[0].annotation
        ty = parser.parse(ann)
        assert isinstance(ty, TensorType)
        assert ty.dtype == "float32"

    def test_torch_long_tensor(self):
        parser = AnnotationParser()
        tree = ast.parse("x: torch.LongTensor", mode="exec")
        ann = tree.body[0].annotation
        ty = parser.parse(ann)
        assert isinstance(ty, TensorType)
        assert ty.dtype == "int64"


# ===================================================================
# TestForwardReferences
# ===================================================================

class TestForwardReferences:
    """Test forward reference parsing."""

    def test_string_annotation(self):
        ty = _parse_node("'MyClass'")
        # String annotations may be resolved as ClassType or ForwardRef
        assert isinstance(ty, (ClassType, ForwardRef))

    def test_unknown_name_as_classtype(self):
        ty = _parse_node("UnknownClass")
        assert isinstance(ty, ClassType)
        assert ty.name == "UnknownClass"

    def test_parse_string_method(self):
        parser = AnnotationParser()
        ty = parser.parse_string("int")
        assert ty == INT_TYPE

    def test_parse_string_forward_ref(self):
        parser = AnnotationParser()
        ty = parser.parse_string("MyFutureClass")
        assert isinstance(ty, (ClassType, ForwardRef))

    def test_parse_string_invalid_syntax(self):
        parser = AnnotationParser()
        ty = parser.parse_string("not valid python 123[")
        assert isinstance(ty, ForwardRef)


# ===================================================================
# TestTypeVarRef
# ===================================================================

class TestTypeVarRef:
    """Test TypeVar reference handling."""

    def test_register_typevar(self):
        parser = AnnotationParser()
        tv = TypeVarRef(name="T")
        parser.register_typevar("T", tv)
        tree = ast.parse("x: T", mode="exec")
        ty = parser.parse(tree.body[0].annotation)
        assert isinstance(ty, TypeVarRef)
        assert ty.name == "T"

    def test_typevar_with_bound(self):
        tv = TypeVarRef(name="T", bound=INT_TYPE)
        assert tv.bound == INT_TYPE
        assert "bound" in repr(tv)

    def test_typevar_with_constraints(self):
        tv = TypeVarRef(name="T", constraints=(INT_TYPE, STR_TYPE))
        assert len(tv.constraints) == 2

    def test_typevar_substitute(self):
        tv = TypeVarRef(name="T")
        result = tv.substitute({"T": INT_TYPE})
        assert result == INT_TYPE

    def test_typevar_free_variables(self):
        tv = TypeVarRef(name="T")
        assert "T" in tv.free_variables()


# ===================================================================
# TestRegistration
# ===================================================================

class TestRegistration:
    """Test type registration in the parser."""

    def test_register_custom_type(self):
        parser = AnnotationParser()
        my_type = ClassType(name="Widget")
        parser.register_type("Widget", my_type)
        tree = ast.parse("x: Widget", mode="exec")
        ty = parser.parse(tree.body[0].annotation)
        assert ty == my_type

    def test_known_types_override(self):
        custom = ClassType(name="CustomInt")
        parser = AnnotationParser(known_types={"int": custom})
        tree = ast.parse("x: int", mode="exec")
        ty = parser.parse(tree.body[0].annotation)
        assert ty == custom


# ===================================================================
# TestFunctionAnnotations
# ===================================================================

class TestFunctionAnnotations:
    """Test parse_function_annotations convenience function."""

    def test_basic_function(self):
        tree = ast.parse("def f(x: int, y: str) -> bool: pass")
        func_node = tree.body[0]
        params, ret = parse_function_annotations(func_node)
        assert len(params) == 2
        assert params[0] == ("x", INT_TYPE)
        assert params[1] == ("y", STR_TYPE)
        assert ret == BOOL_TYPE

    def test_no_annotations(self):
        tree = ast.parse("def f(x, y): pass")
        func_node = tree.body[0]
        params, ret = parse_function_annotations(func_node)
        # params should have ANY_TYPE
        assert all(ty == ANY_TYPE for _, ty in params)
        assert ret == ANY_TYPE

    def test_partial_annotations(self):
        tree = ast.parse("def f(x: int, y) -> str: pass")
        func_node = tree.body[0]
        params, ret = parse_function_annotations(func_node)
        assert params[0][1] == INT_TYPE
        assert params[1][1] == ANY_TYPE
        assert ret == STR_TYPE


# ===================================================================
# TestDottedAttributes
# ===================================================================

class TestDottedAttributes:
    """Test parsing of dotted attribute type references."""

    def test_typing_list(self):
        parser = AnnotationParser()
        tree = ast.parse("x: typing.List[int]", mode="exec")
        ty = parser.parse(tree.body[0].annotation)
        assert isinstance(ty, ListType)

    def test_typing_optional(self):
        parser = AnnotationParser()
        tree = ast.parse("x: typing.Optional[int]", mode="exec")
        ty = parser.parse(tree.body[0].annotation)
        assert isinstance(ty, OptionalType)

    def test_numpy_ndarray(self):
        parser = AnnotationParser()
        tree = ast.parse("x: np.ndarray", mode="exec")
        ty = parser.parse(tree.body[0].annotation)
        assert isinstance(ty, TensorType)
        assert ty.framework == "numpy"

    def test_module_class_ref(self):
        parser = AnnotationParser()
        tree = ast.parse("x: mymodule.MyClass", mode="exec")
        ty = parser.parse(tree.body[0].annotation)
        assert isinstance(ty, ClassType)
        assert ty.name == "MyClass"
        assert ty.module == "mymodule"
