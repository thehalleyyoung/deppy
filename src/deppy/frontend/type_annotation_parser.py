"""Parse Python type annotations to deppy type objects.

This module converts AST annotation nodes (from function signatures,
variable annotations, and class bases) into ``deppy.types.base.TypeBase``
objects.  The parser handles:

- Primitive types: ``int``, ``str``, ``float``, ``bool``, ``None``,
  ``bytes``, ``complex``
- Container types: ``List[X]``, ``Dict[K,V]``, ``Tuple[X,...]``,
  ``Set[X]``, ``FrozenSet[X]``
- Optional and Union: ``Optional[X]``, ``Union[X,Y]``
- Callable: ``Callable[[X], Y]``
- Protocol references
- String annotations (forward references)
- ``torch.Tensor`` -> ``TensorType``
- Class references -> ``ClassType``
- ``typing.TypeVar`` names -> type variables
- ``Literal[...]`` -> ``LiteralType``

In the sheaf view, annotations seed the carrier types at argument-boundary
and return-boundary observation sites.  The annotation parser is therefore
a critical component of the frontend: it determines the initial local sections
at boundary sites before any inference or transport occurs.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
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
    AnyType,
    CallableType,
    ClassType,
    DictType,
    FrozenSetType,
    ListType,
    LiteralType,
    NeverType,
    OptionalType,
    PrimitiveKind,
    PrimitiveType,
    ProtocolType,
    SetType,
    TensorType,
    TupleType,
    TypeBase,
    UnionType,
)
from deppy.static_analysis.observation_sites import SourceSpan


# ═══════════════════════════════════════════════════════════════════════════════
# Forward reference wrapper
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class ForwardRef(TypeBase):
    """A forward reference that has not yet been resolved.

    Forward references arise from string annotations (e.g., ``"MyClass"``)
    and from annotations that reference names not yet defined.  They are
    resolved in a later pass when the full module context is available.
    """
    ref_name: str
    module: str = ""

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        if self.ref_name in mapping:
            return mapping[self.ref_name]
        return self

    def free_variables(self) -> FrozenSet[str]:
        return frozenset({self.ref_name})

    def __repr__(self) -> str:
        return f"ForwardRef({self.ref_name!r})"


# ═══════════════════════════════════════════════════════════════════════════════
# Type variable reference
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class TypeVarRef(TypeBase):
    """A reference to a typing.TypeVar.

    TypeVar references are placeholder types that will be unified during
    type inference.  In the sheaf view, they represent unconstrained
    coordinates in the carrier type at a site.
    """
    name: str
    bound: Optional[TypeBase] = None
    constraints: Tuple[TypeBase, ...] = ()

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        if self.name in mapping:
            return mapping[self.name]
        return self

    def free_variables(self) -> FrozenSet[str]:
        return frozenset({self.name})

    def __repr__(self) -> str:
        if self.bound is not None:
            return f"TypeVar({self.name!r}, bound={self.bound!r})"
        if self.constraints:
            cs = ", ".join(repr(c) for c in self.constraints)
            return f"TypeVar({self.name!r}, {cs})"
        return f"TypeVar({self.name!r})"


# ═══════════════════════════════════════════════════════════════════════════════
# Annotation parser
# ═══════════════════════════════════════════════════════════════════════════════

# Mapping from simple type names to deppy primitive/top/bottom types
_BUILTIN_TYPES: Dict[str, TypeBase] = {
    "int": INT_TYPE,
    "float": FLOAT_TYPE,
    "str": STR_TYPE,
    "bool": BOOL_TYPE,
    "bytes": BYTES_TYPE,
    "complex": COMPLEX_TYPE,
    "None": NONE_TYPE,
    "NoneType": NONE_TYPE,
    "Any": ANY_TYPE,
    "any": ANY_TYPE,
    "Never": NEVER_TYPE,
    "NoReturn": NEVER_TYPE,
    "object": ClassType(name="object"),
    "type": ClassType(name="type"),
    "Ellipsis": ClassType(name="Ellipsis"),
}

# Names that are generic container constructors
_GENERIC_CONTAINERS: Dict[str, str] = {
    "List": "list",
    "list": "list",
    "Dict": "dict",
    "dict": "dict",
    "Tuple": "tuple",
    "tuple": "tuple",
    "Set": "set",
    "set": "set",
    "FrozenSet": "frozenset",
    "frozenset": "frozenset",
    "Sequence": "sequence",
    "Iterable": "iterable",
    "Iterator": "iterator",
    "Mapping": "mapping",
    "MutableMapping": "mutable_mapping",
    "MutableSequence": "mutable_sequence",
    "MutableSet": "mutable_set",
    "Deque": "deque",
    "DefaultDict": "defaultdict",
    "OrderedDict": "ordereddict",
    "Counter": "counter",
    "ChainMap": "chainmap",
}


class AnnotationParser:
    """Converts Python AST annotation nodes to deppy TypeBase objects.

    The parser maintains a namespace mapping for resolving type aliases
    and forward references.  It can be configured with known type variables
    and class definitions from the module context.

    Usage::

        parser = AnnotationParser(filename="my_module.py")
        ty = parser.parse(ast_node)
    """

    def __init__(
        self,
        filename: str = "<unknown>",
        *,
        known_types: Optional[Dict[str, TypeBase]] = None,
        known_typevars: Optional[Dict[str, TypeVarRef]] = None,
        module_name: str = "",
    ) -> None:
        self._filename = filename
        self._module_name = module_name
        self._known_types: Dict[str, TypeBase] = dict(_BUILTIN_TYPES)
        if known_types:
            self._known_types.update(known_types)
        self._known_typevars: Dict[str, TypeVarRef] = known_typevars or {}

    def register_type(self, name: str, ty: TypeBase) -> None:
        """Register a named type for resolution."""
        self._known_types[name] = ty

    def register_typevar(self, name: str, ref: TypeVarRef) -> None:
        """Register a TypeVar for resolution."""
        self._known_typevars[name] = ref

    def parse(self, node: Optional[ast.expr]) -> TypeBase:
        """Parse an AST annotation node into a TypeBase.

        Returns ``ANY_TYPE`` if the node is None (no annotation).
        """
        if node is None:
            return ANY_TYPE
        return self._parse_node(node)

    def parse_string(self, annotation_str: str) -> TypeBase:
        """Parse a string annotation (e.g., from ``__annotations__``).

        The string is first parsed as a Python expression, then the
        resulting AST node is processed normally.
        """
        try:
            tree = ast.parse(annotation_str, mode="eval")
            return self._parse_node(tree.body)
        except SyntaxError:
            return ForwardRef(ref_name=annotation_str, module=self._module_name)

    # ── Internal dispatch ─────────────────────────────────────────────────

    def _parse_node(self, node: ast.expr) -> TypeBase:
        """Dispatch on AST node type to produce a TypeBase."""

        # Simple name: int, str, MyClass, etc.
        if isinstance(node, ast.Name):
            return self._parse_name(node.id)

        # String constant: forward reference
        if isinstance(node, ast.Constant):
            return self._parse_constant(node)

        # Subscript: List[int], Optional[str], Dict[str, int], etc.
        if isinstance(node, ast.Subscript):
            return self._parse_subscript(node)

        # Attribute: typing.List, torch.Tensor, module.Class
        if isinstance(node, ast.Attribute):
            return self._parse_attribute(node)

        # BinOp with |: X | Y (Python 3.10+ union syntax)
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
            left = self._parse_node(node.left)
            right = self._parse_node(node.right)
            return UnionType.build([left, right])

        # Tuple: used in Union[X, Y] subscript parsing
        if isinstance(node, ast.Tuple):
            types = [self._parse_node(e) for e in node.elts]
            return TupleType(tuple(types))

        # List: used in Callable[[X], Y] parameter list
        if isinstance(node, ast.List):
            types = [self._parse_node(e) for e in node.elts]
            return TupleType(tuple(types))

        # None constant
        if isinstance(node, ast.Constant) and node.value is None:
            return NONE_TYPE

        # Starred: *args types
        if isinstance(node, ast.Starred):
            inner = self._parse_node(node.value)
            return inner

        # Fallback: forward reference from the source text
        try:
            text = ast.unparse(node)
            return ForwardRef(ref_name=text, module=self._module_name)
        except Exception:
            return ANY_TYPE

    def _parse_name(self, name: str) -> TypeBase:
        """Resolve a simple name to a type."""
        # Check builtins and known types
        if name in self._known_types:
            return self._known_types[name]

        # Check known type variables
        if name in self._known_typevars:
            return self._known_typevars[name]

        # Check if it's a known generic container without args
        if name in _GENERIC_CONTAINERS:
            container_kind = _GENERIC_CONTAINERS[name]
            if container_kind == "list":
                return ListType(ANY_TYPE)
            if container_kind == "dict":
                return DictType(ANY_TYPE, ANY_TYPE)
            if container_kind == "tuple":
                return TupleType((ANY_TYPE,), variadic=True)
            if container_kind == "set":
                return SetType(ANY_TYPE)
            if container_kind == "frozenset":
                return FrozenSetType(ANY_TYPE)
            return ClassType(name=name)

        # Tensor shorthand
        if name == "Tensor":
            return TensorType()

        # Protocol
        if name == "Protocol":
            return ProtocolType(name="Protocol", members=())

        # Unknown: treat as a class reference or forward ref
        return ClassType(name=name, module=self._module_name)

    def _parse_constant(self, node: ast.Constant) -> TypeBase:
        """Parse a constant node (usually a string forward reference)."""
        if isinstance(node.value, str):
            return self.parse_string(node.value)
        if node.value is None:
            return NONE_TYPE
        if isinstance(node.value, bool):
            return BOOL_TYPE
        if isinstance(node.value, int):
            return INT_TYPE
        if isinstance(node.value, float):
            return FLOAT_TYPE
        if node.value is ...:
            return ANY_TYPE
        return ANY_TYPE

    def _parse_subscript(self, node: ast.Subscript) -> TypeBase:
        """Parse a subscript annotation like List[int] or Union[X, Y]."""
        base_name = self._get_subscript_base(node.value)
        if base_name is None:
            # Complex base: parse as ClassType with type args
            base_type = self._parse_node(node.value)
            args = self._parse_subscript_args(node.slice)
            if isinstance(base_type, ClassType):
                return ClassType(
                    name=base_type.name,
                    module=base_type.module,
                    type_args=tuple(args),
                    bases=base_type.bases,
                )
            return base_type

        return self._parse_generic(base_name, node.slice)

    def _get_subscript_base(self, node: ast.expr) -> Optional[str]:
        """Extract the base name from a subscript's value node."""
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Attribute):
            prefix = self._get_attribute_prefix(node)
            return prefix
        return None

    def _get_attribute_prefix(self, node: ast.Attribute) -> str:
        """Build dotted name from nested attributes."""
        if isinstance(node.value, ast.Name):
            return f"{node.value.id}.{node.attr}"
        if isinstance(node.value, ast.Attribute):
            prefix = self._get_attribute_prefix(node.value)
            return f"{prefix}.{node.attr}"
        return node.attr

    def _parse_generic(self, base_name: str, slice_node: ast.expr) -> TypeBase:
        """Parse a generic type given the base name and slice arguments."""
        args = self._parse_subscript_args(slice_node)

        # Optional[X]
        if base_name in ("Optional", "typing.Optional"):
            if len(args) == 1:
                return OptionalType(args[0])
            return OptionalType(args[0] if args else ANY_TYPE)

        # Union[X, Y, ...]
        if base_name in ("Union", "typing.Union"):
            return UnionType.build(args)

        # List[X]
        if base_name in ("List", "list", "typing.List"):
            return ListType(args[0] if args else ANY_TYPE)

        # Dict[K, V]
        if base_name in ("Dict", "dict", "typing.Dict"):
            key = args[0] if len(args) > 0 else ANY_TYPE
            val = args[1] if len(args) > 1 else ANY_TYPE
            return DictType(key, val)

        # Tuple[X, Y, ...] or Tuple[X, ...]
        if base_name in ("Tuple", "tuple", "typing.Tuple"):
            return self._parse_tuple_args(args, slice_node)

        # Set[X]
        if base_name in ("Set", "set", "typing.Set"):
            return SetType(args[0] if args else ANY_TYPE)

        # FrozenSet[X]
        if base_name in ("FrozenSet", "frozenset", "typing.FrozenSet"):
            return FrozenSetType(args[0] if args else ANY_TYPE)

        # Callable[[X, Y], R]
        if base_name in ("Callable", "typing.Callable",
                          "collections.abc.Callable"):
            return self._parse_callable(slice_node)

        # Literal[v1, v2, ...]
        if base_name in ("Literal", "typing.Literal"):
            return self._parse_literal(slice_node)

        # Type[X]
        if base_name in ("Type", "type", "typing.Type"):
            inner = args[0] if args else ANY_TYPE
            return ClassType(name="Type", type_args=(inner,))

        # ClassVar[X] -> just X
        if base_name in ("ClassVar", "typing.ClassVar"):
            return args[0] if args else ANY_TYPE

        # Final[X] -> just X
        if base_name in ("Final", "typing.Final"):
            return args[0] if args else ANY_TYPE

        # Annotated[X, ...] -> just X
        if base_name in ("Annotated", "typing.Annotated"):
            return args[0] if args else ANY_TYPE

        # torch.Tensor[...] (non-standard but common)
        if base_name in ("torch.Tensor", "Tensor"):
            return TensorType()

        # Sequence, Iterable, etc. -> treat like List
        container_kind = _GENERIC_CONTAINERS.get(
            base_name.split(".")[-1], None
        )
        if container_kind in ("sequence", "iterable", "iterator",
                               "mutable_sequence"):
            return ListType(args[0] if args else ANY_TYPE)
        if container_kind in ("mapping", "mutable_mapping"):
            key = args[0] if len(args) > 0 else ANY_TYPE
            val = args[1] if len(args) > 1 else ANY_TYPE
            return DictType(key, val)

        # Generic class with type args
        clean_name = base_name.split(".")[-1]
        module = ".".join(base_name.split(".")[:-1]) if "." in base_name else ""
        return ClassType(
            name=clean_name,
            module=module,
            type_args=tuple(args),
        )

    def _parse_subscript_args(self, slice_node: ast.expr) -> List[TypeBase]:
        """Parse the arguments of a subscript (the part inside [])."""
        if isinstance(slice_node, ast.Tuple):
            return [self._parse_node(e) for e in slice_node.elts]
        return [self._parse_node(slice_node)]

    def _parse_tuple_args(
        self,
        args: List[TypeBase],
        slice_node: ast.expr,
    ) -> TupleType:
        """Parse Tuple type arguments, handling Tuple[X, ...] syntax."""
        # Check for variadic: Tuple[X, ...]
        if isinstance(slice_node, ast.Tuple) and len(slice_node.elts) == 2:
            second = slice_node.elts[1]
            if isinstance(second, ast.Constant) and second.value is ...:
                return TupleType((args[0],), variadic=True)

        # Empty Tuple[()]
        if not args:
            return TupleType(())

        return TupleType(tuple(args))

    def _parse_callable(self, slice_node: ast.expr) -> TypeBase:
        """Parse Callable[[ParamTypes], ReturnType]."""
        if isinstance(slice_node, ast.Tuple) and len(slice_node.elts) == 2:
            params_node, return_node = slice_node.elts[0], slice_node.elts[1]
            return_type = self._parse_node(return_node)

            # Params can be a list [X, Y, ...] or ... (for any callable)
            if isinstance(params_node, ast.List):
                param_types = tuple(
                    self._parse_node(p) for p in params_node.elts
                )
            elif isinstance(params_node, ast.Constant) and params_node.value is ...:
                # Callable[..., R] - any parameters
                param_types = ()
            else:
                param_types = (self._parse_node(params_node),)

            return CallableType(param_types=param_types, return_type=return_type)

        # Fallback: parse as a generic callable
        return CallableType(param_types=(), return_type=ANY_TYPE)

    def _parse_literal(self, slice_node: ast.expr) -> TypeBase:
        """Parse Literal[v1, v2, ...]."""
        values: List[Union[int, str, bool, bytes, None]] = []

        if isinstance(slice_node, ast.Tuple):
            nodes = slice_node.elts
        else:
            nodes = [slice_node]

        for node in nodes:
            if isinstance(node, ast.Constant):
                val = node.value
                if isinstance(val, (int, str, bool, bytes, type(None))):
                    values.append(val)
            elif isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
                if isinstance(node.operand, ast.Constant) and isinstance(node.operand.value, int):
                    values.append(-node.operand.value)

        if values:
            return LiteralType(tuple(values))
        return ANY_TYPE

    def _parse_attribute(self, node: ast.Attribute) -> TypeBase:
        """Parse an attribute access as a type reference."""
        prefix = self._get_attribute_prefix(node)

        # Check builtins and known types
        if prefix in self._known_types:
            return self._known_types[prefix]

        # torch.Tensor
        if prefix in ("torch.Tensor", "torch.FloatTensor",
                       "torch.LongTensor", "torch.IntTensor",
                       "torch.DoubleTensor", "torch.BoolTensor"):
            dtype = None
            if "Float" in prefix:
                dtype = "float32"
            elif "Long" in prefix:
                dtype = "int64"
            elif "Int" in prefix:
                dtype = "int32"
            elif "Double" in prefix:
                dtype = "float64"
            elif "Bool" in prefix:
                dtype = "bool"
            return TensorType(dtype=dtype)

        # numpy.ndarray
        if prefix in ("numpy.ndarray", "np.ndarray"):
            return TensorType(framework="numpy")

        # typing.* types (resolve through standard names)
        if prefix.startswith("typing."):
            suffix = prefix[7:]  # Remove "typing."
            if suffix in self._known_types:
                return self._known_types[suffix]
            if suffix in _GENERIC_CONTAINERS:
                return self._parse_name(suffix)
            if suffix == "Any":
                return ANY_TYPE
            if suffix == "NoReturn":
                return NEVER_TYPE

        # collections.abc.*
        if prefix.startswith("collections.abc."):
            suffix = prefix[16:]
            if suffix in _GENERIC_CONTAINERS:
                return self._parse_name(suffix)

        # General dotted name -> ClassType
        parts = prefix.rsplit(".", 1)
        if len(parts) == 2:
            return ClassType(name=parts[1], module=parts[0])
        return ClassType(name=prefix, module="")


# ═══════════════════════════════════════════════════════════════════════════════
# Convenience functions
# ═══════════════════════════════════════════════════════════════════════════════


def parse_annotation(
    node: Optional[ast.expr],
    *,
    filename: str = "<unknown>",
    known_types: Optional[Dict[str, TypeBase]] = None,
) -> TypeBase:
    """Parse a single annotation AST node to a TypeBase.

    Convenience wrapper around ``AnnotationParser.parse()``.
    """
    parser = AnnotationParser(filename=filename, known_types=known_types)
    return parser.parse(node)


def parse_annotation_string(
    annotation_str: str,
    *,
    filename: str = "<unknown>",
    known_types: Optional[Dict[str, TypeBase]] = None,
) -> TypeBase:
    """Parse a string annotation to a TypeBase.

    Convenience wrapper for forward references and string-based annotations.
    """
    parser = AnnotationParser(filename=filename, known_types=known_types)
    return parser.parse_string(annotation_str)


def parse_function_annotations(
    func_node: Union[ast.FunctionDef, ast.AsyncFunctionDef],
    *,
    filename: str = "<unknown>",
    known_types: Optional[Dict[str, TypeBase]] = None,
) -> Tuple[List[Tuple[str, TypeBase]], TypeBase]:
    """Parse all annotations from a function definition.

    Returns a tuple of:
    - List of (param_name, param_type) pairs
    - The return type

    This is used by the cover builder to seed carrier types at
    argument-boundary and return-boundary sites.
    """
    parser = AnnotationParser(filename=filename, known_types=known_types)

    param_types: List[Tuple[str, TypeBase]] = []
    for arg in func_node.args.args:
        ty = parser.parse(arg.annotation)
        param_types.append((arg.arg, ty))

    for arg in func_node.args.posonlyargs:
        ty = parser.parse(arg.annotation)
        param_types.append((arg.arg, ty))

    for arg in func_node.args.kwonlyargs:
        ty = parser.parse(arg.annotation)
        param_types.append((arg.arg, ty))

    if func_node.args.vararg:
        ty = parser.parse(func_node.args.vararg.annotation)
        param_types.append((f"*{func_node.args.vararg.arg}", ty))

    if func_node.args.kwarg:
        ty = parser.parse(func_node.args.kwarg.annotation)
        param_types.append((f"**{func_node.args.kwarg.arg}", ty))

    return_type = parser.parse(func_node.returns)

    return param_types, return_type
