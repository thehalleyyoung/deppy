"""Tensor harvester -- extract shape/rank/dtype/device hints from torch calls.

Walks a Python AST and discovers tensor-related facts: shape annotations,
rank constraints, dtype and device specifications, reshape/view operations,
and tensor construction patterns.  Each fact is recorded as a frozen
``TensorFact`` dataclass.
"""

from __future__ import annotations

import ast
import enum
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from deppy.core._protocols import TrustLevel
from deppy.predicates.base import (
    Call,
    IntLit,
    Predicate,
    SourceLocation,
    StrLit,
    Term,
    TupleLit,
    Var,
)
from deppy.predicates.tensor import (
    DevicePred,
    DtypePred,
    RankPred,
    ShapePred,
)
from deppy.static_analysis.observation_sites import SourceSpan


# ===================================================================
#  Tensor fact kinds
# ===================================================================

class TensorFactKind(enum.Enum):
    """Kind of tensor fact."""
    SHAPE = "shape"
    RANK = "rank"
    DTYPE = "dtype"
    DEVICE = "device"
    RESHAPE = "reshape"
    VIEW = "view"
    TRANSPOSE = "transpose"
    PERMUTE = "permute"
    SQUEEZE = "squeeze"
    UNSQUEEZE = "unsqueeze"
    FLATTEN = "flatten"
    CONTIGUOUS = "contiguous"
    CONSTRUCTION = "construction"
    BROADCAST = "broadcast"
    MATMUL = "matmul"
    REDUCTION = "reduction"
    CONCATENATION = "concatenation"
    INDEXING = "indexing"
    CLONE = "clone"
    DETACH = "detach"
    TO_DEVICE = "to_device"
    TYPE_CAST = "type_cast"


class TensorFactOrigin(enum.Enum):
    """Where the tensor fact was discovered."""
    ATTRIBUTE_ACCESS = "attribute_access"
    METHOD_CALL = "method_call"
    FUNCTION_CALL = "function_call"
    ASSIGNMENT = "assignment"
    COMPARISON = "comparison"
    ASSERTION = "assertion"
    ANNOTATION = "annotation"
    CONSTRUCTOR = "constructor"


# ===================================================================
#  TensorFact dataclass
# ===================================================================

@dataclass(frozen=True)
class TensorFact:
    """A tensor-related fact extracted from the AST.

    Attributes:
        variable: The tensor variable name.
        fact_kind: What kind of tensor fact this is.
        value: Associated value (shape tuple, dtype string, device string, etc.).
        predicate: The corresponding deppy tensor predicate, if any.
        source_span: Source location.
        trust_level: Provenance trust.
        fact_origin: Where the fact was discovered.
        enclosing_function: Name of the enclosing function.
        shape_dims: For shape facts, the dimension terms.
        rank_value: For rank facts, the rank.
        dtype_value: For dtype facts, the dtype string.
        device_value: For device facts, the device string.
        target_shape: For reshape/view, the target shape.
        source_variable: For operations, the source tensor variable.
        operation_name: The specific operation (e.g., "reshape", "view").
        framework: The tensor framework ("torch", "numpy", "jax").
    """
    variable: str
    fact_kind: TensorFactKind
    value: Optional[Any] = None
    predicate: Optional[Predicate] = None
    source_span: Optional[SourceSpan] = None
    trust_level: TrustLevel = TrustLevel.TRUSTED_AUTO
    fact_origin: TensorFactOrigin = TensorFactOrigin.METHOD_CALL
    enclosing_function: Optional[str] = None
    shape_dims: Optional[Tuple[Term, ...]] = None
    rank_value: Optional[int] = None
    dtype_value: Optional[str] = None
    device_value: Optional[str] = None
    target_shape: Optional[Tuple[Term, ...]] = None
    source_variable: Optional[str] = None
    operation_name: Optional[str] = None
    framework: str = "torch"


# ===================================================================
#  Helpers
# ===================================================================

_TORCH_CONSTRUCTOR_FUNCS: FrozenSet[str] = frozenset({
    "torch.zeros", "torch.ones", "torch.empty", "torch.rand",
    "torch.randn", "torch.full", "torch.arange", "torch.linspace",
    "torch.logspace", "torch.eye", "torch.tensor", "torch.as_tensor",
    "torch.from_numpy", "torch.zeros_like", "torch.ones_like",
    "torch.empty_like", "torch.rand_like", "torch.randn_like",
    "torch.full_like",
    # Also handle short forms
    "zeros", "ones", "empty", "rand", "randn", "full", "arange",
    "linspace", "logspace", "eye", "tensor", "as_tensor",
})

_NUMPY_CONSTRUCTOR_FUNCS: FrozenSet[str] = frozenset({
    "np.zeros", "np.ones", "np.empty", "np.array", "np.asarray",
    "np.arange", "np.linspace", "np.logspace", "np.eye",
    "np.zeros_like", "np.ones_like", "np.empty_like",
    "numpy.zeros", "numpy.ones", "numpy.empty", "numpy.array",
})

_SHAPE_OPS: FrozenSet[str] = frozenset({
    "reshape", "view", "resize_", "expand", "repeat",
    "contiguous", "narrow", "unfold",
})

_REDUCTION_OPS: FrozenSet[str] = frozenset({
    "sum", "mean", "max", "min", "prod", "std", "var",
    "norm", "argmax", "argmin", "any", "all",
})

_DTYPE_NAMES: FrozenSet[str] = frozenset({
    "float32", "float64", "float16", "bfloat16",
    "int32", "int64", "int16", "int8", "uint8",
    "bool", "complex64", "complex128",
    "torch.float32", "torch.float64", "torch.float16", "torch.bfloat16",
    "torch.int32", "torch.int64", "torch.int16", "torch.int8", "torch.uint8",
    "torch.bool", "torch.complex64", "torch.complex128",
})


def _ast_to_term(node: ast.expr) -> Optional[Term]:
    """Convert AST expression to Term."""
    if isinstance(node, ast.Name):
        return Var(node.id)
    if isinstance(node, ast.Constant):
        if isinstance(node.value, int) and not isinstance(node.value, bool):
            return IntLit(node.value)
        if isinstance(node.value, str):
            return StrLit(node.value)
        return None
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        inner = _ast_to_term(node.operand)
        if isinstance(inner, IntLit):
            return IntLit(-inner.value)
        return None
    if isinstance(node, ast.Attribute):
        from deppy.predicates.base import Attr
        obj = _ast_to_term(node.value)
        if obj is not None:
            return Attr(obj=obj, attr=node.attr)
        return None
    return None


def _extract_var_name(node: ast.expr) -> Optional[str]:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        base = _extract_var_name(node.value)
        if base is not None:
            return f"{base}.{node.attr}"
    return None


def _extract_shape_args(args: List[ast.expr]) -> Optional[Tuple[Term, ...]]:
    """Extract shape dimensions from function arguments.

    Handles both ``reshape(3, 4)`` and ``reshape((3, 4))`` styles.
    """
    if not args:
        return None

    # Single tuple argument
    if len(args) == 1 and isinstance(args[0], ast.Tuple):
        dims: List[Term] = []
        for elt in args[0].elts:
            t = _ast_to_term(elt)
            if t is None:
                return None
            dims.append(t)
        return tuple(dims)

    # Multiple positional arguments
    dims = []
    for arg in args:
        t = _ast_to_term(arg)
        if t is None:
            return None
        dims.append(t)
    return tuple(dims)


def _extract_dtype_name(node: ast.expr) -> Optional[str]:
    """Extract a dtype name from an AST expression."""
    if isinstance(node, ast.Attribute):
        full = _extract_var_name(node)
        if full is not None and any(full.endswith(d) for d in (
            "float32", "float64", "float16", "bfloat16",
            "int32", "int64", "int16", "int8", "uint8",
            "bool", "complex64", "complex128",
        )):
            return full
    if isinstance(node, ast.Name) and node.id in _DTYPE_NAMES:
        return node.id
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    return None


def _extract_device_name(node: ast.expr) -> Optional[str]:
    """Extract a device name from an AST expression."""
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "device":
        if node.args and isinstance(node.args[0], ast.Constant):
            return str(node.args[0].value)
    return None


def _get_full_call_name(node: ast.Call) -> Optional[str]:
    """Get the full dotted name of a function call."""
    if isinstance(node.func, ast.Name):
        return node.func.id
    if isinstance(node.func, ast.Attribute):
        base = _extract_var_name(node.func.value)
        if base is not None:
            return f"{base}.{node.func.attr}"
        return node.func.attr
    return None


def _source_loc(node: ast.AST, file: str) -> SourceLocation:
    return SourceLocation(
        file=file,
        line=getattr(node, "lineno", 0),
        col=getattr(node, "col_offset", 0),
        end_line=getattr(node, "end_lineno", None),
        end_col=getattr(node, "end_col_offset", None),
    )


def _detect_framework(name: str) -> str:
    """Detect the tensor framework from a function/module name."""
    if name.startswith("torch") or name.startswith("nn.") or name.startswith("F."):
        return "torch"
    if name.startswith("np.") or name.startswith("numpy"):
        return "numpy"
    if name.startswith("jax") or name.startswith("jnp"):
        return "jax"
    return "torch"


def _extract_keyword_value(
    call: ast.Call,
    keyword_name: str,
) -> Optional[ast.expr]:
    """Extract the value of a keyword argument from a call."""
    for kw in call.keywords:
        if kw.arg == keyword_name:
            return kw.value
    return None


# ===================================================================
#  TensorHarvester visitor
# ===================================================================

class TensorHarvester(ast.NodeVisitor):
    """AST visitor that extracts tensor facts from Python source.

    Handles:
    - ``x.shape`` / ``x.size()`` attribute access
    - ``x.dtype``, ``x.device`` attribute access
    - ``torch.zeros(3, 4)``, ``torch.ones(3, 4)`` constructors
    - ``x.view(3, 4)``, ``x.reshape(3, 4)`` shape operations
    - ``x.to(device)``, ``x.float()``, ``x.half()`` type/device casts
    - ``x.transpose()``, ``x.permute()``, ``x.squeeze()``, ``x.unsqueeze()``
    - Reductions: ``x.sum()``, ``x.mean()``, etc.
    - ``torch.cat()``, ``torch.stack()`` concatenation
    - ``torch.matmul()``, ``@`` operator

    Usage::

        harvester = TensorHarvester(file="example.py")
        harvester.visit(tree)
        facts = harvester.facts
    """

    def __init__(self, file: str = "<unknown>") -> None:
        self._file = file
        self._facts: List[TensorFact] = []
        self._function_stack: List[str] = []

    @property
    def facts(self) -> List[TensorFact]:
        return list(self._facts)

    @property
    def _current_function(self) -> Optional[str]:
        return self._function_stack[-1] if self._function_stack else None

    def _span(self, node: ast.AST) -> SourceSpan:
        return SourceSpan.from_ast(node, self._file)

    def _add_fact(
        self,
        variable: str,
        kind: TensorFactKind,
        node: ast.AST,
        *,
        value: Optional[Any] = None,
        predicate: Optional[Predicate] = None,
        origin: TensorFactOrigin = TensorFactOrigin.METHOD_CALL,
        shape_dims: Optional[Tuple[Term, ...]] = None,
        rank_value: Optional[int] = None,
        dtype_value: Optional[str] = None,
        device_value: Optional[str] = None,
        target_shape: Optional[Tuple[Term, ...]] = None,
        source_variable: Optional[str] = None,
        operation_name: Optional[str] = None,
        framework: str = "torch",
    ) -> None:
        self._facts.append(TensorFact(
            variable=variable,
            fact_kind=kind,
            value=value,
            predicate=predicate,
            source_span=self._span(node),
            trust_level=TrustLevel.TRUSTED_AUTO,
            fact_origin=origin,
            enclosing_function=self._current_function,
            shape_dims=shape_dims,
            rank_value=rank_value,
            dtype_value=dtype_value,
            device_value=device_value,
            target_shape=target_shape,
            source_variable=source_variable,
            operation_name=operation_name,
            framework=framework,
        ))

    # -- Scope --

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self._function_stack.append(node.name)
        self.generic_visit(node)
        self._function_stack.pop()

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self._function_stack.append(node.name)
        self.generic_visit(node)
        self._function_stack.pop()

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self._function_stack.append(node.name)
        self.generic_visit(node)
        self._function_stack.pop()

    # -- Assignments --

    def visit_Assign(self, node: ast.Assign) -> None:
        for target in node.targets:
            var_name = _extract_var_name(target)
            if var_name is None:
                continue
            self._extract_from_value(var_name, node.value, node)
        self.generic_visit(node)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        if node.target is not None and node.value is not None:
            var_name = _extract_var_name(node.target)
            if var_name is not None:
                self._extract_from_value(var_name, node.value, node)
        self.generic_visit(node)

    # -- Attribute access (x.shape, x.dtype, x.device) --

    def visit_Attribute(self, node: ast.Attribute) -> None:
        obj_var = _extract_var_name(node.value)
        if obj_var is not None:
            src = _source_loc(node, self._file)
            if node.attr == "shape":
                self._add_fact(
                    obj_var, TensorFactKind.SHAPE, node,
                    origin=TensorFactOrigin.ATTRIBUTE_ACCESS,
                    predicate=ShapePred(tensor=Var(obj_var), source_location=src),
                )
            elif node.attr == "dtype":
                self._add_fact(
                    obj_var, TensorFactKind.DTYPE, node,
                    origin=TensorFactOrigin.ATTRIBUTE_ACCESS,
                )
            elif node.attr == "device":
                self._add_fact(
                    obj_var, TensorFactKind.DEVICE, node,
                    origin=TensorFactOrigin.ATTRIBUTE_ACCESS,
                )
            elif node.attr == "ndim" or node.attr == "dim":
                self._add_fact(
                    obj_var, TensorFactKind.RANK, node,
                    origin=TensorFactOrigin.ATTRIBUTE_ACCESS,
                )
            elif node.attr == "T":
                self._add_fact(
                    obj_var, TensorFactKind.TRANSPOSE, node,
                    origin=TensorFactOrigin.ATTRIBUTE_ACCESS,
                    operation_name="T",
                )
        self.generic_visit(node)

    # -- Method / function calls --

    def visit_Call(self, node: ast.Call) -> None:
        self._extract_from_call(node)
        self.generic_visit(node)

    def _extract_from_call(self, call: ast.Call) -> None:
        """Extract tensor facts from a function/method call."""
        # Method calls: x.reshape(...), x.view(...), etc.
        if isinstance(call.func, ast.Attribute):
            method = call.func.attr
            obj_var = _extract_var_name(call.func.value)
            if obj_var is not None:
                self._extract_method_call(obj_var, method, call)

        # Function calls: torch.zeros(...), torch.cat(...), etc.
        full_name = _get_full_call_name(call)
        if full_name is not None:
            self._extract_function_call(full_name, call)

    def _extract_method_call(
        self,
        obj_var: str,
        method: str,
        call: ast.Call,
    ) -> None:
        """Extract facts from tensor method calls."""
        src = _source_loc(call, self._file)

        # Shape operations
        if method in ("reshape", "view"):
            shape = _extract_shape_args(call.args)
            if shape is not None:
                self._add_fact(
                    obj_var, TensorFactKind.RESHAPE if method == "reshape" else TensorFactKind.VIEW,
                    call,
                    target_shape=shape,
                    rank_value=len(shape),
                    operation_name=method,
                    source_variable=obj_var,
                    predicate=ShapePred(tensor=Var(obj_var), shape=list(shape), source_location=src),
                )

        elif method == "size":
            # x.size() -> shape, x.size(dim) -> specific dim
            if call.args:
                self._add_fact(
                    obj_var, TensorFactKind.SHAPE, call,
                    origin=TensorFactOrigin.METHOD_CALL,
                    operation_name="size",
                )
            else:
                self._add_fact(
                    obj_var, TensorFactKind.SHAPE, call,
                    origin=TensorFactOrigin.METHOD_CALL,
                    operation_name="size",
                )

        elif method == "dim":
            self._add_fact(
                obj_var, TensorFactKind.RANK, call,
                origin=TensorFactOrigin.METHOD_CALL,
                operation_name="dim",
            )

        elif method == "transpose":
            self._add_fact(
                obj_var, TensorFactKind.TRANSPOSE, call,
                operation_name="transpose",
                source_variable=obj_var,
            )

        elif method == "permute":
            shape = _extract_shape_args(call.args)
            self._add_fact(
                obj_var, TensorFactKind.PERMUTE, call,
                target_shape=shape,
                operation_name="permute",
                source_variable=obj_var,
            )

        elif method == "squeeze":
            self._add_fact(
                obj_var, TensorFactKind.SQUEEZE, call,
                operation_name="squeeze",
                source_variable=obj_var,
            )

        elif method == "unsqueeze":
            self._add_fact(
                obj_var, TensorFactKind.UNSQUEEZE, call,
                operation_name="unsqueeze",
                source_variable=obj_var,
            )

        elif method in ("flatten", "ravel"):
            self._add_fact(
                obj_var, TensorFactKind.FLATTEN, call,
                rank_value=1,
                operation_name=method,
                source_variable=obj_var,
            )

        elif method == "contiguous":
            self._add_fact(
                obj_var, TensorFactKind.CONTIGUOUS, call,
                operation_name="contiguous",
                source_variable=obj_var,
            )

        elif method in _REDUCTION_OPS:
            self._add_fact(
                obj_var, TensorFactKind.REDUCTION, call,
                operation_name=method,
                source_variable=obj_var,
            )

        elif method == "to":
            # x.to(device) or x.to(dtype) or x.to(device, dtype)
            for arg in call.args:
                device = _extract_device_name(arg)
                if device is not None:
                    self._add_fact(
                        obj_var, TensorFactKind.TO_DEVICE, call,
                        device_value=device,
                        operation_name="to",
                        source_variable=obj_var,
                        predicate=DevicePred(tensor=Var(obj_var), device=device, source_location=src),
                    )
                dtype = _extract_dtype_name(arg)
                if dtype is not None:
                    self._add_fact(
                        obj_var, TensorFactKind.TYPE_CAST, call,
                        dtype_value=dtype,
                        operation_name="to",
                        source_variable=obj_var,
                        predicate=DtypePred(tensor=Var(obj_var), dtype=dtype, source_location=src),
                    )
            # Check keyword args
            device_kw = _extract_keyword_value(call, "device")
            if device_kw is not None:
                device = _extract_device_name(device_kw)
                if device is not None:
                    self._add_fact(
                        obj_var, TensorFactKind.TO_DEVICE, call,
                        device_value=device,
                        operation_name="to",
                        source_variable=obj_var,
                    )
            dtype_kw = _extract_keyword_value(call, "dtype")
            if dtype_kw is not None:
                dtype = _extract_dtype_name(dtype_kw)
                if dtype is not None:
                    self._add_fact(
                        obj_var, TensorFactKind.TYPE_CAST, call,
                        dtype_value=dtype,
                        operation_name="to",
                        source_variable=obj_var,
                    )

        elif method in ("float", "double", "half", "bfloat16", "int", "long", "short", "byte", "bool"):
            dtype_map = {
                "float": "float32", "double": "float64", "half": "float16",
                "bfloat16": "bfloat16", "int": "int32", "long": "int64",
                "short": "int16", "byte": "uint8", "bool": "bool",
            }
            dtype = dtype_map.get(method)
            if dtype is not None:
                self._add_fact(
                    obj_var, TensorFactKind.TYPE_CAST, call,
                    dtype_value=dtype,
                    operation_name=method,
                    source_variable=obj_var,
                    predicate=DtypePred(tensor=Var(obj_var), dtype=dtype, source_location=src),
                )

        elif method == "clone":
            self._add_fact(
                obj_var, TensorFactKind.CLONE, call,
                operation_name="clone",
                source_variable=obj_var,
            )

        elif method == "detach":
            self._add_fact(
                obj_var, TensorFactKind.DETACH, call,
                operation_name="detach",
                source_variable=obj_var,
            )

        elif method == "cuda":
            self._add_fact(
                obj_var, TensorFactKind.TO_DEVICE, call,
                device_value="cuda",
                operation_name="cuda",
                source_variable=obj_var,
            )

        elif method == "cpu":
            self._add_fact(
                obj_var, TensorFactKind.TO_DEVICE, call,
                device_value="cpu",
                operation_name="cpu",
                source_variable=obj_var,
            )

        elif method == "expand":
            shape = _extract_shape_args(call.args)
            if shape is not None:
                self._add_fact(
                    obj_var, TensorFactKind.RESHAPE, call,
                    target_shape=shape,
                    operation_name="expand",
                    source_variable=obj_var,
                )

        elif method == "repeat":
            shape = _extract_shape_args(call.args)
            if shape is not None:
                self._add_fact(
                    obj_var, TensorFactKind.RESHAPE, call,
                    target_shape=shape,
                    operation_name="repeat",
                    source_variable=obj_var,
                )

    def _extract_function_call(
        self,
        full_name: str,
        call: ast.Call,
    ) -> None:
        """Extract facts from tensor function calls."""
        src = _source_loc(call, self._file)
        framework = _detect_framework(full_name)

        # Constructor functions
        if full_name in _TORCH_CONSTRUCTOR_FUNCS or full_name in _NUMPY_CONSTRUCTOR_FUNCS:
            self._extract_constructor(full_name, call, framework)
            return

        # torch.cat / torch.stack
        basename = full_name.split(".")[-1] if "." in full_name else full_name
        if basename in ("cat", "concatenate", "stack", "hstack", "vstack", "dstack"):
            self._add_fact(
                "_result", TensorFactKind.CONCATENATION, call,
                origin=TensorFactOrigin.FUNCTION_CALL,
                operation_name=basename,
                framework=framework,
            )

        # torch.matmul / torch.mm / torch.bmm
        if basename in ("matmul", "mm", "bmm", "dot", "mv"):
            self._add_fact(
                "_result", TensorFactKind.MATMUL, call,
                origin=TensorFactOrigin.FUNCTION_CALL,
                operation_name=basename,
                framework=framework,
            )

        # torch.reshape
        if basename == "reshape" and len(call.args) >= 2:
            src_var = _extract_var_name(call.args[0])
            shape = _extract_shape_args(call.args[1:])
            if src_var is not None and shape is not None:
                self._add_fact(
                    src_var, TensorFactKind.RESHAPE, call,
                    origin=TensorFactOrigin.FUNCTION_CALL,
                    target_shape=shape,
                    source_variable=src_var,
                    operation_name="reshape",
                    framework=framework,
                )

    def _extract_constructor(
        self,
        full_name: str,
        call: ast.Call,
        framework: str,
    ) -> None:
        """Extract facts from tensor constructor calls."""
        src = _source_loc(call, self._file)
        basename = full_name.split(".")[-1] if "." in full_name else full_name

        shape: Optional[Tuple[Term, ...]] = None
        dtype_val: Optional[str] = None
        device_val: Optional[str] = None

        # Shape from positional args
        if basename in ("zeros", "ones", "empty", "rand", "randn", "full"):
            if basename == "full":
                # torch.full(size, fill_value)
                if call.args:
                    shape = _extract_shape_args([call.args[0]])
            else:
                shape = _extract_shape_args(call.args)

        elif basename in ("eye",):
            # torch.eye(n) or torch.eye(n, m)
            if call.args:
                terms = [_ast_to_term(a) for a in call.args[:2]]
                valid = [t for t in terms if t is not None]
                if valid:
                    if len(valid) == 1:
                        shape = (valid[0], valid[0])
                    else:
                        shape = tuple(valid[:2])

        elif basename in ("arange", "linspace", "logspace"):
            # 1D output
            shape = None  # dynamic length; record rank=1
            self._add_fact(
                "_result", TensorFactKind.CONSTRUCTION, call,
                origin=TensorFactOrigin.CONSTRUCTOR,
                rank_value=1,
                operation_name=basename,
                framework=framework,
            )

        elif basename == "tensor" or basename == "as_tensor":
            # torch.tensor([...]) -- shape from literal data
            if call.args and isinstance(call.args[0], ast.List):
                depth, length = _measure_nested_list(call.args[0])
                if depth == 1:
                    shape = (IntLit(length),)
                elif depth == 2:
                    inner = call.args[0].elts[0] if call.args[0].elts else None
                    if isinstance(inner, ast.List):
                        shape = (IntLit(length), IntLit(len(inner.elts)))

        # Extract dtype / device from keyword args
        dtype_kw = _extract_keyword_value(call, "dtype")
        if dtype_kw is not None:
            dtype_val = _extract_dtype_name(dtype_kw)
        device_kw = _extract_keyword_value(call, "device")
        if device_kw is not None:
            device_val = _extract_device_name(device_kw)

        # Record construction fact
        var_term = Var("_result")
        pred: Optional[Predicate] = None
        if shape is not None:
            pred = ShapePred(tensor=var_term, shape=list(shape), source_location=src)

        self._add_fact(
            "_result", TensorFactKind.CONSTRUCTION, call,
            origin=TensorFactOrigin.CONSTRUCTOR,
            shape_dims=shape,
            rank_value=len(shape) if shape is not None else None,
            dtype_value=dtype_val,
            device_value=device_val,
            operation_name=basename,
            framework=framework,
            predicate=pred,
        )

    def _extract_from_value(
        self,
        var_name: str,
        value: ast.expr,
        parent_node: ast.AST,
    ) -> None:
        """Extract facts from an assignment value."""
        # y = x.reshape(...)
        if isinstance(value, ast.Call):
            if isinstance(value.func, ast.Attribute):
                method = value.func.attr
                obj_var = _extract_var_name(value.func.value)
                if obj_var is not None and method in _SHAPE_OPS:
                    shape = _extract_shape_args(value.args)
                    if shape is not None:
                        src = _source_loc(value, self._file)
                        self._add_fact(
                            var_name,
                            TensorFactKind.RESHAPE if method == "reshape" else TensorFactKind.VIEW,
                            parent_node,
                            target_shape=shape,
                            rank_value=len(shape),
                            source_variable=obj_var,
                            operation_name=method,
                            predicate=ShapePred(tensor=Var(var_name), shape=list(shape), source_location=src),
                        )

            # Constructor: y = torch.zeros(3, 4)
            full_name = _get_full_call_name(value)
            if full_name is not None and (full_name in _TORCH_CONSTRUCTOR_FUNCS or full_name in _NUMPY_CONSTRUCTOR_FUNCS):
                self._extract_constructor_assignment(var_name, full_name, value)

    def _extract_constructor_assignment(
        self,
        var_name: str,
        full_name: str,
        call: ast.Call,
    ) -> None:
        """Handle assignments from tensor constructors."""
        framework = _detect_framework(full_name)
        basename = full_name.split(".")[-1] if "." in full_name else full_name
        src = _source_loc(call, self._file)

        shape: Optional[Tuple[Term, ...]] = None
        dtype_val: Optional[str] = None
        device_val: Optional[str] = None

        if basename in ("zeros", "ones", "empty", "rand", "randn"):
            shape = _extract_shape_args(call.args)
        elif basename == "full" and call.args:
            shape = _extract_shape_args([call.args[0]])
        elif basename == "eye" and call.args:
            terms = [_ast_to_term(a) for a in call.args[:2]]
            valid = [t for t in terms if t is not None]
            if len(valid) == 1:
                shape = (valid[0], valid[0])
            elif len(valid) >= 2:
                shape = tuple(valid[:2])

        dtype_kw = _extract_keyword_value(call, "dtype")
        if dtype_kw is not None:
            dtype_val = _extract_dtype_name(dtype_kw)
        device_kw = _extract_keyword_value(call, "device")
        if device_kw is not None:
            device_val = _extract_device_name(device_kw)

        pred: Optional[Predicate] = None
        if shape is not None:
            pred = ShapePred(tensor=Var(var_name), shape=list(shape), source_location=src)

        self._add_fact(
            var_name, TensorFactKind.CONSTRUCTION, call,
            origin=TensorFactOrigin.CONSTRUCTOR,
            shape_dims=shape,
            rank_value=len(shape) if shape is not None else None,
            dtype_value=dtype_val,
            device_value=device_val,
            operation_name=basename,
            framework=framework,
            predicate=pred,
        )

    # -- BinOp: matmul operator @ --

    def visit_BinOp(self, node: ast.BinOp) -> None:
        if isinstance(node.op, ast.MatMult):
            left_var = _extract_var_name(node.left)
            right_var = _extract_var_name(node.right)
            self._add_fact(
                left_var or "_left", TensorFactKind.MATMUL, node,
                operation_name="@",
                source_variable=left_var,
            )
        self.generic_visit(node)


def _measure_nested_list(node: ast.List) -> Tuple[int, int]:
    """Measure depth and length of a nested list literal."""
    if not node.elts:
        return 1, 0
    first = node.elts[0]
    if isinstance(first, ast.List):
        inner_depth, inner_len = _measure_nested_list(first)
        return inner_depth + 1, len(node.elts)
    return 1, len(node.elts)


# ===================================================================
#  Convenience function
# ===================================================================

def harvest_tensor_facts(
    ast_tree: ast.AST,
    *,
    file: str = "<unknown>",
) -> List[TensorFact]:
    """Extract all tensor facts from a Python AST.

    Args:
        ast_tree: The parsed AST (typically from ``ast.parse``).
        file: Source file name for provenance.

    Returns:
        A list of ``TensorFact`` objects.
    """
    harvester = TensorHarvester(file=file)
    harvester.visit(ast_tree)
    return harvester.facts


# ===================================================================
#  Filtering utilities
# ===================================================================

def filter_by_variable(
    facts: List[TensorFact],
    variable: str,
) -> List[TensorFact]:
    return [f for f in facts if f.variable == variable]


def filter_by_kind(
    facts: List[TensorFact],
    kind: TensorFactKind,
) -> List[TensorFact]:
    return [f for f in facts if f.fact_kind == kind]


def shape_facts(facts: List[TensorFact]) -> List[TensorFact]:
    return [f for f in facts if f.fact_kind in (
        TensorFactKind.SHAPE, TensorFactKind.RESHAPE, TensorFactKind.VIEW,
        TensorFactKind.CONSTRUCTION,
    ) and f.shape_dims is not None]


def dtype_facts(facts: List[TensorFact]) -> List[TensorFact]:
    return [f for f in facts if f.dtype_value is not None]


def device_facts(facts: List[TensorFact]) -> List[TensorFact]:
    return [f for f in facts if f.device_value is not None]
