"""PyTorch API signatures and semantic metadata catalog.

Provides a comprehensive catalog of PyTorch API functions with their
type signatures, shape constraints, device/dtype requirements, and
error conditions for use by the theory pack system.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
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


# ═══════════════════════════════════════════════════════════════════════════════
# API entry representation
# ═══════════════════════════════════════════════════════════════════════════════


class ParamKind(Enum):
    """Kind of function parameter."""
    TENSOR = "tensor"
    INT = "int"
    FLOAT = "float"
    BOOL = "bool"
    DTYPE = "dtype"
    DEVICE = "device"
    SHAPE = "shape"
    OPTIONAL_TENSOR = "optional_tensor"
    INT_TUPLE = "int_tuple"
    STRING = "string"
    CALLABLE = "callable"
    ANY = "any"


@dataclass(frozen=True)
class ParamSpec:
    """Specification for a function parameter."""
    name: str
    kind: ParamKind
    required: bool = True
    default: Any = None
    description: str = ""

    @property
    def is_tensor(self) -> bool:
        return self.kind in (ParamKind.TENSOR, ParamKind.OPTIONAL_TENSOR)


class ReturnKind(Enum):
    """Kind of return value."""
    TENSOR = "tensor"
    TENSOR_TUPLE = "tensor_tuple"
    NAMED_TUPLE = "named_tuple"
    SCALAR = "scalar"
    BOOL_VAL = "bool"
    NONE = "none"
    INT_VAL = "int"


@dataclass(frozen=True)
class ReturnSpec:
    """Specification for a function return value."""
    kind: ReturnKind
    count: int = 1
    names: Tuple[str, ...] = ()
    description: str = ""


@dataclass(frozen=True)
class ShapeConstraint:
    """A shape constraint for a PyTorch operation."""
    description: str
    params: Tuple[str, ...] = ()
    predicate: str = ""


@dataclass(frozen=True)
class ErrorCondition:
    """An error condition for a PyTorch operation."""
    exception_type: str
    condition: str
    message_template: str = ""


@dataclass(frozen=True)
class ApiEntry:
    """Complete API entry for a PyTorch function."""
    name: str
    module: str = "torch"
    params: Tuple[ParamSpec, ...] = ()
    returns: ReturnSpec = ReturnSpec(ReturnKind.TENSOR)
    shape_constraints: Tuple[ShapeConstraint, ...] = ()
    error_conditions: Tuple[ErrorCondition, ...] = ()
    requires_grad_safe: bool = True
    in_place: bool = False
    preserves_device: bool = True
    preserves_dtype: bool = True
    category: str = "math"
    description: str = ""
    shape_rule: str = ""

    @property
    def qualified_name(self) -> str:
        return f"{self.module}.{self.name}"

    @property
    def tensor_params(self) -> List[ParamSpec]:
        return [p for p in self.params if p.is_tensor]


# ═══════════════════════════════════════════════════════════════════════════════
# Catalog builder helpers
# ═══════════════════════════════════════════════════════════════════════════════


def _tensor(name: str, required: bool = True, desc: str = "") -> ParamSpec:
    return ParamSpec(name, ParamKind.TENSOR, required, description=desc)

def _opt_tensor(name: str, desc: str = "") -> ParamSpec:
    return ParamSpec(name, ParamKind.OPTIONAL_TENSOR, False, None, desc)

def _int(name: str, default: Any = None, required: bool = True, desc: str = "") -> ParamSpec:
    return ParamSpec(name, ParamKind.INT, required, default, desc)

def _float(name: str, default: Any = None, required: bool = True, desc: str = "") -> ParamSpec:
    return ParamSpec(name, ParamKind.FLOAT, required, default, desc)

def _bool(name: str, default: bool = False, desc: str = "") -> ParamSpec:
    return ParamSpec(name, ParamKind.BOOL, False, default, desc)

def _dtype(name: str = "dtype", desc: str = "") -> ParamSpec:
    return ParamSpec(name, ParamKind.DTYPE, False, None, desc)

def _device(name: str = "device", desc: str = "") -> ParamSpec:
    return ParamSpec(name, ParamKind.DEVICE, False, None, desc)

def _shape(name: str, desc: str = "") -> ParamSpec:
    return ParamSpec(name, ParamKind.SHAPE, True, description=desc)

def _int_tuple(name: str, default: Any = None, required: bool = True, desc: str = "") -> ParamSpec:
    return ParamSpec(name, ParamKind.INT_TUPLE, required, default, desc)


# ═══════════════════════════════════════════════════════════════════════════════
# Core operations catalog
# ═══════════════════════════════════════════════════════════════════════════════


_CATALOG: Dict[str, ApiEntry] = {}


def _register(entry: ApiEntry) -> None:
    _CATALOG[entry.qualified_name] = entry
    _CATALOG[entry.name] = entry


# Arithmetic ops
for op in ("add", "sub", "mul", "div", "remainder", "fmod", "pow"):
    _register(ApiEntry(
        name=op, module="torch",
        params=(_tensor("input"), _tensor("other")),
        returns=ReturnSpec(ReturnKind.TENSOR),
        shape_constraints=(
            ShapeConstraint("broadcast compatible", ("input", "other"), "broadcastable"),
        ),
        error_conditions=(
            ErrorCondition("RuntimeError", "device mismatch"),
        ) + (
            (ErrorCondition("ZeroDivisionError", "other == 0"),) if op in ("div", "remainder", "fmod") else ()
        ),
        shape_rule="broadcast",
        category="arithmetic",
    ))

# Comparison ops
for op in ("eq", "ne", "lt", "le", "gt", "ge"):
    _register(ApiEntry(
        name=op, module="torch",
        params=(_tensor("input"), _tensor("other")),
        returns=ReturnSpec(ReturnKind.TENSOR),
        shape_constraints=(
            ShapeConstraint("broadcast compatible", ("input", "other")),
        ),
        preserves_dtype=False,
        shape_rule="broadcast",
        category="comparison",
    ))

# Reduction ops
for op in ("sum", "mean", "prod", "max", "min", "std", "var"):
    _register(ApiEntry(
        name=op, module="torch",
        params=(
            _tensor("input"),
            _int("dim", None, False, "dimension to reduce"),
            _bool("keepdim"),
        ),
        returns=ReturnSpec(ReturnKind.TENSOR),
        shape_rule="reduce",
        category="reduction",
    ))

# Matrix ops
_register(ApiEntry(
    name="matmul", module="torch",
    params=(_tensor("input"), _tensor("other")),
    shape_constraints=(
        ShapeConstraint("inner dims match", ("input", "other"), "input[-1] == other[-2]"),
    ),
    error_conditions=(
        ErrorCondition("RuntimeError", "inner dimensions mismatch"),
    ),
    shape_rule="matmul",
    category="linalg",
))

_register(ApiEntry(
    name="mm", module="torch",
    params=(_tensor("input"), _tensor("mat2")),
    shape_constraints=(
        ShapeConstraint("2D and inner match", ("input", "mat2"), "input is 2D, mat2 is 2D, input[-1] == mat2[0]"),
    ),
    shape_rule="matmul",
    category="linalg",
))

_register(ApiEntry(
    name="bmm", module="torch",
    params=(_tensor("input"), _tensor("mat2")),
    shape_constraints=(
        ShapeConstraint("3D batch matmul", ("input", "mat2"), "both 3D, batch and inner dims match"),
    ),
    shape_rule="matmul",
    category="linalg",
))

# Shape manipulation
_register(ApiEntry(
    name="reshape", module="torch",
    params=(_tensor("input"), _shape("shape")),
    shape_constraints=(
        ShapeConstraint("numel preserved", ("input", "shape"), "input.numel() == prod(shape)"),
    ),
    error_conditions=(
        ErrorCondition("RuntimeError", "numel mismatch"),
    ),
    shape_rule="reshape",
    category="shape",
))

_register(ApiEntry(
    name="view", module="torch.Tensor",
    params=(_tensor("self"), _shape("shape")),
    shape_constraints=(
        ShapeConstraint("numel preserved, contiguous", ("self", "shape")),
    ),
    error_conditions=(
        ErrorCondition("RuntimeError", "numel mismatch or non-contiguous"),
    ),
    shape_rule="reshape",
    category="shape",
))

_register(ApiEntry(
    name="transpose", module="torch",
    params=(_tensor("input"), _int("dim0"), _int("dim1")),
    shape_rule="transpose",
    category="shape",
))

_register(ApiEntry(
    name="permute", module="torch.Tensor",
    params=(_tensor("self"), _int_tuple("dims")),
    shape_constraints=(
        ShapeConstraint("valid permutation", ("self", "dims"), "dims is permutation of range(ndim)"),
    ),
    shape_rule="permute",
    category="shape",
))

_register(ApiEntry(
    name="cat", module="torch",
    params=(_tensor("tensors"), _int("dim", 0, False)),
    shape_constraints=(
        ShapeConstraint("all dims except cat dim match", ("tensors", "dim")),
    ),
    shape_rule="cat",
    category="shape",
))

_register(ApiEntry(
    name="stack", module="torch",
    params=(_tensor("tensors"), _int("dim", 0, False)),
    shape_constraints=(
        ShapeConstraint("all tensors same shape", ("tensors",)),
    ),
    shape_rule="stack",
    category="shape",
))

# Neural network layers
_register(ApiEntry(
    name="linear", module="torch.nn.functional",
    params=(_tensor("input"), _tensor("weight"), _opt_tensor("bias")),
    shape_constraints=(
        ShapeConstraint("input last dim == weight second dim", ("input", "weight")),
    ),
    shape_rule="linear",
    category="nn",
))

_register(ApiEntry(
    name="conv2d", module="torch.nn.functional",
    params=(
        _tensor("input"), _tensor("weight"), _opt_tensor("bias"),
        _int_tuple("stride", (1, 1), False),
        _int_tuple("padding", (0, 0), False),
        _int_tuple("dilation", (1, 1), False),
        _int("groups", 1, False),
    ),
    shape_constraints=(
        ShapeConstraint("4D input, channels match", ("input", "weight", "groups")),
    ),
    error_conditions=(
        ErrorCondition("RuntimeError", "input not 4D or channels mismatch"),
    ),
    shape_rule="conv2d",
    category="nn",
))

_register(ApiEntry(
    name="conv1d", module="torch.nn.functional",
    params=(
        _tensor("input"), _tensor("weight"), _opt_tensor("bias"),
        _int("stride", 1, False), _int("padding", 0, False),
        _int("dilation", 1, False), _int("groups", 1, False),
    ),
    shape_rule="conv1d",
    category="nn",
))

_register(ApiEntry(
    name="max_pool2d", module="torch.nn.functional",
    params=(
        _tensor("input"), _int_tuple("kernel_size"),
        _int_tuple("stride", None, False), _int_tuple("padding", (0, 0), False),
        _int_tuple("dilation", (1, 1), False), _bool("ceil_mode"),
        _bool("return_indices"),
    ),
    shape_rule="pool2d",
    category="nn",
))

_register(ApiEntry(
    name="avg_pool2d", module="torch.nn.functional",
    params=(
        _tensor("input"), _int_tuple("kernel_size"),
        _int_tuple("stride", None, False), _int_tuple("padding", (0, 0), False),
        _bool("ceil_mode"), _bool("count_include_pad"),
    ),
    shape_rule="pool2d",
    category="nn",
))

# Activations
for act in ("relu", "sigmoid", "tanh", "softmax", "log_softmax",
            "gelu", "silu", "leaky_relu", "elu", "selu", "mish"):
    _register(ApiEntry(
        name=act, module="torch.nn.functional",
        params=(_tensor("input"),) + ((_int("dim"),) if act in ("softmax", "log_softmax") else ()),
        shape_rule="identity",
        category="activation",
    ))

# Loss functions
_register(ApiEntry(
    name="cross_entropy", module="torch.nn.functional",
    params=(_tensor("input"), _tensor("target")),
    shape_constraints=(
        ShapeConstraint("input is (N, C), target is (N,)", ("input", "target")),
    ),
    shape_rule="loss",
    category="loss",
))

_register(ApiEntry(
    name="mse_loss", module="torch.nn.functional",
    params=(_tensor("input"), _tensor("target")),
    shape_constraints=(
        ShapeConstraint("same shape", ("input", "target")),
    ),
    shape_rule="loss",
    category="loss",
))

# Normalization
for norm in ("batch_norm", "layer_norm", "group_norm", "instance_norm"):
    _register(ApiEntry(
        name=norm, module="torch.nn.functional",
        params=(_tensor("input"),),
        shape_rule="identity",
        category="normalization",
    ))

_register(ApiEntry(
    name="dropout", module="torch.nn.functional",
    params=(_tensor("input"), _float("p", 0.5, False), _bool("training", True)),
    shape_rule="identity",
    category="regularization",
))

_register(ApiEntry(
    name="embedding", module="torch.nn.functional",
    params=(_tensor("input"), _tensor("weight")),
    shape_rule="embedding",
    category="nn",
))


# ═══════════════════════════════════════════════════════════════════════════════
# Catalog query API
# ═══════════════════════════════════════════════════════════════════════════════


def lookup_api(name: str) -> Optional[ApiEntry]:
    """Look up an API entry by name (qualified or short)."""
    return _CATALOG.get(name)


def lookup_api_fuzzy(name: str) -> List[ApiEntry]:
    """Look up API entries matching a substring."""
    results = []
    name_lower = name.lower()
    for key, entry in _CATALOG.items():
        if name_lower in key.lower():
            if entry not in results:
                results.append(entry)
    return results


def get_shape_rule(api_name: str) -> Optional[str]:
    """Get the shape rule name for a PyTorch operation."""
    entry = lookup_api(api_name)
    if entry is not None:
        return entry.shape_rule
    return None


def get_error_conditions(api_name: str) -> List[ErrorCondition]:
    """Get error conditions for a PyTorch operation."""
    entry = lookup_api(api_name)
    if entry is not None:
        return list(entry.error_conditions)
    return []


def get_shape_constraints(api_name: str) -> List[ShapeConstraint]:
    """Get shape constraints for a PyTorch operation."""
    entry = lookup_api(api_name)
    if entry is not None:
        return list(entry.shape_constraints)
    return []


def all_entries() -> List[ApiEntry]:
    """Return all unique API entries."""
    seen: Set[str] = set()
    entries: List[ApiEntry] = []
    for key, entry in _CATALOG.items():
        if entry.qualified_name not in seen:
            seen.add(entry.qualified_name)
            entries.append(entry)
    return entries


def entries_by_category(category: str) -> List[ApiEntry]:
    """Return all entries in a category."""
    return [e for e in all_entries() if e.category == category]


def categories() -> List[str]:
    """Return all categories."""
    cats: Set[str] = set()
    for e in all_entries():
        cats.add(e.category)
    return sorted(cats)
