"""PyTorch library theory pack for tensor shape, device, and dtype analysis.

Provides PyTorch-specific theory packs:
  - TorchShapePack: shape propagation for PyTorch operations
  - torch_api_catalog: API signature and metadata catalog
"""

from .torch_shape_pack import (
    TorchShapePack,
    torch_shape_dispatch,
    linear_output_shape,
    conv1d_output_shape,
    conv3d_output_shape,
    pool2d_output_shape,
    adaptive_pool2d_output_shape,
    batch_norm_output_shape,
    embedding_output_shape,
    attention_output_shape,
    rnn_output_shape,
)

from .torch_api_catalog import (
    ApiEntry,
    ParamSpec,
    ParamKind,
    ReturnSpec,
    ReturnKind,
    ShapeConstraint,
    ErrorCondition,
    lookup_api,
    lookup_api_fuzzy,
    get_shape_rule,
    get_error_conditions,
    get_shape_constraints,
    all_entries,
    entries_by_category,
    categories,
)

__all__ = [
    "TorchShapePack",
    "torch_shape_dispatch",
    "linear_output_shape",
    "conv1d_output_shape",
    "conv3d_output_shape",
    "pool2d_output_shape",
    "adaptive_pool2d_output_shape",
    "batch_norm_output_shape",
    "embedding_output_shape",
    "attention_output_shape",
    "rnn_output_shape",
    "ApiEntry",
    "ParamSpec",
    "ParamKind",
    "ReturnSpec",
    "ReturnKind",
    "ShapeConstraint",
    "ErrorCondition",
    "lookup_api",
    "lookup_api_fuzzy",
    "get_shape_rule",
    "get_error_conditions",
    "get_shape_constraints",
    "all_entries",
    "entries_by_category",
    "categories",
]
