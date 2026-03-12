"""PyTorch-specific shape theory pack.

Extends the base tensor shape theory with PyTorch-specific shape sites
for reshape/view/broadcast/matmul/conv/pooling/normalization operations.
"""

from __future__ import annotations

import math
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

from deppy.core._protocols import (
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism

from ..theory_pack_base import (
    BoundaryClassification,
    SolverResult,
    SolverStatus,
    TheoryPackBase,
    merge_refinements,
)
from ..tensor_shape_theory import (
    ShapeInfo,
    Shape,
    Dim,
    broadcast_shapes,
    matmul_shapes,
    reshape_shape,
    conv2d_output_shape,
    transpose_shape,
    permute_shape,
    cat_shapes,
    dispatch_shape_op,
    _compute_numel,
)

# ═══════════════════════════════════════════════════════════════════════════════
# PyTorch-specific shape computations
# ═══════════════════════════════════════════════════════════════════════════════


def linear_output_shape(
    input_shape: Shape,
    out_features: int,
) -> Optional[Shape]:
    """Compute nn.Linear output shape."""
    if len(input_shape) < 1:
        return None
    return input_shape[:-1] + (out_features,)


def conv1d_output_shape(
    input_shape: Shape,
    kernel_size: int,
    stride: int = 1,
    padding: int = 0,
    dilation: int = 1,
    out_channels: Optional[int] = None,
) -> Optional[Shape]:
    """Compute Conv1d output shape."""
    if len(input_shape) != 3:
        return None
    batch, in_c, in_l = input_shape
    if not isinstance(in_l, int):
        l_out: Dim = "L_out"
    else:
        l_out = (in_l + 2 * padding - dilation * (kernel_size - 1) - 1) // stride + 1
    oc: Dim = out_channels if out_channels is not None else "C_out"
    return (batch, oc, l_out)


def conv3d_output_shape(
    input_shape: Shape,
    kernel_size: Tuple[int, int, int],
    stride: Tuple[int, int, int] = (1, 1, 1),
    padding: Tuple[int, int, int] = (0, 0, 0),
    dilation: Tuple[int, int, int] = (1, 1, 1),
    out_channels: Optional[int] = None,
) -> Optional[Shape]:
    """Compute Conv3d output shape."""
    if len(input_shape) != 5:
        return None
    batch, in_c = input_shape[0], input_shape[1]
    dims = input_shape[2:]
    out_dims: List[Dim] = []
    for i in range(3):
        d = dims[i]
        if not isinstance(d, int):
            out_dims.append(f"D{i}_out")
        else:
            out_dims.append(
                (d + 2 * padding[i] - dilation[i] * (kernel_size[i] - 1) - 1) // stride[i] + 1
            )
    oc: Dim = out_channels if out_channels is not None else "C_out"
    return (batch, oc) + tuple(out_dims)


def pool2d_output_shape(
    input_shape: Shape,
    kernel_size: Union[int, Tuple[int, int]],
    stride: Optional[Union[int, Tuple[int, int]]] = None,
    padding: Union[int, Tuple[int, int]] = 0,
    ceil_mode: bool = False,
) -> Optional[Shape]:
    """Compute MaxPool2d/AvgPool2d output shape."""
    if len(input_shape) != 4:
        return None
    batch, channels, in_h, in_w = input_shape
    if isinstance(kernel_size, int):
        kh, kw = kernel_size, kernel_size
    else:
        kh, kw = kernel_size
    if stride is None:
        sh, sw = kh, kw
    elif isinstance(stride, int):
        sh, sw = stride, stride
    else:
        sh, sw = stride
    if isinstance(padding, int):
        ph, pw = padding, padding
    else:
        ph, pw = padding
    if not isinstance(in_h, int) or not isinstance(in_w, int):
        return (batch, channels, "H_pool", "W_pool")
    if ceil_mode:
        h_out = math.ceil((in_h + 2 * ph - kh) / sh) + 1
        w_out = math.ceil((in_w + 2 * pw - kw) / sw) + 1
    else:
        h_out = (in_h + 2 * ph - kh) // sh + 1
        w_out = (in_w + 2 * pw - kw) // sw + 1
    return (batch, channels, h_out, w_out)


def adaptive_pool2d_output_shape(
    input_shape: Shape,
    output_size: Union[int, Tuple[int, int]],
) -> Optional[Shape]:
    """Compute AdaptiveAvgPool2d/AdaptiveMaxPool2d output shape."""
    if len(input_shape) != 4:
        return None
    batch, channels = input_shape[0], input_shape[1]
    if isinstance(output_size, int):
        oh, ow = output_size, output_size
    else:
        oh, ow = output_size
    return (batch, channels, oh, ow)


def batch_norm_output_shape(input_shape: Shape) -> Optional[Shape]:
    """BatchNorm preserves shape."""
    return input_shape


def embedding_output_shape(
    num_indices: Optional[int],
    embedding_dim: int,
    input_shape: Optional[Shape] = None,
) -> Optional[Shape]:
    """Compute nn.Embedding output shape."""
    if input_shape is not None:
        return input_shape + (embedding_dim,)
    if num_indices is not None:
        return (num_indices, embedding_dim)
    return ("N", embedding_dim)


def attention_output_shape(
    query_shape: Shape,
    key_shape: Shape,
    value_shape: Shape,
    num_heads: Optional[int] = None,
) -> Optional[Shape]:
    """Compute multi-head attention output shape (simplified)."""
    if len(query_shape) < 2 or len(value_shape) < 2:
        return None
    batch_dims = query_shape[:-2]
    seq_len = query_shape[-2]
    v_dim = value_shape[-1]
    return batch_dims + (seq_len, v_dim)


def rnn_output_shape(
    input_shape: Shape,
    hidden_size: int,
    num_layers: int = 1,
    bidirectional: bool = False,
    batch_first: bool = True,
) -> Optional[Shape]:
    """Compute RNN/LSTM/GRU output shape."""
    if len(input_shape) != 3:
        return None
    if batch_first:
        batch, seq_len = input_shape[0], input_shape[1]
    else:
        seq_len, batch = input_shape[0], input_shape[1]
    d = 2 if bidirectional else 1
    out_features = hidden_size * d
    if batch_first:
        return (batch, seq_len, out_features)
    else:
        return (seq_len, batch, out_features)


# ═══════════════════════════════════════════════════════════════════════════════
# PyTorch shape dispatch
# ═══════════════════════════════════════════════════════════════════════════════


def torch_shape_dispatch(
    op_name: str,
    input_shapes: List[Shape],
    params: Optional[Dict[str, Any]] = None,
) -> Optional[Shape]:
    """Dispatch a PyTorch-specific shape operation."""
    params = params or {}

    base_result = dispatch_shape_op(op_name, input_shapes, params)
    if base_result is not None:
        return base_result

    if op_name == "linear" and input_shapes:
        out_features = params.get("out_features")
        if out_features is not None:
            return linear_output_shape(input_shapes[0], int(out_features))

    elif op_name == "conv1d" and input_shapes:
        ks = params.get("kernel_size", 3)
        stride = params.get("stride", 1)
        padding = params.get("padding", 0)
        dilation = params.get("dilation", 1)
        oc = params.get("out_channels")
        return conv1d_output_shape(input_shapes[0], ks, stride, padding, dilation, oc)

    elif op_name == "conv3d" and input_shapes:
        ks = params.get("kernel_size", (3, 3, 3))
        stride = params.get("stride", (1, 1, 1))
        padding = params.get("padding", (0, 0, 0))
        dilation = params.get("dilation", (1, 1, 1))
        oc = params.get("out_channels")
        return conv3d_output_shape(input_shapes[0], ks, stride, padding, dilation, oc)

    elif op_name in ("max_pool2d", "avg_pool2d") and input_shapes:
        ks = params.get("kernel_size", 2)
        stride = params.get("stride")
        padding = params.get("padding", 0)
        ceil = params.get("ceil_mode", False)
        return pool2d_output_shape(input_shapes[0], ks, stride, padding, ceil)

    elif op_name in ("adaptive_avg_pool2d", "adaptive_max_pool2d") and input_shapes:
        output_size = params.get("output_size", (1, 1))
        return adaptive_pool2d_output_shape(input_shapes[0], output_size)

    elif op_name in ("batch_norm", "layer_norm", "group_norm", "instance_norm") and input_shapes:
        return batch_norm_output_shape(input_shapes[0])

    elif op_name == "embedding":
        dim = params.get("embedding_dim")
        input_shape = input_shapes[0] if input_shapes else None
        if dim is not None:
            return embedding_output_shape(None, int(dim), input_shape)

    elif op_name in ("rnn", "lstm", "gru") and input_shapes:
        hidden = params.get("hidden_size", 64)
        layers = params.get("num_layers", 1)
        bidir = params.get("bidirectional", False)
        bf = params.get("batch_first", True)
        return rnn_output_shape(input_shapes[0], hidden, layers, bidir, bf)

    elif op_name == "attention" and len(input_shapes) >= 3:
        heads = params.get("num_heads")
        return attention_output_shape(input_shapes[0], input_shapes[1], input_shapes[2], heads)

    elif op_name == "dropout" and input_shapes:
        return input_shapes[0]

    elif op_name in ("relu", "gelu", "silu", "sigmoid", "tanh", "softmax",
                      "log_softmax", "leaky_relu", "elu", "selu") and input_shapes:
        return input_shapes[0]

    elif op_name == "chunk" and input_shapes:
        chunks = params.get("chunks", 2)
        dim = params.get("dim", 0)
        s = list(input_shapes[0])
        ndim = len(s)
        if dim < 0:
            dim += ndim
        if 0 <= dim < ndim and isinstance(s[dim], int) and isinstance(chunks, int):
            chunk_size = math.ceil(s[dim] / chunks)
            s[dim] = chunk_size
            return tuple(s)

    elif op_name == "stack" and input_shapes:
        dim = params.get("dim", 0)
        n = len(input_shapes)
        s = list(input_shapes[0])
        ndim = len(s)
        if dim < 0:
            dim += ndim + 1
        if 0 <= dim <= ndim:
            s.insert(dim, n)
            return tuple(s)

    elif op_name == "repeat" and input_shapes:
        repeats = params.get("repeats")
        if repeats and isinstance(repeats, (list, tuple)):
            s = list(input_shapes[0])
            while len(s) < len(repeats):
                s.insert(0, 1)
            result = []
            for d, r in zip(s, repeats):
                if isinstance(d, int) and isinstance(r, int):
                    result.append(d * r)
                else:
                    result.append(f"repeat({d},{r})")
            return tuple(result)

    elif op_name == "expand" and input_shapes:
        sizes = params.get("sizes")
        if sizes and isinstance(sizes, (list, tuple)):
            return tuple(sizes)

    return None


# ═══════════════════════════════════════════════════════════════════════════════
# TorchShapePack
# ═══════════════════════════════════════════════════════════════════════════════


class TorchShapePack(TheoryPackBase):
    """PyTorch-specific shape theory pack.

    Extends the base tensor shape theory with PyTorch-specific operations
    like conv, pool, norm, attention, and RNN layers.
    """

    pack_name = "torch_shape"
    pack_priority = 24

    _APPLICABLE = frozenset({
        SiteKind.TENSOR_SHAPE,
        SiteKind.SSA_VALUE,
        SiteKind.CALL_RESULT,
        SiteKind.ERROR,
    })

    def applicable_site_kinds(self) -> FrozenSet[SiteKind]:
        return self._APPLICABLE

    def solve_local(self, site: SiteId, section: LocalSection) -> SolverResult:
        refs = section.refinements
        op_name = refs.get("shape_op") or refs.get("torch_op")

        if op_name is None:
            return SolverResult(
                status=SolverStatus.UNCHANGED,
                section=section,
                explanation="no torch shape op",
            )

        input_shapes_raw = refs.get("input_shapes", [])
        input_shapes = [tuple(s) for s in input_shapes_raw if isinstance(s, (tuple, list))]
        params = refs.get("shape_params", {})

        result_shape = torch_shape_dispatch(str(op_name), input_shapes, params)

        if result_shape is not None:
            new_info = ShapeInfo(
                shape=result_shape, ndim=len(result_shape),
                numel=_compute_numel(result_shape),
            )
            new_refs = dict(refs)
            new_refs.update(new_info.to_refinements())
            new_refs["_torch_shape_resolved"] = True

            return SolverResult(
                status=SolverStatus.SOLVED,
                section=LocalSection(
                    site_id=section.site_id,
                    carrier_type=section.carrier_type,
                    refinements=new_refs,
                    trust=TrustLevel.BOUNDED_AUTO,
                    provenance=f"torch shape: {op_name} -> {result_shape}",
                    witnesses=dict(section.witnesses),
                ),
                explanation=f"torch {op_name}: {input_shapes} -> {result_shape}",
            )

        return SolverResult(
            status=SolverStatus.REFINED,
            section=section,
            constraints_remaining=[f"torch shape op {op_name} unresolved"],
            explanation=f"torch shape op {op_name}: insufficient info",
        )

    def forward_refine(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        restricted = morphism.restrict(section)
        info = ShapeInfo.from_refinements(section.refinements)

        if not info.is_known:
            return restricted

        op_name = morphism.metadata.get("torch_op") if morphism.metadata else None
        if op_name is not None and info.shape is not None:
            params = morphism.metadata.get("shape_params", {}) if morphism.metadata else {}
            second = morphism.metadata.get("second_shape") if morphism.metadata else None
            inputs = [info.shape]
            if second is not None:
                inputs.append(tuple(second))
            result = torch_shape_dispatch(str(op_name), inputs, params)
            if result is not None:
                new_refs = merge_refinements(
                    restricted.refinements,
                    ShapeInfo(shape=result, ndim=len(result)).to_refinements(),
                    "meet",
                )
                return LocalSection(
                    site_id=restricted.site_id,
                    carrier_type=restricted.carrier_type,
                    refinements=new_refs,
                    trust=restricted.trust,
                    provenance=f"torch shape forward: {op_name} -> {result}",
                    witnesses=dict(restricted.witnesses),
                )

        new_refs = merge_refinements(restricted.refinements, info.to_refinements(), "meet")
        return LocalSection(
            site_id=restricted.site_id,
            carrier_type=restricted.carrier_type,
            refinements=new_refs,
            trust=restricted.trust,
            provenance="torch shape forward: propagated",
            witnesses=dict(restricted.witnesses),
        )

    def backward_pullback(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        refs = section.refinements
        required = {}
        shape = refs.get("shape")
        ndim = refs.get("ndim")
        if ndim is not None:
            required["ndim"] = ndim
        op_name = morphism.metadata.get("torch_op") if morphism.metadata else None
        if op_name in ("conv2d",):
            required["ndim"] = 4
        elif op_name in ("conv1d",):
            required["ndim"] = 3
        elif op_name in ("conv3d",):
            required["ndim"] = 5
        elif op_name in ("linear",) and shape is not None:
            in_features = morphism.metadata.get("shape_params", {}).get("in_features") if morphism.metadata else None
            if in_features is not None:
                required["_last_dim"] = in_features
        return LocalSection(
            site_id=morphism.source,
            carrier_type=section.carrier_type,
            refinements=required,
            trust=TrustLevel.RESIDUAL,
            provenance="torch shape pullback",
        )

    def viability_predicate(self, error_site: SiteId) -> str:
        name = error_site.name
        if "conv" in name.lower():
            return "input channels match weight, spatial dims valid"
        if "linear" in name.lower():
            return "input last dim matches in_features"
        if "pool" in name.lower():
            return "kernel fits within input spatial dims"
        return f"torch shape compatible at {name}"

    def classify_proof_boundary(self, section: LocalSection) -> BoundaryClassification:
        if section.refinements.get("_torch_shape_resolved"):
            return BoundaryClassification.FULLY_PROVEN
        info = ShapeInfo.from_refinements(section.refinements)
        if info.is_fully_concrete:
            return BoundaryClassification.CONDITIONALLY_PROVEN
        return BoundaryClassification.REQUIRES_PROOF
