"""PyTorch Theory Pack — Tensor shape algebra and nn module tracking.

Tensor Shape Tracking
─────────────────────
PyTorch tensors carry a ``shape`` (alias ``size()``) that determines the
dimensionality of the data.  Virtually every operation in PyTorch has
shape-level preconditions and postconditions:

  • ``view(shape)`` requires ``prod(old_shape) == prod(new_shape)``
  • ``mm(a, b)`` requires ``a.shape[1] == b.shape[0]``
  • ``nn.Linear(in_features, out_features)`` maps
    ``(..., in_features) → (..., out_features)``

This theory pack encodes these constraints so that the hybrid checker can
catch shape mismatches *before* the code reaches the GPU.

nn Module Tracking
──────────────────
The ``torch.nn`` zoo is large and version-sensitive.  Each ``nn.Module`` and
``nn.functional`` function is catalogued with its input/output shape contract,
enabling the verifier to trace shapes through entire neural network forward
passes.

Version Tracking
────────────────
PyTorch evolves rapidly.  Each API entry optionally records ``added_in`` and
``deprecated_in`` so that the anti-hallucination layer can warn when code
targets a newer API than the project's pinned PyTorch version.
"""

from __future__ import annotations


# --- Integration with existing deppy codebase ---
try:
    from deppy.theory_packs import register_pack_spec, TheoryPackSpec
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

from typing import Dict, List

from deppy.hybrid.theory_library.base import (

    APIEntry,
    Axiom,
    HybridTheoryPack,
    TheoryPackMeta,
    TypeRule,
)

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _api(
    module: str,
    name: str,
    signature: str,
    description: str = "",
    *,
    lean_type: str | None = None,
    structural: list[str] | None = None,
    semantic: list[str] | None = None,
    added_in: str | None = None,
    deprecated_in: str | None = None,
) -> APIEntry:
    return APIEntry(
        module=module,
        name=name,
        signature=signature,
        lean_type=lean_type,
        description=description,
        structural_properties=structural or [],
        semantic_properties=semantic or [],
        added_in=added_in,
        deprecated_in=deprecated_in,
    )

# ---------------------------------------------------------------------------
# TorchTheoryPack
# ---------------------------------------------------------------------------

class TorchTheoryPack(HybridTheoryPack):
    """Theory pack for PyTorch ≥ 1.10 with tensor shape algebra."""

    def __init__(self) -> None:
        meta = TheoryPackMeta(
            name="PyTorch Theory Pack",
            version="1.0.0",
            library_name="torch",
            library_version="1.10",
            description=(
                "Tensor shape algebra, nn module contracts, and semantic "
                "axioms for PyTorch.  Encodes preconditions for view, matmul, "
                "Linear, Conv2d, and the full nn zoo so that shape mismatches "
                "are caught before GPU execution."
            ),
            author="deppy contributors",
        )

        entries = self._build_api_entries()
        api_dict: Dict[str, APIEntry] = {}
        for e in entries:
            api_dict[e.qualified_name] = e

        super().__init__(
            meta=meta,
            api_entries=api_dict,
            type_rules=self._build_type_rules(),
            axioms=self._build_axioms(),
        )

    # ── API entries ────────────────────────────────────────────────────────

    @staticmethod
    def _build_api_entries() -> List[APIEntry]:  # noqa: C901
        entries: List[APIEntry] = []
        _a = entries.append

        # -- tensor creation -------------------------------------------------
        _a(_api("torch", "tensor",
               "(data, *, dtype=None, device=None, requires_grad=False, pin_memory=False) -> Tensor",
               "Construct a tensor from data."))
        _a(_api("torch", "zeros",
               "(*size, *, out=None, dtype=None, layout=torch.strided, device=None, requires_grad=False) -> Tensor",
               "Return a tensor filled with zeros.",
               structural=["result.shape == size", "all(result == 0)"]))
        _a(_api("torch", "ones",
               "(*size, *, out=None, dtype=None, layout=torch.strided, device=None, requires_grad=False) -> Tensor",
               "Return a tensor filled with ones.",
               structural=["result.shape == size", "all(result == 1)"]))
        _a(_api("torch", "randn",
               "(*size, *, out=None, dtype=None, layout=torch.strided, device=None, requires_grad=False) -> Tensor",
               "Return a tensor filled with random numbers from N(0,1).",
               structural=["result.shape == size"]))
        _a(_api("torch", "rand",
               "(*size, *, out=None, dtype=None, layout=torch.strided, device=None, requires_grad=False) -> Tensor",
               "Return a tensor filled with random numbers from U(0,1).",
               structural=["result.shape == size"]))
        _a(_api("torch", "empty",
               "(*size, *, out=None, dtype=None, layout=torch.strided, device=None, requires_grad=False, pin_memory=False, memory_format=torch.contiguous_format) -> Tensor",
               "Return an uninitialised tensor.",
               structural=["result.shape == size"]))
        _a(_api("torch", "full",
               "(size, fill_value, *, out=None, dtype=None, layout=torch.strided, device=None, requires_grad=False) -> Tensor",
               "Return a tensor filled with fill_value.",
               structural=["result.shape == size"]))
        _a(_api("torch", "arange",
               "(start=0, end, step=1, *, out=None, dtype=None, layout=torch.strided, device=None, requires_grad=False) -> Tensor",
               "Return a 1-D tensor with values from [start, end).",
               structural=["result.ndim == 1"]))
        _a(_api("torch", "linspace",
               "(start, end, steps, *, out=None, dtype=None, layout=torch.strided, device=None, requires_grad=False) -> Tensor",
               "Return a 1-D tensor with evenly spaced values.",
               structural=["result.shape == (steps,)"]))
        _a(_api("torch", "logspace",
               "(start, end, steps, base=10.0, *, out=None, dtype=None, layout=torch.strided, device=None, requires_grad=False) -> Tensor",
               "Return a 1-D tensor with log-spaced values.",
               structural=["result.shape == (steps,)"]))
        _a(_api("torch", "eye",
               "(n: int, m: int | None = None, *, out=None, dtype=None, layout=torch.strided, device=None, requires_grad=False) -> Tensor",
               "Return a 2-D identity tensor.",
               structural=["result.shape == (n, m if m else n)"]))
        _a(_api("torch", "zeros_like",
               "(input: Tensor, *, dtype=None, layout=None, device=None, requires_grad=False, memory_format=torch.preserve_format) -> Tensor",
               "Return a tensor of zeros with the same size as input.",
               structural=["result.shape == input.shape"]))
        _a(_api("torch", "ones_like",
               "(input: Tensor, *, dtype=None, layout=None, device=None, requires_grad=False, memory_format=torch.preserve_format) -> Tensor",
               "Return a tensor of ones with the same size as input.",
               structural=["result.shape == input.shape"]))
        _a(_api("torch", "rand_like",
               "(input: Tensor, *, dtype=None, layout=None, device=None, requires_grad=False, memory_format=torch.preserve_format) -> Tensor",
               "Return a tensor with the same size as input, filled with U(0,1).",
               structural=["result.shape == input.shape"]))
        _a(_api("torch", "randn_like",
               "(input: Tensor, *, dtype=None, layout=None, device=None, requires_grad=False, memory_format=torch.preserve_format) -> Tensor",
               "Return a tensor with the same size as input, filled with N(0,1).",
               structural=["result.shape == input.shape"]))
        _a(_api("torch", "from_numpy",
               "(ndarray) -> Tensor",
               "Create a Tensor from a numpy ndarray."))

        # -- tensor shape manipulation ---------------------------------------
        _a(_api("torch.Tensor", "view",
               "(self, *shape) -> Tensor",
               "Returns a new tensor with the same data but different shape.",
               structural=["prod(result.shape) == prod(self.shape)", "result.shape == shape"]))
        _a(_api("torch.Tensor", "reshape",
               "(self, *shape) -> Tensor",
               "Returns a tensor with the same data and number of elements but different shape.",
               structural=["prod(result.shape) == prod(self.shape)", "result.shape == shape"]))
        _a(_api("torch.Tensor", "transpose",
               "(self, dim0: int, dim1: int) -> Tensor",
               "Transpose two dimensions.",
               structural=["result.shape[dim0] == self.shape[dim1]", "result.shape[dim1] == self.shape[dim0]"]))
        _a(_api("torch.Tensor", "permute",
               "(self, *dims) -> Tensor",
               "Permute the dimensions of this tensor.",
               structural=["result.shape == tuple(self.shape[d] for d in dims)"]))
        _a(_api("torch.Tensor", "contiguous",
               "(self, memory_format=torch.contiguous_format) -> Tensor",
               "Return a contiguous in memory tensor with same data.",
               structural=["result.shape == self.shape"]))
        _a(_api("torch.Tensor", "squeeze",
               "(self, dim=None) -> Tensor",
               "Remove dimensions of size 1."))
        _a(_api("torch.Tensor", "unsqueeze",
               "(self, dim: int) -> Tensor",
               "Add a dimension of size 1 at the specified position.",
               structural=["result.ndim == self.ndim + 1", "result.shape[dim] == 1"]))
        _a(_api("torch.Tensor", "expand",
               "(self, *sizes) -> Tensor",
               "Expand the tensor to a larger size.",
               structural=["result.ndim == self.ndim"]))
        _a(_api("torch.Tensor", "repeat",
               "(self, *repeats) -> Tensor",
               "Repeat the tensor along the specified dimensions.",
               structural=["result.shape[i] == self.shape[i] * repeats[i]"]))
        _a(_api("torch.Tensor", "flatten",
               "(self, start_dim=0, end_dim=-1) -> Tensor",
               "Flatten a contiguous range of dims.",
               structural=["result.size == self.size"]))
        _a(_api("torch.Tensor", "unflatten",
               "(self, dim: int, sizes) -> Tensor",
               "Expand a single dimension into multiple.",
               added_in="1.11"))
        _a(_api("torch.Tensor", "narrow",
               "(self, dim: int, start: int, length: int) -> Tensor",
               "Return a narrowed version of the tensor.",
               structural=["result.shape[dim] == length"]))
        _a(_api("torch.Tensor", "chunk",
               "(self, chunks: int, dim: int = 0) -> tuple[Tensor, ...]",
               "Split a tensor into chunks."))
        _a(_api("torch.Tensor", "split",
               "(self, split_size_or_sections, dim: int = 0) -> tuple[Tensor, ...]",
               "Split the tensor into chunks."))
        _a(_api("torch.Tensor", "t",
               "(self) -> Tensor",
               "Transpose a 2D tensor (0 and 1 are permuted).",
               structural=["result.shape == (self.shape[1], self.shape[0])"]))
        _a(_api("torch.Tensor", "clone",
               "(self, *, memory_format=torch.preserve_format) -> Tensor",
               "Return a copy of self.",
               structural=["result.shape == self.shape"]))
        _a(_api("torch.Tensor", "detach",
               "(self) -> Tensor",
               "Detach from computation graph.",
               structural=["result.shape == self.shape"]))

        # -- concatenation / stacking ----------------------------------------
        _a(_api("torch", "cat",
               "(tensors: tuple[Tensor, ...] | list[Tensor], dim: int = 0, *, out=None) -> Tensor",
               "Concatenate tensors along an existing dimension.",
               structural=["result.shape[dim] == sum(t.shape[dim] for t in tensors)"]))
        _a(_api("torch", "stack",
               "(tensors: tuple[Tensor, ...] | list[Tensor], dim: int = 0, *, out=None) -> Tensor",
               "Concatenate tensors along a new dimension.",
               structural=["result.ndim == tensors[0].ndim + 1"]))
        _a(_api("torch", "split",
               "(tensor: Tensor, split_size_or_sections, dim: int = 0) -> tuple[Tensor, ...]",
               "Split a tensor into chunks."))
        _a(_api("torch", "chunk",
               "(input: Tensor, chunks: int, dim: int = 0) -> tuple[Tensor, ...]",
               "Split a tensor into a specific number of chunks."))
        _a(_api("torch", "unbind",
               "(input: Tensor, dim: int = 0) -> tuple[Tensor, ...]",
               "Remove a tensor dimension.",
               structural=["len(result) == input.shape[dim]"]))

        # -- matrix operations -----------------------------------------------
        _a(_api("torch", "matmul",
               "(input: Tensor, other: Tensor, *, out=None) -> Tensor",
               "Matrix product of two tensors.",
               structural=[
                   "input.shape[-1] == other.shape[-2]",
                   "result.shape[-2:] == (input.shape[-2], other.shape[-1])",
               ]))
        _a(_api("torch", "bmm",
               "(input: Tensor, mat2: Tensor, *, out=None) -> Tensor",
               "Batched matrix multiplication.",
               structural=[
                   "input.shape[0] == mat2.shape[0]",
                   "input.shape[2] == mat2.shape[1]",
                   "result.shape == (input.shape[0], input.shape[1], mat2.shape[2])",
               ]))
        _a(_api("torch", "mm",
               "(input: Tensor, mat2: Tensor, *, out=None) -> Tensor",
               "Matrix multiplication of two 2D tensors.",
               structural=[
                   "input.shape[1] == mat2.shape[0]",
                   "result.shape == (input.shape[0], mat2.shape[1])",
               ]))
        _a(_api("torch", "mv",
               "(input: Tensor, vec: Tensor, *, out=None) -> Tensor",
               "Matrix-vector product.",
               structural=[
                   "input.ndim == 2", "vec.ndim == 1",
                   "input.shape[1] == vec.shape[0]",
                   "result.shape == (input.shape[0],)",
               ]))
        _a(_api("torch", "addmm",
               "(input: Tensor, mat1: Tensor, mat2: Tensor, *, beta=1, alpha=1, out=None) -> Tensor",
               "Performs input + alpha * (mat1 @ mat2).",
               structural=["mat1.shape[1] == mat2.shape[0]"]))
        _a(_api("torch", "einsum",
               "(equation: str, *operands) -> Tensor",
               "Einstein summation."))

        # -- reductions ------------------------------------------------------
        _a(_api("torch", "sum",
               "(input: Tensor, dim=None, keepdim=False, *, dtype=None) -> Tensor",
               "Returns the sum of all elements."))
        _a(_api("torch", "mean",
               "(input: Tensor, dim=None, keepdim=False, *, dtype=None) -> Tensor",
               "Returns the mean value of all elements."))
        _a(_api("torch", "std",
               "(input: Tensor, dim=None, unbiased=True, keepdim=False) -> Tensor",
               "Returns the standard deviation.",
               structural=["result >= 0"]))
        _a(_api("torch", "var",
               "(input: Tensor, dim=None, unbiased=True, keepdim=False) -> Tensor",
               "Returns the variance.",
               structural=["result >= 0"]))
        _a(_api("torch", "min",
               "(input: Tensor, dim=None, keepdim=False) -> Tensor | namedtuple",
               "Returns the minimum value."))
        _a(_api("torch", "max",
               "(input: Tensor, dim=None, keepdim=False) -> Tensor | namedtuple",
               "Returns the maximum value."))
        _a(_api("torch", "argmin",
               "(input: Tensor, dim=None, keepdim=False) -> Tensor",
               "Returns the indices of the minimum value."))
        _a(_api("torch", "argmax",
               "(input: Tensor, dim=None, keepdim=False) -> Tensor",
               "Returns the indices of the maximum value."))
        _a(_api("torch", "norm",
               "(input: Tensor, p='fro', dim=None, keepdim=False, out=None, dtype=None) -> Tensor",
               "Returns the matrix norm or vector norm.",
               structural=["result >= 0"]))
        _a(_api("torch", "prod",
               "(input: Tensor, dim=None, keepdim=False, *, dtype=None) -> Tensor",
               "Returns the product of all elements."))
        _a(_api("torch", "cumsum",
               "(input: Tensor, dim: int, *, dtype=None) -> Tensor",
               "Returns the cumulative sum along a dimension.",
               structural=["result.shape == input.shape"]))
        _a(_api("torch", "cumprod",
               "(input: Tensor, dim: int, *, dtype=None) -> Tensor",
               "Returns the cumulative product along a dimension.",
               structural=["result.shape == input.shape"]))

        # -- element-wise operations -----------------------------------------
        _a(_api("torch", "abs",
               "(input: Tensor, *, out=None) -> Tensor",
               "Compute element-wise absolute value.",
               structural=["result.shape == input.shape", "all(result >= 0)"]))
        _a(_api("torch", "sqrt",
               "(input: Tensor, *, out=None) -> Tensor",
               "Compute element-wise square root.",
               structural=["result.shape == input.shape"]))
        _a(_api("torch", "exp",
               "(input: Tensor, *, out=None) -> Tensor",
               "Compute element-wise exponential.",
               structural=["result.shape == input.shape", "all(result > 0)"]))
        _a(_api("torch", "log",
               "(input: Tensor, *, out=None) -> Tensor",
               "Compute element-wise natural logarithm.",
               structural=["result.shape == input.shape"]))
        _a(_api("torch", "sin",
               "(input: Tensor, *, out=None) -> Tensor",
               "Compute element-wise sine.",
               structural=["result.shape == input.shape"]))
        _a(_api("torch", "cos",
               "(input: Tensor, *, out=None) -> Tensor",
               "Compute element-wise cosine.",
               structural=["result.shape == input.shape"]))
        _a(_api("torch", "tanh",
               "(input: Tensor, *, out=None) -> Tensor",
               "Compute element-wise hyperbolic tangent.",
               structural=["result.shape == input.shape"]))
        _a(_api("torch", "sigmoid",
               "(input: Tensor, *, out=None) -> Tensor",
               "Compute element-wise sigmoid.",
               structural=["result.shape == input.shape", "all(0 <= result <= 1)"]))
        _a(_api("torch", "clamp",
               "(input: Tensor, min=None, max=None, *, out=None) -> Tensor",
               "Clamp all elements to [min, max].",
               structural=["result.shape == input.shape"]))
        _a(_api("torch", "pow",
               "(input: Tensor, exponent, *, out=None) -> Tensor",
               "Element-wise power.",
               structural=["result.shape == input.shape"]))
        _a(_api("torch", "where",
               "(condition: Tensor, input: Tensor, other: Tensor) -> Tensor",
               "Select elements from input or other based on condition.",
               structural=["result.shape == broadcast(condition.shape, input.shape, other.shape)"]))
        _a(_api("torch", "sort",
               "(input: Tensor, dim=-1, descending=False, stable=False) -> namedtuple",
               "Sort a tensor along a dimension.",
               structural=["result.values.shape == input.shape"]))

        # -- comparison / boolean --------------------------------------------
        _a(_api("torch", "eq",
               "(input: Tensor, other) -> Tensor",
               "Element-wise equality.",
               structural=["result.shape == broadcast(input.shape, other.shape)"]))
        _a(_api("torch", "ne",
               "(input: Tensor, other) -> Tensor",
               "Element-wise inequality.",
               structural=["result.shape == broadcast(input.shape, other.shape)"]))
        _a(_api("torch", "isnan",
               "(input: Tensor) -> Tensor",
               "Element-wise NaN test.",
               structural=["result.shape == input.shape"]))
        _a(_api("torch", "isinf",
               "(input: Tensor) -> Tensor",
               "Element-wise infinity test.",
               structural=["result.shape == input.shape"]))

        # -- nn.Module layers ------------------------------------------------
        _a(_api("torch.nn", "Linear",
               "(in_features: int, out_features: int, bias: bool = True, device=None, dtype=None) -> Linear",
               "Applies a linear transformation: y = xA^T + b.",
               structural=["input: (..., in_features) -> output: (..., out_features)"]))
        _a(_api("torch.nn", "Conv1d",
               "(in_channels: int, out_channels: int, kernel_size, stride=1, padding=0, dilation=1, groups=1, bias=True, ...) -> Conv1d",
               "Applies a 1D convolution."))
        _a(_api("torch.nn", "Conv2d",
               "(in_channels: int, out_channels: int, kernel_size, stride=1, padding=0, dilation=1, groups=1, bias=True, ...) -> Conv2d",
               "Applies a 2D convolution.",
               structural=["input: (N, C_in, H, W) -> output: (N, C_out, H', W')"]))
        _a(_api("torch.nn", "Conv3d",
               "(in_channels: int, out_channels: int, kernel_size, stride=1, padding=0, dilation=1, groups=1, bias=True, ...) -> Conv3d",
               "Applies a 3D convolution."))
        _a(_api("torch.nn", "ConvTranspose2d",
               "(in_channels: int, out_channels: int, kernel_size, stride=1, padding=0, output_padding=0, groups=1, bias=True, dilation=1, ...) -> ConvTranspose2d",
               "Applies a 2D transposed convolution."))
        _a(_api("torch.nn", "BatchNorm1d",
               "(num_features: int, eps=1e-05, momentum=0.1, affine=True, track_running_stats=True, ...) -> BatchNorm1d",
               "Applies Batch Normalisation over a 2D or 3D input.",
               structural=["output.shape == input.shape"]))
        _a(_api("torch.nn", "BatchNorm2d",
               "(num_features: int, eps=1e-05, momentum=0.1, affine=True, track_running_stats=True, ...) -> BatchNorm2d",
               "Applies Batch Normalisation over a 4D input.",
               structural=["output.shape == input.shape"]))
        _a(_api("torch.nn", "LayerNorm",
               "(normalized_shape, eps=1e-05, elementwise_affine=True, ...) -> LayerNorm",
               "Applies Layer Normalisation.",
               structural=["output.shape == input.shape"]))
        _a(_api("torch.nn", "GroupNorm",
               "(num_groups: int, num_channels: int, eps=1e-05, affine=True, ...) -> GroupNorm",
               "Applies Group Normalisation.",
               structural=["output.shape == input.shape"]))
        _a(_api("torch.nn", "InstanceNorm2d",
               "(num_features: int, eps=1e-05, momentum=0.1, affine=False, track_running_stats=False) -> InstanceNorm2d",
               "Applies Instance Normalisation.",
               structural=["output.shape == input.shape"]))
        _a(_api("torch.nn", "Dropout",
               "(p: float = 0.5, inplace: bool = False) -> Dropout",
               "Randomly zero elements during training.",
               structural=["output.shape == input.shape"]))
        _a(_api("torch.nn", "Dropout2d",
               "(p: float = 0.5, inplace: bool = False) -> Dropout2d",
               "Randomly zero entire channels during training.",
               structural=["output.shape == input.shape"]))
        _a(_api("torch.nn", "ReLU",
               "(inplace: bool = False) -> ReLU",
               "Rectified Linear Unit activation.",
               structural=["output.shape == input.shape"],
               semantic=["all(output >= 0)"]))
        _a(_api("torch.nn", "LeakyReLU",
               "(negative_slope: float = 0.01, inplace: bool = False) -> LeakyReLU",
               "Leaky ReLU activation.",
               structural=["output.shape == input.shape"]))
        _a(_api("torch.nn", "GELU",
               "(approximate: str = 'none') -> GELU",
               "Gaussian Error Linear Unit activation.",
               structural=["output.shape == input.shape"]))
        _a(_api("torch.nn", "SiLU",
               "(inplace: bool = False) -> SiLU",
               "Sigmoid Linear Unit (SiLU / Swish).",
               structural=["output.shape == input.shape"], added_in="1.7"))
        _a(_api("torch.nn", "Sigmoid",
               "() -> Sigmoid",
               "Sigmoid activation.",
               structural=["output.shape == input.shape"],
               semantic=["all(0 <= output <= 1)"]))
        _a(_api("torch.nn", "Tanh",
               "() -> Tanh",
               "Hyperbolic tangent activation.",
               structural=["output.shape == input.shape"],
               semantic=["all(-1 <= output <= 1)"]))
        _a(_api("torch.nn", "Softmax",
               "(dim: int | None = None) -> Softmax",
               "Softmax activation.",
               structural=["output.shape == input.shape"],
               semantic=["all(0 <= output <= 1)", "output.sum(dim=dim) ≈ 1"]))
        _a(_api("torch.nn", "LogSoftmax",
               "(dim: int | None = None) -> LogSoftmax",
               "Log-Softmax activation.",
               structural=["output.shape == input.shape"],
               semantic=["all(output <= 0)"]))
        _a(_api("torch.nn", "Embedding",
               "(num_embeddings: int, embedding_dim: int, padding_idx=None, ...) -> Embedding",
               "Simple lookup table for embeddings.",
               structural=["input: (*) -> output: (*, embedding_dim)"]))
        _a(_api("torch.nn", "EmbeddingBag",
               "(num_embeddings: int, embedding_dim: int, ...) -> EmbeddingBag",
               "Compute sums or means of bags of embeddings."))
        _a(_api("torch.nn", "LSTM",
               "(input_size: int, hidden_size: int, num_layers: int = 1, bias: bool = True, batch_first: bool = False, dropout: float = 0, bidirectional: bool = False, ...) -> LSTM",
               "Applies a multi-layer long short-term memory (LSTM) RNN."))
        _a(_api("torch.nn", "GRU",
               "(input_size: int, hidden_size: int, num_layers: int = 1, bias: bool = True, batch_first: bool = False, dropout: float = 0, bidirectional: bool = False, ...) -> GRU",
               "Applies a multi-layer gated recurrent unit (GRU) RNN."))
        _a(_api("torch.nn", "RNN",
               "(input_size: int, hidden_size: int, num_layers: int = 1, nonlinearity: str = 'tanh', bias: bool = True, batch_first: bool = False, dropout: float = 0, bidirectional: bool = False) -> RNN",
               "Applies a multi-layer Elman RNN."))
        _a(_api("torch.nn", "MultiheadAttention",
               "(embed_dim: int, num_heads: int, dropout: float = 0.0, bias: bool = True, ...) -> MultiheadAttention",
               "Multi-Head Attention mechanism.",
               structural=["embed_dim % num_heads == 0"]))
        _a(_api("torch.nn", "TransformerEncoder",
               "(encoder_layer, num_layers: int, norm=None, ...) -> TransformerEncoder",
               "TransformerEncoder is a stack of N encoder layers."))
        _a(_api("torch.nn", "TransformerDecoder",
               "(decoder_layer, num_layers: int, norm=None) -> TransformerDecoder",
               "TransformerDecoder is a stack of N decoder layers."))
        _a(_api("torch.nn", "TransformerEncoderLayer",
               "(d_model: int, nhead: int, dim_feedforward: int = 2048, dropout: float = 0.1, ...) -> TransformerEncoderLayer",
               "A single layer of the transformer encoder."))
        _a(_api("torch.nn", "TransformerDecoderLayer",
               "(d_model: int, nhead: int, dim_feedforward: int = 2048, dropout: float = 0.1, ...) -> TransformerDecoderLayer",
               "A single layer of the transformer decoder."))
        _a(_api("torch.nn", "Transformer",
               "(d_model: int = 512, nhead: int = 8, num_encoder_layers: int = 6, num_decoder_layers: int = 6, dim_feedforward: int = 2048, dropout: float = 0.1, ...) -> Transformer",
               "Full transformer model."))
        _a(_api("torch.nn", "MaxPool2d",
               "(kernel_size, stride=None, padding=0, dilation=1, return_indices=False, ceil_mode=False) -> MaxPool2d",
               "Applies a 2D max pooling."))
        _a(_api("torch.nn", "AvgPool2d",
               "(kernel_size, stride=None, padding=0, ceil_mode=False, count_include_pad=True, divisor_override=None) -> AvgPool2d",
               "Applies a 2D average pooling."))
        _a(_api("torch.nn", "AdaptiveAvgPool2d",
               "(output_size) -> AdaptiveAvgPool2d",
               "Applies 2D adaptive average pooling.",
               structural=["output.shape[-2:] == output_size"]))
        _a(_api("torch.nn", "MaxPool1d",
               "(kernel_size, stride=None, padding=0, dilation=1, return_indices=False, ceil_mode=False) -> MaxPool1d",
               "Applies a 1D max pooling."))
        _a(_api("torch.nn", "AdaptiveAvgPool1d",
               "(output_size: int) -> AdaptiveAvgPool1d",
               "Applies 1D adaptive average pooling."))
        _a(_api("torch.nn", "Flatten",
               "(start_dim: int = 1, end_dim: int = -1) -> Flatten",
               "Flattens a contiguous range of dims into a tensor."))
        _a(_api("torch.nn", "Unflatten",
               "(dim: int, unflattened_size) -> Unflatten",
               "Unflatten a tensor dim expanding it to a desired shape.",
               added_in="1.11"))
        _a(_api("torch.nn", "Sequential",
               "(*args) -> Sequential",
               "A sequential container for modules."))
        _a(_api("torch.nn", "ModuleList",
               "(modules=None) -> ModuleList",
               "Holds submodules in a list."))
        _a(_api("torch.nn", "ModuleDict",
               "(modules=None) -> ModuleDict",
               "Holds submodules in a dict."))
        _a(_api("torch.nn", "ParameterList",
               "(parameters=None) -> ParameterList",
               "Holds parameters in a list."))
        _a(_api("torch.nn", "Parameter",
               "(data: Tensor, requires_grad: bool = True) -> Parameter",
               "A Tensor that is a module parameter."))
        _a(_api("torch.nn", "CrossEntropyLoss",
               "(weight=None, size_average=None, ignore_index=-100, reduce=None, reduction='mean', label_smoothing=0.0) -> CrossEntropyLoss",
               "Cross entropy loss combining LogSoftmax and NLLLoss."))
        _a(_api("torch.nn", "MSELoss",
               "(size_average=None, reduce=None, reduction='mean') -> MSELoss",
               "Mean squared error loss."))
        _a(_api("torch.nn", "BCELoss",
               "(weight=None, size_average=None, reduce=None, reduction='mean') -> BCELoss",
               "Binary cross-entropy loss."))
        _a(_api("torch.nn", "BCEWithLogitsLoss",
               "(weight=None, size_average=None, reduce=None, reduction='mean', pos_weight=None) -> BCEWithLogitsLoss",
               "BCE loss with built-in sigmoid."))
        _a(_api("torch.nn", "L1Loss",
               "(size_average=None, reduce=None, reduction='mean') -> L1Loss",
               "Mean absolute error loss."))
        _a(_api("torch.nn", "SmoothL1Loss",
               "(size_average=None, reduce=None, reduction='mean', beta=1.0) -> SmoothL1Loss",
               "Smooth L1 (Huber) loss."))
        _a(_api("torch.nn", "NLLLoss",
               "(weight=None, size_average=None, ignore_index=-100, reduce=None, reduction='mean') -> NLLLoss",
               "Negative log likelihood loss."))
        _a(_api("torch.nn", "KLDivLoss",
               "(size_average=None, reduce=None, reduction='mean', log_target=False) -> KLDivLoss",
               "Kullback-Leibler divergence loss."))
        _a(_api("torch.nn", "TripletMarginLoss",
               "(margin: float = 1.0, p: float = 2.0, eps: float = 1e-06, swap: bool = False, size_average=None, reduce=None, reduction='mean') -> TripletMarginLoss",
               "Triplet margin loss."))
        _a(_api("torch.nn", "CosineEmbeddingLoss",
               "(margin: float = 0.0, size_average=None, reduce=None, reduction='mean') -> CosineEmbeddingLoss",
               "Cosine embedding loss."))

        # -- nn.functional ---------------------------------------------------
        _a(_api("torch.nn.functional", "softmax",
               "(input: Tensor, dim: int | None = None, _stacklevel=3, dtype=None) -> Tensor",
               "Apply softmax function.",
               structural=["result.shape == input.shape"],
               semantic=["all(0 <= result <= 1)", "result.sum(dim=dim) ≈ 1"]))
        _a(_api("torch.nn.functional", "log_softmax",
               "(input: Tensor, dim: int | None = None, _stacklevel=3, dtype=None) -> Tensor",
               "Apply log-softmax function.",
               structural=["result.shape == input.shape"]))
        _a(_api("torch.nn.functional", "relu",
               "(input: Tensor, inplace: bool = False) -> Tensor",
               "Apply rectified linear unit.",
               structural=["result.shape == input.shape"],
               semantic=["all(result >= 0)"]))
        _a(_api("torch.nn.functional", "gelu",
               "(input: Tensor, approximate: str = 'none') -> Tensor",
               "Apply Gaussian Error Linear Unit.",
               structural=["result.shape == input.shape"]))
        _a(_api("torch.nn.functional", "silu",
               "(input: Tensor, inplace: bool = False) -> Tensor",
               "Apply SiLU (Swish) activation.",
               structural=["result.shape == input.shape"], added_in="1.7"))
        _a(_api("torch.nn.functional", "leaky_relu",
               "(input: Tensor, negative_slope: float = 0.01, inplace: bool = False) -> Tensor",
               "Apply leaky ReLU.",
               structural=["result.shape == input.shape"]))
        _a(_api("torch.nn.functional", "sigmoid",
               "(input: Tensor) -> Tensor",
               "Apply sigmoid function.",
               structural=["result.shape == input.shape"],
               semantic=["all(0 <= result <= 1)"]))
        _a(_api("torch.nn.functional", "tanh",
               "(input: Tensor) -> Tensor",
               "Apply hyperbolic tangent.",
               structural=["result.shape == input.shape"]))
        _a(_api("torch.nn.functional", "cross_entropy",
               "(input: Tensor, target: Tensor, weight=None, size_average=None, ignore_index=-100, reduce=None, reduction='mean', label_smoothing=0.0) -> Tensor",
               "Compute cross entropy loss.",
               semantic=["result >= 0"]))
        _a(_api("torch.nn.functional", "mse_loss",
               "(input: Tensor, target: Tensor, size_average=None, reduce=None, reduction='mean') -> Tensor",
               "Compute mean squared error loss.",
               semantic=["result >= 0"]))
        _a(_api("torch.nn.functional", "binary_cross_entropy",
               "(input: Tensor, target: Tensor, weight=None, size_average=None, reduce=None, reduction='mean') -> Tensor",
               "Compute binary cross-entropy loss.",
               semantic=["result >= 0"]))
        _a(_api("torch.nn.functional", "l1_loss",
               "(input: Tensor, target: Tensor, size_average=None, reduce=None, reduction='mean') -> Tensor",
               "Compute mean absolute error loss.",
               semantic=["result >= 0"]))
        _a(_api("torch.nn.functional", "dropout",
               "(input: Tensor, p: float = 0.5, training: bool = True, inplace: bool = False) -> Tensor",
               "Apply dropout.",
               structural=["result.shape == input.shape"]))
        _a(_api("torch.nn.functional", "layer_norm",
               "(input: Tensor, normalized_shape, weight=None, bias=None, eps=1e-05) -> Tensor",
               "Apply layer normalisation.",
               structural=["result.shape == input.shape"]))
        _a(_api("torch.nn.functional", "batch_norm",
               "(input: Tensor, running_mean, running_var, weight=None, bias=None, training=False, momentum=0.1, eps=1e-05) -> Tensor",
               "Apply batch normalisation.",
               structural=["result.shape == input.shape"]))
        _a(_api("torch.nn.functional", "linear",
               "(input: Tensor, weight: Tensor, bias: Tensor | None = None) -> Tensor",
               "Apply a linear transformation.",
               structural=["input.shape[-1] == weight.shape[1]", "result.shape[-1] == weight.shape[0]"]))
        _a(_api("torch.nn.functional", "conv2d",
               "(input: Tensor, weight: Tensor, bias=None, stride=1, padding=0, dilation=1, groups=1) -> Tensor",
               "Apply a 2D convolution.",
               structural=["input.shape[1] == weight.shape[1] * groups"]))
        _a(_api("torch.nn.functional", "max_pool2d",
               "(input: Tensor, kernel_size, stride=None, padding=0, dilation=1, ceil_mode=False, return_indices=False) -> Tensor",
               "Apply 2D max pooling."))
        _a(_api("torch.nn.functional", "avg_pool2d",
               "(input: Tensor, kernel_size, stride=None, padding=0, ceil_mode=False, count_include_pad=True, divisor_override=None) -> Tensor",
               "Apply 2D average pooling."))
        _a(_api("torch.nn.functional", "interpolate",
               "(input: Tensor, size=None, scale_factor=None, mode='nearest', align_corners=None, recompute_scale_factor=None, antialias=False) -> Tensor",
               "Down/up sample input to given size or scale_factor."))
        _a(_api("torch.nn.functional", "pad",
               "(input: Tensor, pad, mode='constant', value=None) -> Tensor",
               "Pad tensor."))
        _a(_api("torch.nn.functional", "normalize",
               "(input: Tensor, p: float = 2.0, dim: int = 1, eps: float = 1e-12, out=None) -> Tensor",
               "Perform Lp normalisation over specified dimension.",
               structural=["result.shape == input.shape"]))
        _a(_api("torch.nn.functional", "one_hot",
               "(tensor: Tensor, num_classes: int = -1) -> Tensor",
               "Takes LongTensor of indices and returns one-hot encoding.",
               structural=["result.ndim == tensor.ndim + 1"],
               added_in="1.1"))
        _a(_api("torch.nn.functional", "embedding",
               "(input: Tensor, weight: Tensor, padding_idx=None, max_norm=None, norm_type=2.0, scale_grad_by_freq=False, sparse=False) -> Tensor",
               "Simple lookup table for embeddings.",
               structural=["result.shape == (*input.shape, weight.shape[1])"]))
        _a(_api("torch.nn.functional", "cosine_similarity",
               "(x1: Tensor, x2: Tensor, dim: int = 1, eps: float = 1e-8) -> Tensor",
               "Compute cosine similarity between samples.",
               semantic=["all(-1 <= result <= 1)"]))
        _a(_api("torch.nn.functional", "pairwise_distance",
               "(x1: Tensor, x2: Tensor, p: float = 2.0, eps: float = 1e-6, keepdim: bool = False) -> Tensor",
               "Compute pairwise distance.",
               semantic=["all(result >= 0)"]))

        # -- optimisers ------------------------------------------------------
        _a(_api("torch.optim", "SGD",
               "(params, lr=..., momentum=0, dampening=0, weight_decay=0, nesterov=False, ...) -> SGD",
               "Stochastic Gradient Descent optimiser."))
        _a(_api("torch.optim", "Adam",
               "(params, lr=0.001, betas=(0.9, 0.999), eps=1e-08, weight_decay=0, amsgrad=False, ...) -> Adam",
               "Adam optimiser."))
        _a(_api("torch.optim", "AdamW",
               "(params, lr=0.001, betas=(0.9, 0.999), eps=1e-08, weight_decay=0.01, amsgrad=False, ...) -> AdamW",
               "AdamW optimiser with decoupled weight decay."))
        _a(_api("torch.optim", "RMSprop",
               "(params, lr=0.01, alpha=0.99, eps=1e-08, weight_decay=0, momentum=0, centered=False) -> RMSprop",
               "RMSprop optimiser."))
        _a(_api("torch.optim", "Adagrad",
               "(params, lr=0.01, lr_decay=0, weight_decay=0, initial_accumulator_value=0, eps=1e-10) -> Adagrad",
               "Adagrad optimiser."))
        _a(_api("torch.optim.lr_scheduler", "StepLR",
               "(optimizer, step_size: int, gamma: float = 0.1, last_epoch: int = -1, verbose: bool = False) -> StepLR",
               "Decays the learning rate by gamma every step_size epochs."))
        _a(_api("torch.optim.lr_scheduler", "CosineAnnealingLR",
               "(optimizer, T_max: int, eta_min: float = 0, last_epoch: int = -1, verbose: bool = False) -> CosineAnnealingLR",
               "Cosine annealing learning rate scheduler."))
        _a(_api("torch.optim.lr_scheduler", "ReduceLROnPlateau",
               "(optimizer, mode='min', factor=0.1, patience=10, ...) -> ReduceLROnPlateau",
               "Reduce LR when a metric has stopped improving."))
        _a(_api("torch.optim.lr_scheduler", "OneCycleLR",
               "(optimizer, max_lr, total_steps=None, epochs=None, steps_per_epoch=None, ...) -> OneCycleLR",
               "OneCycle learning rate policy.", added_in="1.3"))

        # -- autograd --------------------------------------------------------
        _a(_api("torch.autograd", "grad",
               "(outputs, inputs, grad_outputs=None, retain_graph=None, create_graph=False, ...) -> tuple[Tensor, ...]",
               "Compute and return the sum of gradients of outputs w.r.t. inputs."))
        _a(_api("torch.autograd", "backward",
               "(tensors, grad_tensors=None, retain_graph=None, create_graph=False, ...) -> None",
               "Computes the sum of gradients of given tensors w.r.t. graph leaves."))
        _a(_api("torch", "no_grad",
               "() -> context_manager",
               "Context manager disabling gradient computation."))
        _a(_api("torch", "enable_grad",
               "() -> context_manager",
               "Context manager enabling gradient computation."))
        _a(_api("torch", "set_grad_enabled",
               "(mode: bool) -> context_manager",
               "Context manager setting gradient computation on or off."))

        # -- device / dtype --------------------------------------------------
        _a(_api("torch", "device",
               "(device: str | int) -> torch.device",
               "Represent a device on which a tensor is or will be allocated."))
        _a(_api("torch.Tensor", "to",
               "(self, device=None, dtype=None, ...) -> Tensor",
               "Move and/or cast the tensor.",
               structural=["result.shape == self.shape"]))
        _a(_api("torch.Tensor", "cpu",
               "(self, memory_format=torch.preserve_format) -> Tensor",
               "Return a copy on CPU.",
               structural=["result.shape == self.shape"]))
        _a(_api("torch.Tensor", "cuda",
               "(self, device=None, non_blocking=False, memory_format=torch.preserve_format) -> Tensor",
               "Return a copy on CUDA.",
               structural=["result.shape == self.shape"]))
        _a(_api("torch.Tensor", "numpy",
               "(self, *, force=False) -> numpy.ndarray",
               "Return the tensor as a NumPy ndarray.",
               structural=["result.shape == self.shape"]))
        _a(_api("torch.Tensor", "item",
               "(self) -> number",
               "Return the value of a scalar tensor.",
               structural=["self.numel() == 1"]))

        # -- serialisation ---------------------------------------------------
        _a(_api("torch", "save",
               "(obj, f, pickle_module=pickle, pickle_protocol=DEFAULT_PROTOCOL, _use_new_zipfile_serialization=True) -> None",
               "Save an object to a disk file."))
        _a(_api("torch", "load",
               "(f, map_location=None, pickle_module=pickle, *, weights_only=False, **pickle_load_args) -> Any",
               "Load an object saved with torch.save."))

        # -- utilities -------------------------------------------------------
        _a(_api("torch.nn.utils", "clip_grad_norm_",
               "(parameters, max_norm: float, norm_type: float = 2.0, error_if_nonfinite: bool = False, foreach=None) -> Tensor",
               "Clip the gradient norm of parameters."))
        _a(_api("torch.nn.utils", "clip_grad_value_",
               "(parameters, clip_value: float, foreach=None) -> None",
               "Clip the gradients of parameters."))
        _a(_api("torch.utils.data", "DataLoader",
               "(dataset, batch_size=1, shuffle=False, sampler=None, ...) -> DataLoader",
               "Data loader combining a dataset and a sampler."))
        _a(_api("torch.utils.data", "Dataset",
               "base class",
               "Abstract base class for datasets."))
        _a(_api("torch.utils.data", "TensorDataset",
               "(*tensors: Tensor) -> TensorDataset",
               "Dataset wrapping tensors."))
        _a(_api("torch.cuda", "is_available",
               "() -> bool",
               "Return whether CUDA is available."))
        _a(_api("torch.cuda", "device_count",
               "() -> int",
               "Return the number of GPUs available."))
        _a(_api("torch.cuda", "synchronize",
               "(device=None) -> None",
               "Wait for all kernels on the GPU to complete."))

        return entries

    # ── Type rules ─────────────────────────────────────────────────────────

    @staticmethod
    def _build_type_rules() -> List[TypeRule]:
        rules: List[TypeRule] = []
        _r = rules.append

        _r(TypeRule(
            name="zeros_shape",
            pattern="torch.zeros(*size) -> Tensor",
            postcondition="result.shape == size",
            lean_statement="axiom zeros_shape (s : Shape) : (torch.zeros s).shape = s",
        ))
        _r(TypeRule(
            name="ones_shape",
            pattern="torch.ones(*size) -> Tensor",
            postcondition="result.shape == size",
        ))
        _r(TypeRule(
            name="randn_shape",
            pattern="torch.randn(*size) -> Tensor",
            postcondition="result.shape == size",
        ))
        _r(TypeRule(
            name="view_prod_invariant",
            pattern="Tensor.view(*shape) -> Tensor",
            precondition="prod(self.shape) == prod(shape)",
            postcondition="result.shape == shape",
            lean_statement=(
                "axiom view_prod_invariant (t : Tensor s) (s' : Shape)\n"
                "  (h : prod s = prod s') : (t.view s').shape = s'"
            ),
        ))
        _r(TypeRule(
            name="reshape_prod_invariant",
            pattern="Tensor.reshape(*shape) -> Tensor",
            precondition="prod(self.shape) == prod(shape)",
            postcondition="result.shape == shape",
        ))
        _r(TypeRule(
            name="transpose_dims",
            pattern="Tensor.transpose(dim0, dim1) -> Tensor",
            postcondition="result.shape[dim0] == self.shape[dim1] and result.shape[dim1] == self.shape[dim0]",
        ))
        _r(TypeRule(
            name="permute_dims",
            pattern="Tensor.permute(*dims) -> Tensor",
            postcondition="result.shape == tuple(self.shape[d] for d in dims)",
        ))
        _r(TypeRule(
            name="unsqueeze_ndim",
            pattern="Tensor.unsqueeze(dim) -> Tensor",
            postcondition="result.ndim == self.ndim + 1 and result.shape[dim] == 1",
        ))
        _r(TypeRule(
            name="squeeze_removes_ones",
            pattern="Tensor.squeeze(dim) -> Tensor",
            postcondition="result.ndim <= self.ndim",
        ))
        _r(TypeRule(
            name="flatten_preserves_numel",
            pattern="Tensor.flatten(start_dim, end_dim) -> Tensor",
            postcondition="result.numel() == self.numel()",
        ))
        _r(TypeRule(
            name="cat_dim_sum",
            pattern="torch.cat(tensors, dim) -> Tensor",
            precondition="all shapes match except along dim",
            postcondition="result.shape[dim] == sum(t.shape[dim] for t in tensors)",
        ))
        _r(TypeRule(
            name="stack_new_dim",
            pattern="torch.stack(tensors, dim) -> Tensor",
            precondition="all tensors have the same shape",
            postcondition="result.ndim == tensors[0].ndim + 1",
        ))
        _r(TypeRule(
            name="matmul_shape",
            pattern="torch.matmul(a, b) -> Tensor",
            precondition="a.shape[-1] == b.shape[-2]",
            postcondition="result.shape[-2:] == (a.shape[-2], b.shape[-1])",
            lean_statement=(
                "axiom matmul_shape (a : Tensor [m, k]) (b : Tensor [k, n]) :\n"
                "  (torch.matmul a b).shape = [m, n]"
            ),
        ))
        _r(TypeRule(
            name="mm_2d",
            pattern="torch.mm(a, b) -> Tensor",
            precondition="a.ndim == 2 and b.ndim == 2 and a.shape[1] == b.shape[0]",
            postcondition="result.shape == (a.shape[0], b.shape[1])",
        ))
        _r(TypeRule(
            name="bmm_3d",
            pattern="torch.bmm(a, b) -> Tensor",
            precondition="a.ndim == 3 and b.ndim == 3 and a.shape[0] == b.shape[0] and a.shape[2] == b.shape[1]",
            postcondition="result.shape == (a.shape[0], a.shape[1], b.shape[2])",
        ))
        _r(TypeRule(
            name="linear_shape",
            pattern="nn.Linear(in_f, out_f)(input) -> Tensor",
            precondition="input.shape[-1] == in_f",
            postcondition="result.shape == (*input.shape[:-1], out_f)",
            lean_statement=(
                "axiom linear_shape (in_f out_f : Nat) (x : Tensor [..., in_f]) :\n"
                "  (nn.Linear in_f out_f x).shape = [..., out_f]"
            ),
        ))
        _r(TypeRule(
            name="conv2d_channels",
            pattern="nn.Conv2d(c_in, c_out, k)(input) -> Tensor",
            precondition="input.shape[1] == c_in",
            postcondition="result.shape[1] == c_out",
        ))
        _r(TypeRule(
            name="batchnorm_preserves_shape",
            pattern="nn.BatchNorm2d(num_features)(input) -> Tensor",
            postcondition="result.shape == input.shape",
        ))
        _r(TypeRule(
            name="layernorm_preserves_shape",
            pattern="nn.LayerNorm(normalized_shape)(input) -> Tensor",
            postcondition="result.shape == input.shape",
        ))
        _r(TypeRule(
            name="dropout_preserves_shape",
            pattern="nn.Dropout(p)(input) -> Tensor",
            postcondition="result.shape == input.shape",
        ))
        _r(TypeRule(
            name="relu_preserves_shape",
            pattern="nn.ReLU()(input) -> Tensor",
            postcondition="result.shape == input.shape",
        ))
        _r(TypeRule(
            name="gelu_preserves_shape",
            pattern="nn.GELU()(input) -> Tensor",
            postcondition="result.shape == input.shape",
        ))
        _r(TypeRule(
            name="softmax_preserves_shape",
            pattern="F.softmax(input, dim) -> Tensor",
            postcondition="result.shape == input.shape",
            lean_statement=(
                "axiom softmax_preserves_shape (x : Tensor s) (d : Nat) :\n"
                "  (F.softmax x d).shape = s"
            ),
        ))
        _r(TypeRule(
            name="softmax_sums_to_one",
            pattern="F.softmax(input, dim) -> Tensor",
            postcondition="result.sum(dim=dim) ≈ 1",
        ))
        _r(TypeRule(
            name="softmax_nonneg",
            pattern="F.softmax(input, dim) -> Tensor",
            postcondition="all(result >= 0) and all(result <= 1)",
        ))
        _r(TypeRule(
            name="sigmoid_range",
            pattern="torch.sigmoid(input) -> Tensor",
            postcondition="all(0 <= result <= 1)",
        ))
        _r(TypeRule(
            name="embedding_shape",
            pattern="nn.Embedding(num_emb, emb_dim)(indices) -> Tensor",
            postcondition="result.shape == (*indices.shape, emb_dim)",
        ))
        _r(TypeRule(
            name="multihead_attention_divisibility",
            pattern="nn.MultiheadAttention(embed_dim, num_heads)",
            precondition="embed_dim % num_heads == 0",
        ))
        _r(TypeRule(
            name="cross_entropy_nonneg",
            pattern="F.cross_entropy(input, target) -> Tensor",
            postcondition="result >= 0",
        ))
        _r(TypeRule(
            name="mse_loss_nonneg",
            pattern="F.mse_loss(input, target) -> Tensor",
            postcondition="result >= 0",
        ))
        _r(TypeRule(
            name="norm_nonneg",
            pattern="torch.norm(input) -> Tensor",
            postcondition="result >= 0",
        ))
        _r(TypeRule(
            name="abs_nonneg",
            pattern="torch.abs(input) -> Tensor",
            postcondition="all(result >= 0)",
        ))
        _r(TypeRule(
            name="exp_positive",
            pattern="torch.exp(input) -> Tensor",
            postcondition="all(result > 0)",
        ))
        _r(TypeRule(
            name="clone_preserves_shape",
            pattern="Tensor.clone() -> Tensor",
            postcondition="result.shape == self.shape",
        ))
        _r(TypeRule(
            name="to_preserves_shape",
            pattern="Tensor.to(device) -> Tensor",
            postcondition="result.shape == self.shape",
        ))
        _r(TypeRule(
            name="cumsum_preserves_shape",
            pattern="torch.cumsum(input, dim) -> Tensor",
            postcondition="result.shape == input.shape",
        ))
        _r(TypeRule(
            name="sort_preserves_shape",
            pattern="torch.sort(input, dim) -> Tensor",
            postcondition="result.values.shape == input.shape",
        ))
        _r(TypeRule(
            name="narrow_dim_length",
            pattern="Tensor.narrow(dim, start, length) -> Tensor",
            postcondition="result.shape[dim] == length",
        ))
        _r(TypeRule(
            name="expand_ndim",
            pattern="Tensor.expand(*sizes) -> Tensor",
            postcondition="result.ndim == len(sizes)",
        ))
        _r(TypeRule(
            name="t_2d_transpose",
            pattern="Tensor.t() -> Tensor",
            precondition="self.ndim == 2",
            postcondition="result.shape == (self.shape[1], self.shape[0])",
        ))
        _r(TypeRule(
            name="one_hot_shape",
            pattern="F.one_hot(tensor, num_classes) -> Tensor",
            postcondition="result.shape == (*tensor.shape, num_classes)",
        ))
        _r(TypeRule(
            name="normalize_preserves_shape",
            pattern="F.normalize(input, p, dim) -> Tensor",
            postcondition="result.shape == input.shape",
        ))

        return rules

    # ── Axioms ─────────────────────────────────────────────────────────────

    @staticmethod
    def _build_axioms() -> List[Axiom]:
        axioms: List[Axiom] = []
        _x = axioms.append

        _x(Axiom(
            name="view_view_compose",
            statement="t.view(s1).view(s2) == t.view(s2) when prod(t.shape) == prod(s1) == prod(s2)",
            lean_statement=(
                "axiom view_view_compose (t : Tensor s) (s1 s2 : Shape)\n"
                "  (h1 : prod s = prod s1) (h2 : prod s1 = prod s2) :\n"
                "  (t.view s1).view s2 = t.view s2"
            ),
            trust_level="tested",
            source="PyTorch property test",
        ))
        _x(Axiom(
            name="transpose_involution",
            statement="t.transpose(d0, d1).transpose(d0, d1) == t",
            lean_statement=(
                "axiom transpose_involution (t : Tensor s) (d0 d1 : Nat) :\n"
                "  (t.transpose d0 d1).transpose d0 d1 = t"
            ),
            trust_level="tested",
            source="PyTorch property test",
        ))
        _x(Axiom(
            name="matmul_associative",
            statement="matmul(matmul(a, b), c) == matmul(a, matmul(b, c))",
            lean_statement=(
                "axiom matmul_associative (a : Tensor [m, k]) (b : Tensor [k, l]) (c : Tensor [l, n]) :\n"
                "  torch.matmul (torch.matmul a b) c = torch.matmul a (torch.matmul b c)"
            ),
            trust_level="assumed",
            source="Linear algebra",
        ))
        _x(Axiom(
            name="identity_matmul",
            statement="matmul(eye(n), t) == t  for t.shape[0] == n",
            trust_level="tested",
            source="PyTorch property test",
        ))
        _x(Axiom(
            name="softmax_sums_to_one",
            statement="F.softmax(x, dim).sum(dim=dim) ≈ 1",
            lean_statement=(
                "axiom softmax_sums_to_one (x : Tensor s) (d : Nat) :\n"
                "  (F.softmax x d).sum d = 1"
            ),
            trust_level="tested",
            source="PyTorch property test",
        ))
        _x(Axiom(
            name="softmax_nonneg",
            statement="all(F.softmax(x, dim) >= 0)",
            trust_level="tested",
            source="PyTorch property test",
        ))
        _x(Axiom(
            name="relu_idempotent",
            statement="relu(relu(x)) == relu(x)",
            lean_statement=(
                "axiom relu_idempotent (x : Tensor s) :\n"
                "  F.relu (F.relu x) = F.relu x"
            ),
            trust_level="tested",
            source="PyTorch property test",
        ))
        _x(Axiom(
            name="sigmoid_bounded",
            statement="0 <= sigmoid(x) <= 1 for all x",
            trust_level="tested",
            source="PyTorch property test",
        ))
        _x(Axiom(
            name="zeros_add_identity",
            statement="t + torch.zeros_like(t) == t",
            lean_statement="axiom zeros_add_identity (t : Tensor s) : t + torch.zeros_like t = t",
            trust_level="tested",
            source="PyTorch property test",
        ))
        _x(Axiom(
            name="ones_mul_identity",
            statement="t * torch.ones_like(t) == t",
            trust_level="tested",
            source="PyTorch property test",
        ))
        _x(Axiom(
            name="cat_split_roundtrip",
            statement="torch.cat(torch.split(t, sizes, dim), dim) == t",
            trust_level="tested",
            source="PyTorch property test",
        ))
        _x(Axiom(
            name="clone_equality",
            statement="t.clone() == t and t.clone() is not t",
            trust_level="tested",
            source="PyTorch property test",
        ))
        _x(Axiom(
            name="detach_data_equality",
            statement="t.detach().data_ptr() == t.data_ptr() (shares storage)",
            trust_level="tested",
            source="PyTorch property test",
        ))
        _x(Axiom(
            name="contiguous_preserves_values",
            statement="t.contiguous() == t",
            trust_level="tested",
            source="PyTorch property test",
        ))
        _x(Axiom(
            name="exp_log_inverse",
            statement="torch.log(torch.exp(x)) ≈ x  (for finite x)",
            lean_statement=(
                "axiom exp_log_inverse (x : Tensor s) :\n"
                "  torch.log (torch.exp x) = x"
            ),
            trust_level="assumed",
            source="Calculus",
        ))
        _x(Axiom(
            name="norm_nonneg",
            statement="torch.norm(t) >= 0",
            lean_statement="axiom norm_nonneg (t : Tensor s) : torch.norm t ≥ 0",
            trust_level="verified",
            source="Linear algebra",
        ))
        _x(Axiom(
            name="cross_entropy_nonneg",
            statement="F.cross_entropy(input, target) >= 0",
            trust_level="tested",
            source="Information theory",
        ))
        _x(Axiom(
            name="mse_nonneg",
            statement="F.mse_loss(input, target) >= 0",
            trust_level="tested",
            source="Definition of MSE",
        ))
        _x(Axiom(
            name="squeeze_unsqueeze_roundtrip",
            statement="t.unsqueeze(dim).squeeze(dim) == t",
            trust_level="tested",
            source="PyTorch property test",
        ))
        _x(Axiom(
            name="to_device_preserves_values",
            statement="t.to(device).to(original_device) == t",
            trust_level="tested",
            source="PyTorch property test",
        ))
        _x(Axiom(
            name="sort_idempotent",
            statement="torch.sort(torch.sort(t, dim).values, dim).values == torch.sort(t, dim).values",
            trust_level="tested",
            source="PyTorch property test",
        ))
        _x(Axiom(
            name="dropout_identity_eval",
            statement="nn.Dropout(p)(x) == x  when model.eval()",
            trust_level="tested",
            source="PyTorch docs",
        ))
        _x(Axiom(
            name="batchnorm_preserves_shape",
            statement="nn.BatchNorm2d(c)(x).shape == x.shape",
            trust_level="tested",
            source="PyTorch docs",
        ))

        return axioms
