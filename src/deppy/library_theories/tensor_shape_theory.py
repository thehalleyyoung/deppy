"""Theory Family 5: Tensor Shape Theory.

Handles reshape, view, broadcast, matmul, and convolution shape constraints.
Forward: compute output shapes from input shapes.
Backward: infer required input shapes from output requirements.
"""

from __future__ import annotations

import math
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

from deppy.core._protocols import (
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism

from .theory_pack_base import (
    BoundaryClassification,
    SolverResult,
    SolverStatus,
    TheoryPackBase,
    merge_refinements,
)

Dim = Union[int, str]
Shape = Tuple[Dim, ...]


# ═══════════════════════════════════════════════════════════════════════════════
# Shape representation
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ShapeInfo:
    """Shape information for a tensor."""
    shape: Optional[Shape] = None
    ndim: Optional[int] = None
    numel: Optional[int] = None
    batch_dims: int = 0

    @property
    def is_known(self) -> bool:
        return self.shape is not None

    @property
    def is_fully_concrete(self) -> bool:
        if self.shape is None:
            return False
        return all(isinstance(d, int) for d in self.shape)

    def concrete_numel(self) -> Optional[int]:
        if not self.is_fully_concrete or self.shape is None:
            return None
        result = 1
        for d in self.shape:
            if isinstance(d, int):
                result *= d
            else:
                return None
        return result

    def to_refinements(self) -> Dict[str, Any]:
        refs: Dict[str, Any] = {}
        if self.shape is not None:
            refs["shape"] = self.shape
            refs["ndim"] = len(self.shape)
        elif self.ndim is not None:
            refs["ndim"] = self.ndim
        if self.numel is not None:
            refs["numel"] = self.numel
        if self.batch_dims > 0:
            refs["batch_dims"] = self.batch_dims
        return refs

    @staticmethod
    def from_refinements(refs: Dict[str, Any]) -> ShapeInfo:
        shape = refs.get("shape")
        if shape is not None and isinstance(shape, (tuple, list)):
            shape = tuple(shape)
        ndim = refs.get("ndim")
        numel = refs.get("numel")
        batch_dims = refs.get("batch_dims", 0)
        return ShapeInfo(shape, ndim, numel, batch_dims)


# ═══════════════════════════════════════════════════════════════════════════════
# Shape operations
# ═══════════════════════════════════════════════════════════════════════════════


def broadcast_shapes(a: Shape, b: Shape) -> Optional[Shape]:
    """Compute the broadcast result shape, or None if incompatible."""
    result: List[Dim] = []
    la, lb = len(a), len(b)
    max_len = max(la, lb)
    padded_a: List[Dim] = [1] * (max_len - la) + list(a)
    padded_b: List[Dim] = [1] * (max_len - lb) + list(b)
    for da, db in zip(padded_a, padded_b):
        if isinstance(da, int) and isinstance(db, int):
            if da == db:
                result.append(da)
            elif da == 1:
                result.append(db)
            elif db == 1:
                result.append(da)
            else:
                return None
        elif isinstance(da, int) and da == 1:
            result.append(db)
        elif isinstance(db, int) and db == 1:
            result.append(da)
        elif isinstance(da, str) and isinstance(db, str):
            if da == db:
                result.append(da)
            else:
                result.append(f"broadcast({da},{db})")
        else:
            result.append(da if isinstance(da, str) else db)
    return tuple(result)


def matmul_shapes(a: Shape, b: Shape) -> Optional[Shape]:
    """Compute the matmul result shape."""
    if len(a) == 0 or len(b) == 0:
        return None
    if len(a) == 1 and len(b) == 1:
        if _dims_compatible(a[0], b[0]):
            return ()
        return None
    if len(a) == 1 and len(b) == 2:
        if _dims_compatible(a[0], b[0]):
            return (b[1],)
        return None
    if len(a) == 2 and len(b) == 1:
        if _dims_compatible(a[1], b[0]):
            return (a[0],)
        return None
    if len(a) >= 2 and len(b) >= 2:
        if not _dims_compatible(a[-1], b[-2]):
            return None
        batch_a = a[:-2]
        batch_b = b[:-2]
        batch = broadcast_shapes(batch_a, batch_b)
        if batch is None and (batch_a or batch_b):
            return None
        if batch is None:
            batch = ()
        return batch + (a[-2], b[-1])
    return None


def reshape_shape(
    input_shape: Shape, target_shape: Shape
) -> Optional[Shape]:
    """Validate and resolve a reshape operation."""
    input_numel = _compute_numel(input_shape)
    neg_one_count = sum(1 for d in target_shape if isinstance(d, int) and d == -1)
    if neg_one_count > 1:
        return None
    if neg_one_count == 1 and input_numel is not None:
        known_product = 1
        for d in target_shape:
            if isinstance(d, int) and d != -1:
                known_product *= d
        if known_product == 0:
            return None
        inferred = input_numel // known_product
        result = tuple(inferred if (isinstance(d, int) and d == -1) else d for d in target_shape)
        return result
    if neg_one_count == 0:
        target_numel = _compute_numel(target_shape)
        if input_numel is not None and target_numel is not None:
            if input_numel != target_numel:
                return None
        return target_shape
    return target_shape


def conv2d_output_shape(
    input_shape: Shape,
    kernel_size: Tuple[int, int],
    stride: Tuple[int, int] = (1, 1),
    padding: Tuple[int, int] = (0, 0),
    dilation: Tuple[int, int] = (1, 1),
    out_channels: Optional[int] = None,
) -> Optional[Shape]:
    """Compute Conv2d output shape."""
    if len(input_shape) != 4:
        return None
    batch, in_c, in_h, in_w = input_shape
    if not all(isinstance(d, int) for d in (in_h, in_w)):
        h_out: Dim = "H_out"
        w_out: Dim = "W_out"
    else:
        h_out = (int(in_h) + 2 * padding[0] - dilation[0] * (kernel_size[0] - 1) - 1) // stride[0] + 1
        w_out = (int(in_w) + 2 * padding[1] - dilation[1] * (kernel_size[1] - 1) - 1) // stride[1] + 1
    oc: Dim = out_channels if out_channels is not None else "C_out"
    return (batch, oc, h_out, w_out)


def transpose_shape(shape: Shape, dim0: int, dim1: int) -> Optional[Shape]:
    """Compute shape after transposing two dimensions."""
    ndim = len(shape)
    if dim0 < 0:
        dim0 += ndim
    if dim1 < 0:
        dim1 += ndim
    if dim0 < 0 or dim0 >= ndim or dim1 < 0 or dim1 >= ndim:
        return None
    lst = list(shape)
    lst[dim0], lst[dim1] = lst[dim1], lst[dim0]
    return tuple(lst)


def permute_shape(shape: Shape, dims: Tuple[int, ...]) -> Optional[Shape]:
    """Compute shape after permutation."""
    if len(dims) != len(shape):
        return None
    if set(dims) != set(range(len(shape))):
        return None
    return tuple(shape[d] for d in dims)


def cat_shapes(shapes: List[Shape], dim: int = 0) -> Optional[Shape]:
    """Compute shape after concatenation along a dimension."""
    if not shapes:
        return None
    ndim = len(shapes[0])
    if dim < 0:
        dim += ndim
    if dim < 0 or dim >= ndim:
        return None
    for s in shapes[1:]:
        if len(s) != ndim:
            return None
        for i in range(ndim):
            if i != dim and not _dims_compatible(shapes[0][i], s[i]):
                return None
    cat_dim: Dim = 0
    all_int = True
    for s in shapes:
        if isinstance(s[dim], int):
            cat_dim = int(cat_dim) + int(s[dim]) if isinstance(cat_dim, int) else cat_dim
        else:
            all_int = False
    if not all_int:
        cat_dim = f"cat_dim({dim})"
    result = list(shapes[0])
    result[dim] = cat_dim
    return tuple(result)


def _dims_compatible(a: Dim, b: Dim) -> bool:
    if isinstance(a, int) and isinstance(b, int):
        return a == b
    return True


def _compute_numel(shape: Shape) -> Optional[int]:
    result = 1
    for d in shape:
        if isinstance(d, int):
            result *= d
        else:
            return None
    return result


# ═══════════════════════════════════════════════════════════════════════════════
# Shape operation dispatch
# ═══════════════════════════════════════════════════════════════════════════════


_SHAPE_OPS: Dict[str, Any] = {
    "reshape": reshape_shape,
    "view": reshape_shape,
    "matmul": matmul_shapes,
    "broadcast": broadcast_shapes,
}


def dispatch_shape_op(
    op_name: str,
    input_shapes: List[Shape],
    params: Optional[Dict[str, Any]] = None,
) -> Optional[Shape]:
    """Dispatch a shape operation to the appropriate handler."""
    params = params or {}
    if op_name in ("reshape", "view") and len(input_shapes) >= 1:
        target = params.get("target_shape")
        if target is not None:
            return reshape_shape(input_shapes[0], tuple(target))
    elif op_name == "matmul" and len(input_shapes) >= 2:
        return matmul_shapes(input_shapes[0], input_shapes[1])
    elif op_name in ("add", "sub", "mul", "div") and len(input_shapes) >= 2:
        return broadcast_shapes(input_shapes[0], input_shapes[1])
    elif op_name == "transpose" and len(input_shapes) >= 1:
        dim0 = params.get("dim0", 0)
        dim1 = params.get("dim1", 1)
        return transpose_shape(input_shapes[0], dim0, dim1)
    elif op_name == "permute" and len(input_shapes) >= 1:
        dims = params.get("dims")
        if dims is not None:
            return permute_shape(input_shapes[0], tuple(dims))
    elif op_name == "cat" and input_shapes:
        dim = params.get("dim", 0)
        return cat_shapes(input_shapes, dim)
    elif op_name == "conv2d" and len(input_shapes) >= 1:
        kernel = params.get("kernel_size", (3, 3))
        stride = params.get("stride", (1, 1))
        padding = params.get("padding", (0, 0))
        dilation = params.get("dilation", (1, 1))
        out_c = params.get("out_channels")
        return conv2d_output_shape(
            input_shapes[0], kernel, stride, padding, dilation, out_c
        )
    elif op_name == "unsqueeze" and len(input_shapes) >= 1:
        dim = params.get("dim", 0)
        s = list(input_shapes[0])
        ndim = len(s)
        if dim < 0:
            dim += ndim + 1
        if 0 <= dim <= ndim:
            s.insert(dim, 1)
            return tuple(s)
    elif op_name == "squeeze" and len(input_shapes) >= 1:
        dim = params.get("dim")
        s = list(input_shapes[0])
        if dim is not None:
            ndim = len(s)
            if dim < 0:
                dim += ndim
            if 0 <= dim < ndim and isinstance(s[dim], int) and s[dim] == 1:
                s.pop(dim)
        else:
            s = [d for d in s if not (isinstance(d, int) and d == 1)]
        return tuple(s)
    elif op_name == "flatten" and len(input_shapes) >= 1:
        start = params.get("start_dim", 0)
        end = params.get("end_dim", -1)
        s = list(input_shapes[0])
        ndim = len(s)
        if start < 0:
            start += ndim
        if end < 0:
            end += ndim
        flat_dims = s[start:end + 1]
        flat_product = _compute_numel(tuple(flat_dims))
        if flat_product is not None:
            result = s[:start] + [flat_product] + s[end + 1:]
        else:
            result = s[:start] + ["flat"] + s[end + 1:]
        return tuple(result)
    return None


# ═══════════════════════════════════════════════════════════════════════════════
# TensorShapeTheoryPack
# ═══════════════════════════════════════════════════════════════════════════════


class TensorShapeTheoryPack(TheoryPackBase):
    """Theory Family 5: Tensor Shape Theory.

    Handles TENSOR_SHAPE sites for shape constraint propagation.
    """

    pack_name = "tensor_shape"
    pack_priority = 25

    _APPLICABLE = frozenset({
        SiteKind.TENSOR_SHAPE,
        SiteKind.SSA_VALUE,
        SiteKind.CALL_RESULT,
        SiteKind.ERROR,
    })

    def applicable_site_kinds(self) -> FrozenSet[SiteKind]:
        return self._APPLICABLE

    def solve_local(self, site: SiteId, section: LocalSection) -> SolverResult:
        """Resolve tensor shape constraints."""
        refs = section.refinements
        info = ShapeInfo.from_refinements(refs)

        op_name = refs.get("shape_op")
        if op_name is not None:
            input_shapes_raw = refs.get("input_shapes", [])
            input_shapes = []
            for s in input_shapes_raw:
                if isinstance(s, (tuple, list)):
                    input_shapes.append(tuple(s))
            params = refs.get("shape_params", {})
            result_shape = dispatch_shape_op(str(op_name), input_shapes, params)

            if result_shape is not None:
                new_info = ShapeInfo(
                    shape=result_shape,
                    ndim=len(result_shape),
                    numel=_compute_numel(result_shape),
                )
                new_refs = dict(refs)
                new_refs.update(new_info.to_refinements())
                new_refs["_shape_resolved"] = True

                return SolverResult(
                    status=SolverStatus.SOLVED,
                    section=LocalSection(
                        site_id=section.site_id,
                        carrier_type=section.carrier_type,
                        refinements=new_refs,
                        trust=TrustLevel.BOUNDED_AUTO,
                        provenance=f"shape: {op_name} -> {result_shape}",
                        witnesses=dict(section.witnesses),
                    ),
                    explanation=f"{op_name}: {input_shapes} -> {result_shape}",
                )
            else:
                return SolverResult(
                    status=SolverStatus.REFINED,
                    section=section,
                    constraints_remaining=[f"shape op {op_name} failed"],
                    explanation=f"shape op {op_name} incompatible",
                )

        if info.is_known:
            new_refs = dict(refs)
            new_refs.update(info.to_refinements())
            return SolverResult(
                status=SolverStatus.REFINED,
                section=LocalSection(
                    site_id=section.site_id,
                    carrier_type=section.carrier_type,
                    refinements=new_refs,
                    trust=section.trust,
                    provenance=f"shape info: {info.shape}",
                    witnesses=dict(section.witnesses),
                ),
                explanation=f"shape: {info.shape}",
            )

        return SolverResult(
            status=SolverStatus.UNCHANGED,
            section=section,
            explanation="no shape information to resolve",
        )

    def forward_refine(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        """Propagate shape information forward through operations."""
        restricted = morphism.restrict(section)
        info = ShapeInfo.from_refinements(section.refinements)

        if not info.is_known:
            return restricted

        op_name = None
        params: Dict[str, Any] = {}
        if morphism.metadata:
            op_name = morphism.metadata.get("shape_op")
            params = morphism.metadata.get("shape_params", {})

        if op_name is not None and info.shape is not None:
            second_shape = morphism.metadata.get("second_shape") if morphism.metadata else None
            input_shapes = [info.shape]
            if second_shape is not None:
                input_shapes.append(tuple(second_shape))
            result = dispatch_shape_op(op_name, input_shapes, params)
            if result is not None:
                new_info = ShapeInfo(shape=result, ndim=len(result))
                new_refs = merge_refinements(
                    restricted.refinements, new_info.to_refinements(), "meet"
                )
                return LocalSection(
                    site_id=restricted.site_id,
                    carrier_type=restricted.carrier_type,
                    refinements=new_refs,
                    trust=restricted.trust,
                    provenance=f"shape forward: {op_name} -> {result}",
                    witnesses=dict(restricted.witnesses),
                )

        shape_refs = info.to_refinements()
        new_refs = merge_refinements(restricted.refinements, shape_refs, "meet")
        return LocalSection(
            site_id=restricted.site_id,
            carrier_type=restricted.carrier_type,
            refinements=new_refs,
            trust=restricted.trust,
            provenance="shape forward: propagated",
            witnesses=dict(restricted.witnesses),
        )

    def backward_pullback(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        """Infer required input shapes from output requirements."""
        refs = section.refinements
        required_shape = refs.get("shape")
        required_ndim = refs.get("ndim")

        required_refs: Dict[str, Any] = {}

        op_name = None
        if morphism.metadata:
            op_name = morphism.metadata.get("shape_op")

        if op_name == "matmul" and required_shape is not None and len(required_shape) >= 2:
            required_refs["_requires_shape_compatible_matmul"] = True
            required_refs["ndim_min"] = 2

        elif op_name in ("reshape", "view") and required_shape is not None:
            numel = _compute_numel(tuple(required_shape))
            if numel is not None:
                required_refs["numel"] = numel

        elif op_name == "conv2d":
            required_refs["ndim"] = 4

        if required_ndim is not None:
            required_refs["ndim"] = required_ndim

        return LocalSection(
            site_id=morphism.source,
            carrier_type=section.carrier_type,
            refinements=required_refs,
            trust=TrustLevel.RESIDUAL,
            provenance=f"shape pullback: requires {required_refs}",
        )

    def viability_predicate(self, error_site: SiteId) -> str:
        name = error_site.name
        if "reshape" in name.lower() or "view" in name.lower():
            return "input numel == target numel"
        if "matmul" in name.lower() or "mm" in name.lower():
            return "a.shape[-1] == b.shape[-2]"
        if "broadcast" in name.lower():
            return "shapes are broadcast-compatible"
        if "conv" in name.lower():
            return "input has 4 dims (N, C, H, W) and channels match"
        return f"tensor shapes compatible at {name}"

    def classify_proof_boundary(self, section: LocalSection) -> BoundaryClassification:
        refs = section.refinements
        if refs.get("_shape_resolved"):
            return BoundaryClassification.FULLY_PROVEN
        info = ShapeInfo.from_refinements(refs)
        if info.is_fully_concrete:
            return BoundaryClassification.CONDITIONALLY_PROVEN
        if info.is_known:
            return BoundaryClassification.CONDITIONALLY_PROVEN
        if section.trust == TrustLevel.ASSUMED:
            return BoundaryClassification.ASSUMED
        return BoundaryClassification.REQUIRES_PROOF
