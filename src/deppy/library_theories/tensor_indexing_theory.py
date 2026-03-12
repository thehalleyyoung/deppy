"""Theory Family 7: Tensor Indexing Theory.

Handles gather, index_select, subscript, advanced indexing, and bounds.
Forward: propagate index validity.
Backward: require in-bounds indices.
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


# ═══════════════════════════════════════════════════════════════════════════════
# Indexing mode
# ═══════════════════════════════════════════════════════════════════════════════


class IndexMode(Enum):
    """How a tensor is being indexed."""
    SCALAR = "scalar"
    SLICE = "slice"
    BOOLEAN_MASK = "boolean_mask"
    INTEGER_ARRAY = "integer_array"
    GATHER = "gather"
    INDEX_SELECT = "index_select"
    SCATTER = "scatter"
    ADVANCED = "advanced"
    ELLIPSIS = "ellipsis"


@dataclass(frozen=True)
class IndexBound:
    """Bounds information for an index into a dimension."""
    dim: int
    dim_size: Optional[int] = None
    index_min: Optional[int] = None
    index_max: Optional[int] = None
    index_mode: IndexMode = IndexMode.SCALAR

    @property
    def is_known_valid(self) -> bool:
        if self.dim_size is None or self.index_min is None or self.index_max is None:
            return False
        effective_min = self.index_min if self.index_min >= 0 else self.index_min + self.dim_size
        effective_max = self.index_max if self.index_max >= 0 else self.index_max + self.dim_size
        return 0 <= effective_min and effective_max < self.dim_size

    @property
    def is_known_invalid(self) -> bool:
        if self.dim_size is None:
            return False
        if self.index_min is not None and self.index_min >= self.dim_size:
            return True
        if self.index_max is not None and self.index_max < -self.dim_size:
            return True
        return False


@dataclass(frozen=True)
class SliceBound:
    """Bounds for a slice index."""
    dim: int
    dim_size: Optional[int] = None
    start: Optional[int] = None
    stop: Optional[int] = None
    step: Optional[int] = None

    def effective_range(self) -> Optional[Tuple[int, int, int]]:
        if self.dim_size is None:
            return None
        s = self.start if self.start is not None else 0
        e = self.stop if self.stop is not None else self.dim_size
        st = self.step if self.step is not None else 1
        if s < 0:
            s += self.dim_size
        if e < 0:
            e += self.dim_size
        s = max(0, min(s, self.dim_size))
        e = max(0, min(e, self.dim_size))
        return (s, e, st)

    def output_size(self) -> Optional[int]:
        rng = self.effective_range()
        if rng is None:
            return None
        s, e, st = rng
        if st == 0:
            return None
        if st > 0:
            return max(0, (e - s + st - 1) // st)
        else:
            return max(0, (s - e - st - 1) // (-st))


@dataclass
class IndexingInfo:
    """Complete indexing information for a tensor access."""
    mode: IndexMode = IndexMode.SCALAR
    bounds: List[IndexBound] = field(default_factory=list)
    slice_bounds: List[SliceBound] = field(default_factory=list)
    tensor_shape: Optional[Tuple[Any, ...]] = None
    gather_dim: Optional[int] = None
    index_tensor_shape: Optional[Tuple[Any, ...]] = None
    boolean_mask_count: Optional[int] = None

    @property
    def all_bounds_valid(self) -> bool:
        return all(b.is_known_valid for b in self.bounds)

    @property
    def any_bound_invalid(self) -> bool:
        return any(b.is_known_invalid for b in self.bounds)

    def to_refinements(self) -> Dict[str, Any]:
        refs: Dict[str, Any] = {"index_mode": self.mode.value}
        if self.tensor_shape is not None:
            refs["indexed_shape"] = self.tensor_shape
        if self.bounds:
            refs["index_bounds"] = [
                {"dim": b.dim, "dim_size": b.dim_size,
                 "min": b.index_min, "max": b.index_max}
                for b in self.bounds
            ]
        if self.slice_bounds:
            refs["slice_bounds"] = [
                {"dim": sb.dim, "dim_size": sb.dim_size,
                 "start": sb.start, "stop": sb.stop, "step": sb.step}
                for sb in self.slice_bounds
            ]
        refs["all_indices_valid"] = self.all_bounds_valid
        if self.gather_dim is not None:
            refs["gather_dim"] = self.gather_dim
        if self.index_tensor_shape is not None:
            refs["index_tensor_shape"] = self.index_tensor_shape
        return refs

    @staticmethod
    def from_refinements(refs: Dict[str, Any]) -> IndexingInfo:
        mode_str = refs.get("index_mode", "scalar")
        try:
            mode = IndexMode(mode_str)
        except ValueError:
            mode = IndexMode.SCALAR
        tensor_shape = refs.get("indexed_shape")
        if tensor_shape is not None:
            tensor_shape = tuple(tensor_shape)
        bounds_raw = refs.get("index_bounds", [])
        bounds = []
        for b in bounds_raw:
            if isinstance(b, dict):
                bounds.append(IndexBound(
                    dim=b.get("dim", 0),
                    dim_size=b.get("dim_size"),
                    index_min=b.get("min"),
                    index_max=b.get("max"),
                ))
        slice_bounds_raw = refs.get("slice_bounds", [])
        slice_bounds = []
        for sb in slice_bounds_raw:
            if isinstance(sb, dict):
                slice_bounds.append(SliceBound(
                    dim=sb.get("dim", 0),
                    dim_size=sb.get("dim_size"),
                    start=sb.get("start"),
                    stop=sb.get("stop"),
                    step=sb.get("step"),
                ))
        return IndexingInfo(
            mode=mode, bounds=bounds, slice_bounds=slice_bounds,
            tensor_shape=tensor_shape,
            gather_dim=refs.get("gather_dim"),
            index_tensor_shape=refs.get("index_tensor_shape"),
            boolean_mask_count=refs.get("boolean_mask_count"),
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Index output shape computation
# ═══════════════════════════════════════════════════════════════════════════════


def scalar_index_output_shape(
    input_shape: Tuple[Any, ...], dim: int
) -> Optional[Tuple[Any, ...]]:
    ndim = len(input_shape)
    if dim < 0:
        dim += ndim
    if dim < 0 or dim >= ndim:
        return None
    return input_shape[:dim] + input_shape[dim + 1:]


def slice_index_output_shape(
    input_shape: Tuple[Any, ...],
    dim: int,
    slice_bound: SliceBound,
) -> Optional[Tuple[Any, ...]]:
    ndim = len(input_shape)
    if dim < 0:
        dim += ndim
    if dim < 0 or dim >= ndim:
        return None
    out_size = slice_bound.output_size()
    if out_size is not None:
        return input_shape[:dim] + (out_size,) + input_shape[dim + 1:]
    return input_shape[:dim] + ("slice",) + input_shape[dim + 1:]


def gather_output_shape(
    input_shape: Tuple[Any, ...],
    index_shape: Tuple[Any, ...],
    dim: int,
) -> Optional[Tuple[Any, ...]]:
    return index_shape


def index_select_output_shape(
    input_shape: Tuple[Any, ...],
    dim: int,
    num_indices: Optional[int] = None,
) -> Optional[Tuple[Any, ...]]:
    ndim = len(input_shape)
    if dim < 0:
        dim += ndim
    if dim < 0 or dim >= ndim:
        return None
    if num_indices is not None:
        return input_shape[:dim] + (num_indices,) + input_shape[dim + 1:]
    return input_shape[:dim] + ("K",) + input_shape[dim + 1:]


def boolean_mask_output_shape(
    input_shape: Tuple[Any, ...],
    mask_true_count: Optional[int] = None,
) -> Optional[Tuple[Any, ...]]:
    if mask_true_count is not None:
        return (mask_true_count,)
    return ("N_selected",)


# ═══════════════════════════════════════════════════════════════════════════════
# TensorIndexingTheoryPack
# ═══════════════════════════════════════════════════════════════════════════════


class TensorIndexingTheoryPack(TheoryPackBase):
    """Theory Family 7: Tensor Indexing Theory.

    Handles TENSOR_INDEXING sites for index bounds checking.
    """

    pack_name = "tensor_indexing"
    pack_priority = 30

    _APPLICABLE = frozenset({
        SiteKind.TENSOR_INDEXING,
        SiteKind.SSA_VALUE,
        SiteKind.CALL_RESULT,
        SiteKind.ERROR,
    })

    def applicable_site_kinds(self) -> FrozenSet[SiteKind]:
        return self._APPLICABLE

    def solve_local(self, site: SiteId, section: LocalSection) -> SolverResult:
        refs = section.refinements
        info = IndexingInfo.from_refinements(refs)

        if info.any_bound_invalid:
            return SolverResult(
                status=SolverStatus.UNSATISFIABLE,
                section=section,
                explanation="index is provably out of bounds",
            )

        if info.all_bounds_valid:
            new_refs = dict(refs)
            new_refs.update(info.to_refinements())
            new_refs["_index_safe"] = True
            return SolverResult(
                status=SolverStatus.SOLVED,
                section=LocalSection(
                    site_id=section.site_id,
                    carrier_type=section.carrier_type,
                    refinements=new_refs,
                    trust=TrustLevel.BOUNDED_AUTO,
                    provenance="indexing: all bounds verified",
                    witnesses=dict(section.witnesses),
                ),
                explanation="all index bounds verified",
            )

        if info.tensor_shape is not None and info.bounds:
            refined_bounds = self._refine_bounds(info)
            new_info = IndexingInfo(
                mode=info.mode, bounds=refined_bounds,
                slice_bounds=info.slice_bounds,
                tensor_shape=info.tensor_shape,
                gather_dim=info.gather_dim,
                index_tensor_shape=info.index_tensor_shape,
            )
            new_refs = dict(refs)
            new_refs.update(new_info.to_refinements())

            remaining = []
            for b in refined_bounds:
                if not b.is_known_valid:
                    remaining.append(
                        f"index at dim {b.dim}: "
                        f"[{b.index_min}, {b.index_max}] vs size {b.dim_size}"
                    )

            return SolverResult(
                status=SolverStatus.REFINED,
                section=LocalSection(
                    site_id=section.site_id,
                    carrier_type=section.carrier_type,
                    refinements=new_refs,
                    trust=section.trust,
                    provenance="indexing: partial bounds refinement",
                    witnesses=dict(section.witnesses),
                ),
                constraints_remaining=remaining,
                explanation=f"refined {len(refined_bounds)} index bounds",
            )

        return SolverResult(
            status=SolverStatus.UNCHANGED,
            section=section,
            explanation="no indexing information to resolve",
        )

    def forward_refine(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        restricted = morphism.restrict(section)
        info = IndexingInfo.from_refinements(section.refinements)

        if info.tensor_shape is None:
            return restricted

        op_name = None
        if morphism.metadata:
            op_name = morphism.metadata.get("index_op")

        output_shape: Optional[Tuple[Any, ...]] = None
        if op_name == "scalar_index":
            dim = morphism.metadata.get("dim", 0) if morphism.metadata else 0
            output_shape = scalar_index_output_shape(info.tensor_shape, dim)
        elif op_name == "slice":
            dim = morphism.metadata.get("dim", 0) if morphism.metadata else 0
            sb_data = morphism.metadata.get("slice_bound", {}) if morphism.metadata else {}
            sb = SliceBound(
                dim=dim,
                dim_size=info.tensor_shape[dim] if dim < len(info.tensor_shape) and isinstance(info.tensor_shape[dim], int) else None,
                start=sb_data.get("start"), stop=sb_data.get("stop"),
                step=sb_data.get("step"),
            )
            output_shape = slice_index_output_shape(info.tensor_shape, dim, sb)
        elif op_name == "gather":
            dim = morphism.metadata.get("dim", 0) if morphism.metadata else 0
            idx_shape = morphism.metadata.get("index_shape") if morphism.metadata else None
            if idx_shape is not None:
                output_shape = gather_output_shape(info.tensor_shape, tuple(idx_shape), dim)
        elif op_name == "index_select":
            dim = morphism.metadata.get("dim", 0) if morphism.metadata else 0
            n_idx = morphism.metadata.get("num_indices") if morphism.metadata else None
            output_shape = index_select_output_shape(info.tensor_shape, dim, n_idx)
        elif op_name == "boolean_mask":
            count = morphism.metadata.get("true_count") if morphism.metadata else None
            result = boolean_mask_output_shape(info.tensor_shape, count)
            if result is not None:
                output_shape = result

        new_refs = dict(restricted.refinements)
        if output_shape is not None:
            new_refs["shape"] = output_shape
            new_refs["ndim"] = len(output_shape)
        if info.all_bounds_valid:
            new_refs["_index_safe"] = True

        return LocalSection(
            site_id=restricted.site_id,
            carrier_type=restricted.carrier_type,
            refinements=new_refs,
            trust=restricted.trust,
            provenance=f"indexing forward: {op_name}",
            witnesses=dict(restricted.witnesses),
        )

    def backward_pullback(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        refs = section.refinements
        required_refs: Dict[str, Any] = {}

        dim = refs.get("indexed_dim", 0)
        idx_min = refs.get("index_min")
        idx_max = refs.get("index_max")

        if idx_min is not None or idx_max is not None:
            required_refs["_requires_dim_size"] = dim
            if idx_max is not None:
                required_refs[f"dim_{dim}_min_size"] = int(idx_max) + 1

        if refs.get("_index_safe") is None:
            required_refs["_requires_bounds_check"] = True

        return LocalSection(
            site_id=morphism.source,
            carrier_type=section.carrier_type,
            refinements=required_refs,
            trust=TrustLevel.RESIDUAL,
            provenance="indexing pullback: bounds requirements",
        )

    def viability_predicate(self, error_site: SiteId) -> str:
        name = error_site.name
        if "gather" in name.lower():
            return "all indices in [0, dim_size) for gather"
        if "select" in name.lower():
            return "index in [0, dim_size) for index_select"
        return f"0 <= index < tensor.size(dim) at {name}"

    def classify_proof_boundary(self, section: LocalSection) -> BoundaryClassification:
        refs = section.refinements
        if refs.get("_index_safe"):
            return BoundaryClassification.FULLY_PROVEN
        info = IndexingInfo.from_refinements(refs)
        if info.all_bounds_valid:
            return BoundaryClassification.FULLY_PROVEN
        if info.bounds:
            return BoundaryClassification.CONDITIONALLY_PROVEN
        return BoundaryClassification.REQUIRES_PROOF

    # ── Internal helpers ──────────────────────────────────────────────────

    def _refine_bounds(self, info: IndexingInfo) -> List[IndexBound]:
        """Refine index bounds using known tensor shape."""
        refined = []
        for b in info.bounds:
            dim_size = b.dim_size
            if dim_size is None and info.tensor_shape is not None:
                dim = b.dim
                if dim < 0 and info.tensor_shape:
                    dim += len(info.tensor_shape)
                if 0 <= dim < len(info.tensor_shape):
                    ds = info.tensor_shape[dim]
                    if isinstance(ds, int):
                        dim_size = ds
            refined.append(IndexBound(
                dim=b.dim, dim_size=dim_size,
                index_min=b.index_min, index_max=b.index_max,
                index_mode=b.index_mode,
            ))
        return refined
