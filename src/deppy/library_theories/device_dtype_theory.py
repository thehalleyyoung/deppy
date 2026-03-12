"""Theory Family 8: Device & Dtype Compatibility.

Table-driven device (cpu/cuda/mps) and dtype (float32/float64/int64/etc.)
compatibility checking.
Forward: propagate device/dtype through operations.
Backward: require compatible device/dtype.
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
# Device and Dtype enumerations
# ═══════════════════════════════════════════════════════════════════════════════


class Device(Enum):
    CPU = "cpu"
    CUDA = "cuda"
    CUDA_0 = "cuda:0"
    CUDA_1 = "cuda:1"
    MPS = "mps"
    XPU = "xpu"
    META = "meta"

    @property
    def base_device(self) -> str:
        return self.value.split(":")[0]

    def is_same_device_family(self, other: Device) -> bool:
        return self.base_device == other.base_device


class Dtype(Enum):
    FLOAT16 = "float16"
    BFLOAT16 = "bfloat16"
    FLOAT32 = "float32"
    FLOAT64 = "float64"
    INT8 = "int8"
    INT16 = "int16"
    INT32 = "int32"
    INT64 = "int64"
    UINT8 = "uint8"
    BOOL = "bool"
    COMPLEX64 = "complex64"
    COMPLEX128 = "complex128"

    @property
    def is_floating(self) -> bool:
        return self in (Dtype.FLOAT16, Dtype.BFLOAT16, Dtype.FLOAT32, Dtype.FLOAT64)

    @property
    def is_integer(self) -> bool:
        return self in (Dtype.INT8, Dtype.INT16, Dtype.INT32, Dtype.INT64, Dtype.UINT8)

    @property
    def is_complex(self) -> bool:
        return self in (Dtype.COMPLEX64, Dtype.COMPLEX128)

    @property
    def is_bool(self) -> bool:
        return self == Dtype.BOOL

    @property
    def element_size(self) -> int:
        _sizes = {
            Dtype.BOOL: 1, Dtype.INT8: 1, Dtype.UINT8: 1,
            Dtype.FLOAT16: 2, Dtype.BFLOAT16: 2, Dtype.INT16: 2,
            Dtype.FLOAT32: 4, Dtype.INT32: 4,
            Dtype.FLOAT64: 8, Dtype.INT64: 8, Dtype.COMPLEX64: 8,
            Dtype.COMPLEX128: 16,
        }
        return _sizes.get(self, 4)


# ═══════════════════════════════════════════════════════════════════════════════
# Dtype promotion table
# ═══════════════════════════════════════════════════════════════════════════════

_DTYPE_PROMOTION_ORDER = {
    Dtype.BOOL: 0,
    Dtype.UINT8: 1, Dtype.INT8: 2, Dtype.INT16: 3, Dtype.INT32: 4, Dtype.INT64: 5,
    Dtype.FLOAT16: 6, Dtype.BFLOAT16: 7, Dtype.FLOAT32: 8, Dtype.FLOAT64: 9,
    Dtype.COMPLEX64: 10, Dtype.COMPLEX128: 11,
}

_DTYPE_PROMOTION: Dict[Tuple[Dtype, Dtype], Dtype] = {}

def _init_promotion_table() -> None:
    pairs = [
        (Dtype.BOOL, Dtype.INT8, Dtype.INT8),
        (Dtype.BOOL, Dtype.INT16, Dtype.INT16),
        (Dtype.BOOL, Dtype.INT32, Dtype.INT32),
        (Dtype.BOOL, Dtype.INT64, Dtype.INT64),
        (Dtype.BOOL, Dtype.FLOAT16, Dtype.FLOAT16),
        (Dtype.BOOL, Dtype.FLOAT32, Dtype.FLOAT32),
        (Dtype.BOOL, Dtype.FLOAT64, Dtype.FLOAT64),
        (Dtype.INT8, Dtype.INT16, Dtype.INT16),
        (Dtype.INT8, Dtype.INT32, Dtype.INT32),
        (Dtype.INT8, Dtype.INT64, Dtype.INT64),
        (Dtype.INT8, Dtype.FLOAT16, Dtype.FLOAT16),
        (Dtype.INT8, Dtype.FLOAT32, Dtype.FLOAT32),
        (Dtype.INT8, Dtype.FLOAT64, Dtype.FLOAT64),
        (Dtype.INT16, Dtype.INT32, Dtype.INT32),
        (Dtype.INT16, Dtype.INT64, Dtype.INT64),
        (Dtype.INT16, Dtype.FLOAT32, Dtype.FLOAT32),
        (Dtype.INT16, Dtype.FLOAT64, Dtype.FLOAT64),
        (Dtype.INT32, Dtype.INT64, Dtype.INT64),
        (Dtype.INT32, Dtype.FLOAT32, Dtype.FLOAT64),
        (Dtype.INT32, Dtype.FLOAT64, Dtype.FLOAT64),
        (Dtype.INT64, Dtype.FLOAT32, Dtype.FLOAT64),
        (Dtype.INT64, Dtype.FLOAT64, Dtype.FLOAT64),
        (Dtype.FLOAT16, Dtype.FLOAT32, Dtype.FLOAT32),
        (Dtype.FLOAT16, Dtype.FLOAT64, Dtype.FLOAT64),
        (Dtype.BFLOAT16, Dtype.FLOAT32, Dtype.FLOAT32),
        (Dtype.BFLOAT16, Dtype.FLOAT64, Dtype.FLOAT64),
        (Dtype.FLOAT32, Dtype.FLOAT64, Dtype.FLOAT64),
        (Dtype.FLOAT32, Dtype.COMPLEX64, Dtype.COMPLEX64),
        (Dtype.FLOAT64, Dtype.COMPLEX128, Dtype.COMPLEX128),
        (Dtype.COMPLEX64, Dtype.COMPLEX128, Dtype.COMPLEX128),
        (Dtype.UINT8, Dtype.INT8, Dtype.INT16),
        (Dtype.UINT8, Dtype.INT16, Dtype.INT16),
        (Dtype.UINT8, Dtype.INT32, Dtype.INT32),
        (Dtype.UINT8, Dtype.INT64, Dtype.INT64),
        (Dtype.UINT8, Dtype.FLOAT16, Dtype.FLOAT16),
        (Dtype.UINT8, Dtype.FLOAT32, Dtype.FLOAT32),
        (Dtype.UINT8, Dtype.FLOAT64, Dtype.FLOAT64),
    ]
    for a, b, result in pairs:
        _DTYPE_PROMOTION[(a, b)] = result
        _DTYPE_PROMOTION[(b, a)] = result
    for d in Dtype:
        _DTYPE_PROMOTION[(d, d)] = d

_init_promotion_table()


def promote_dtypes(a: Dtype, b: Dtype) -> Optional[Dtype]:
    """Get the promoted dtype from combining two dtypes."""
    return _DTYPE_PROMOTION.get((a, b))


def parse_dtype(s: str) -> Optional[Dtype]:
    """Parse a string to a Dtype enum."""
    s = s.lower().replace("torch.", "").replace("np.", "").replace("numpy.", "")
    for d in Dtype:
        if d.value == s:
            return d
    aliases = {
        "float": Dtype.FLOAT32, "double": Dtype.FLOAT64,
        "half": Dtype.FLOAT16, "int": Dtype.INT32,
        "long": Dtype.INT64, "short": Dtype.INT16,
        "byte": Dtype.UINT8, "char": Dtype.INT8,
        "cfloat": Dtype.COMPLEX64, "cdouble": Dtype.COMPLEX128,
    }
    return aliases.get(s)


def parse_device(s: str) -> Optional[Device]:
    """Parse a string to a Device enum."""
    s = s.lower()
    for d in Device:
        if d.value == s:
            return d
    if s.startswith("cuda") and ":" not in s:
        return Device.CUDA
    return None


# ═══════════════════════════════════════════════════════════════════════════════
# Compatibility checking
# ═══════════════════════════════════════════════════════════════════════════════


def devices_compatible(a: Device, b: Device) -> bool:
    """Check if two tensors on these devices can be combined."""
    if a == b:
        return True
    if a.base_device == b.base_device:
        return True
    return False


def dtypes_compatible_for_op(a: Dtype, b: Dtype, op: str = "arithmetic") -> bool:
    """Check if two dtypes can be combined for a given operation."""
    if op in ("matmul", "mm", "bmm"):
        return a.is_floating == b.is_floating or a.is_complex == b.is_complex
    promoted = promote_dtypes(a, b)
    return promoted is not None


_OP_REQUIRES_FLOAT: Set[str] = {
    "softmax", "log_softmax", "sigmoid", "tanh", "sin", "cos",
    "exp", "log", "sqrt", "norm", "normalize", "dropout",
    "batch_norm", "layer_norm", "group_norm",
    "conv1d", "conv2d", "conv3d", "linear",
    "cross_entropy", "nll_loss", "mse_loss",
}


def op_requires_float(op_name: str) -> bool:
    """Check if an operation requires floating-point dtype."""
    return op_name.lower() in _OP_REQUIRES_FLOAT


@dataclass(frozen=True)
class DeviceDtypeInfo:
    """Device and dtype information for a tensor."""
    device: Optional[Device] = None
    dtype: Optional[Dtype] = None

    def to_refinements(self) -> Dict[str, Any]:
        refs: Dict[str, Any] = {}
        if self.device is not None:
            refs["device"] = self.device.value
        if self.dtype is not None:
            refs["dtype"] = self.dtype.value
        return refs

    @staticmethod
    def from_refinements(refs: Dict[str, Any]) -> DeviceDtypeInfo:
        dev_str = refs.get("device")
        dtype_str = refs.get("dtype")
        device = parse_device(str(dev_str)) if dev_str else None
        dtype = parse_dtype(str(dtype_str)) if dtype_str else None
        return DeviceDtypeInfo(device=device, dtype=dtype)


# ═══════════════════════════════════════════════════════════════════════════════
# DeviceDtypeTheoryPack
# ═══════════════════════════════════════════════════════════════════════════════


class DeviceDtypeTheoryPack(TheoryPackBase):
    """Theory Family 8: Device & Dtype Compatibility.

    Table-driven device and dtype propagation and checking.
    """

    pack_name = "device_dtype"
    pack_priority = 28

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
        info = DeviceDtypeInfo.from_refinements(refs)

        op_name = refs.get("operation") or refs.get("tensor_op")
        if op_name is not None:
            op_name = str(op_name)
            if op_requires_float(op_name) and info.dtype is not None:
                if not info.dtype.is_floating and not info.dtype.is_complex:
                    return SolverResult(
                        status=SolverStatus.UNSATISFIABLE,
                        section=section,
                        explanation=f"{op_name} requires floating dtype, got {info.dtype.value}",
                    )

        second_info = DeviceDtypeInfo.from_refinements(
            refs.get("_second_operand", {})
        )

        if info.device is not None and second_info.device is not None:
            if not devices_compatible(info.device, second_info.device):
                return SolverResult(
                    status=SolverStatus.UNSATISFIABLE,
                    section=section,
                    explanation=(
                        f"device mismatch: {info.device.value} vs "
                        f"{second_info.device.value}"
                    ),
                )

        result_dtype = info.dtype
        if info.dtype is not None and second_info.dtype is not None:
            promoted = promote_dtypes(info.dtype, second_info.dtype)
            if promoted is None:
                return SolverResult(
                    status=SolverStatus.UNSATISFIABLE,
                    section=section,
                    explanation=(
                        f"dtype incompatible: {info.dtype.value} vs "
                        f"{second_info.dtype.value}"
                    ),
                )
            result_dtype = promoted

        result_device = info.device or second_info.device

        cast_target = refs.get("cast_dtype")
        if cast_target is not None:
            parsed = parse_dtype(str(cast_target))
            if parsed is not None:
                result_dtype = parsed

        to_device = refs.get("to_device")
        if to_device is not None:
            parsed_dev = parse_device(str(to_device))
            if parsed_dev is not None:
                result_device = parsed_dev

        result_info = DeviceDtypeInfo(device=result_device, dtype=result_dtype)
        new_refs = dict(refs)
        new_refs.update(result_info.to_refinements())
        new_refs["_device_dtype_resolved"] = True

        return SolverResult(
            status=SolverStatus.SOLVED,
            section=LocalSection(
                site_id=section.site_id,
                carrier_type=section.carrier_type,
                refinements=new_refs,
                trust=TrustLevel.BOUNDED_AUTO,
                provenance=f"device_dtype: {result_info}",
                witnesses=dict(section.witnesses),
            ),
            explanation=f"device={result_device}, dtype={result_dtype}",
        )

    def forward_refine(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        restricted = morphism.restrict(section)
        info = DeviceDtypeInfo.from_refinements(section.refinements)

        if morphism.metadata:
            cast = morphism.metadata.get("cast_dtype")
            if cast is not None:
                parsed = parse_dtype(str(cast))
                if parsed is not None:
                    info = DeviceDtypeInfo(device=info.device, dtype=parsed)

            to_dev = morphism.metadata.get("to_device")
            if to_dev is not None:
                parsed_dev = parse_device(str(to_dev))
                if parsed_dev is not None:
                    info = DeviceDtypeInfo(device=parsed_dev, dtype=info.dtype)

        new_refs = merge_refinements(restricted.refinements, info.to_refinements(), "meet")
        return LocalSection(
            site_id=restricted.site_id,
            carrier_type=restricted.carrier_type,
            refinements=new_refs,
            trust=restricted.trust,
            provenance="device_dtype forward",
            witnesses=dict(restricted.witnesses),
        )

    def backward_pullback(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        refs = section.refinements
        required_refs: Dict[str, Any] = {}

        target_device = refs.get("device")
        target_dtype = refs.get("dtype")

        if target_device is not None:
            required_refs["device"] = target_device
        if target_dtype is not None:
            op_name = refs.get("operation")
            if op_name and op_requires_float(str(op_name)):
                required_refs["_requires_floating_dtype"] = True
            else:
                required_refs["dtype"] = target_dtype

        return LocalSection(
            site_id=morphism.source,
            carrier_type=section.carrier_type,
            refinements=required_refs,
            trust=TrustLevel.RESIDUAL,
            provenance="device_dtype pullback",
        )

    def viability_predicate(self, error_site: SiteId) -> str:
        name = error_site.name
        if "device" in name.lower():
            return "all tensors on the same device"
        if "dtype" in name.lower():
            return "dtypes are compatible (promotable)"
        return f"device/dtype compatible at {name}"

    def classify_proof_boundary(self, section: LocalSection) -> BoundaryClassification:
        refs = section.refinements
        if refs.get("_device_dtype_resolved"):
            return BoundaryClassification.FULLY_PROVEN
        info = DeviceDtypeInfo.from_refinements(refs)
        if info.device is not None and info.dtype is not None:
            return BoundaryClassification.CONDITIONALLY_PROVEN
        return BoundaryClassification.ASSUMED
