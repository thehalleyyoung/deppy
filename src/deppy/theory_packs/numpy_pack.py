from __future__ import annotations

from typing import Any, Tuple

from deppy.core._protocols import SiteKind

from .models import AxiomSpec, TheoryPackSpec, VerificationCase


NUMPY_AXIOMS: Tuple[AxiomSpec, ...] = (
    AxiomSpec(
        name="reshape-preserves-numel",
        library="numpy",
        version_range=">=1.20",
        site_kinds=(SiteKind.TENSOR_SHAPE, SiteKind.CALL_RESULT, SiteKind.SSA_VALUE),
        rewrite_rule="np.reshape(a, shape) preserves total element count",
        solver_formula="numel(result) = numel(a)",
        delegate_pack_names=("tensor_shape", "tensor_indexing"),
        verification_cases=(
            VerificationCase(
                name="reshape-2x3-to-3x2",
                operation="reshape",
                payload={"data": [[1, 2, 3], [4, 5, 6]], "shape": (3, 2)},
                expected={"shape": (3, 2), "size": 6},
            ),
        ),
    ),
    AxiomSpec(
        name="broadcast-add-shape",
        library="numpy",
        version_range=">=1.20",
        site_kinds=(SiteKind.TENSOR_SHAPE, SiteKind.CALL_RESULT),
        rewrite_rule="numpy broadcasting computes join-compatible shape",
        solver_formula="shape(a + b) = broadcast(shape(a), shape(b))",
        delegate_pack_names=("tensor_shape",),
        verification_cases=(
            VerificationCase(
                name="broadcast-2x1-plus-1x3",
                operation="broadcast_add",
                payload={"left_shape": (2, 1), "right_shape": (1, 3)},
                expected={"shape": (2, 3)},
            ),
        ),
    ),
    AxiomSpec(
        name="dtype-promotion",
        library="numpy",
        version_range=">=1.20",
        site_kinds=(SiteKind.CALL_RESULT, SiteKind.SSA_VALUE),
        rewrite_rule="numpy result_type follows dtype promotion lattice",
        solver_formula="dtype(result) = promote(dtype(a), dtype(b))",
        delegate_pack_names=("device_dtype",),
        verification_cases=(
            VerificationCase(
                name="int32-plus-float64",
                operation="dtype_promotion",
                payload={"left": "int32", "right": "float64"},
                expected={"dtype": "float64"},
            ),
        ),
    ),
)


def build_numpy_pack_spec() -> TheoryPackSpec:
    return TheoryPackSpec(
        name="numpy",
        library="numpy",
        version_range=">=1.20",
        site_kinds=(SiteKind.TENSOR_SHAPE, SiteKind.TENSOR_INDEXING, SiteKind.CALL_RESULT, SiteKind.SSA_VALUE),
        delegate_pack_names=("tensor_shape", "tensor_indexing", "device_dtype"),
        axioms=NUMPY_AXIOMS,
        description="NumPy-oriented facade over the existing tensor, indexing, and dtype theory packs.",
    )


def verify_numpy_axiom_case(axiom: AxiomSpec, case: VerificationCase, module: Any) -> tuple[bool, str]:
    np = module
    if case.operation == "reshape":
        array = np.array(case.payload["data"])
        result = array.reshape(tuple(case.payload["shape"]))
        expected_shape = tuple(case.expected["shape"])
        expected_size = int(case.expected["size"])
        return result.shape == expected_shape and int(result.size) == expected_size, f"observed shape={tuple(result.shape)} size={int(result.size)}"
    if case.operation == "broadcast_add":
        left = np.zeros(tuple(case.payload["left_shape"]))
        right = np.zeros(tuple(case.payload["right_shape"]))
        result = left + right
        expected_shape = tuple(case.expected["shape"])
        return tuple(result.shape) == expected_shape, f"observed shape={tuple(result.shape)}"
    if case.operation == "dtype_promotion":
        promoted = np.result_type(np.dtype(case.payload["left"]), np.dtype(case.payload["right"]))
        return str(promoted) == str(case.expected["dtype"]), f"observed dtype={promoted}"
    raise ValueError(f"unsupported numpy verification operation: {case.operation}")
