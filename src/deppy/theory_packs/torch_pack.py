from __future__ import annotations

from typing import Any, Tuple

from deppy.core._protocols import SiteKind

from .models import AxiomSpec, TheoryPackSpec, VerificationCase


TORCH_AXIOMS: Tuple[AxiomSpec, ...] = (
    AxiomSpec(
        name="matmul-shape",
        library="torch",
        version_range=">=2.0",
        site_kinds=(SiteKind.TENSOR_SHAPE, SiteKind.CALL_RESULT),
        rewrite_rule="matmul follows matrix multiplication shape rules",
        solver_formula="shape(A @ B) = (m, n) when A=(m,k), B=(k,n)",
        delegate_pack_names=("torch_shape", "tensor_shape"),
        verification_cases=(
            VerificationCase(
                name="matmul-2x3-by-3x4",
                operation="matmul",
                payload={"left_shape": (2, 3), "right_shape": (3, 4)},
                expected={"shape": (2, 4)},
            ),
        ),
    ),
    AxiomSpec(
        name="broadcast-add-shape",
        library="torch",
        version_range=">=2.0",
        site_kinds=(SiteKind.TENSOR_SHAPE, SiteKind.CALL_RESULT),
        rewrite_rule="torch broadcasting follows NumPy-compatible semantics",
        solver_formula="shape(a + b) = broadcast(shape(a), shape(b))",
        delegate_pack_names=("torch_shape", "tensor_shape"),
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
        library="torch",
        version_range=">=2.0",
        site_kinds=(SiteKind.CALL_RESULT, SiteKind.SSA_VALUE),
        rewrite_rule="binary tensor arithmetic promotes dtypes",
        solver_formula="dtype(a + b) = promote(dtype(a), dtype(b))",
        delegate_pack_names=("device_dtype",),
        verification_cases=(
            VerificationCase(
                name="int32-plus-float32",
                operation="dtype_promotion",
                payload={"left_dtype": "int32", "right_dtype": "float32"},
                expected={"dtype": "torch.float32"},
            ),
        ),
    ),
)


def build_torch_pack_spec() -> TheoryPackSpec:
    return TheoryPackSpec(
        name="torch",
        library="torch",
        version_range=">=2.0",
        site_kinds=(SiteKind.TENSOR_SHAPE, SiteKind.TENSOR_INDEXING, SiteKind.CALL_RESULT, SiteKind.SSA_VALUE),
        delegate_pack_names=("torch_shape", "tensor_shape", "tensor_indexing", "device_dtype"),
        axioms=TORCH_AXIOMS,
        description="Torch-oriented facade over existing tensor, indexing, and dtype packs plus the PyTorch shape pack.",
    )


def verify_torch_axiom_case(axiom: AxiomSpec, case: VerificationCase, module: Any) -> tuple[bool, str]:
    torch = module
    if case.operation == "matmul":
        left = torch.zeros(tuple(case.payload["left_shape"]))
        right = torch.zeros(tuple(case.payload["right_shape"]))
        result = left @ right
        return tuple(result.shape) == tuple(case.expected["shape"]), f"observed shape={tuple(result.shape)}"
    if case.operation == "broadcast_add":
        left = torch.zeros(tuple(case.payload["left_shape"]))
        right = torch.zeros(tuple(case.payload["right_shape"]))
        result = left + right
        return tuple(result.shape) == tuple(case.expected["shape"]), f"observed shape={tuple(result.shape)}"
    if case.operation == "dtype_promotion":
        left = torch.zeros((1,), dtype=getattr(torch, str(case.payload["left_dtype"])))
        right = torch.zeros((1,), dtype=getattr(torch, str(case.payload["right_dtype"])))
        result = left + right
        return str(result.dtype) == str(case.expected["dtype"]), f"observed dtype={result.dtype}"
    raise ValueError(f"unsupported torch verification operation: {case.operation}")
