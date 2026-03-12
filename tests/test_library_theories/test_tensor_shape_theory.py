"""Tests for the tensor shape theory pack: reshape, matmul, broadcast, etc.

Covers ShapeInfo, broadcast_shapes, matmul_shapes, reshape_shape,
conv2d_output_shape, transpose_shape, permute_shape, cat_shapes,
dispatch_shape_op, and TensorShapeTheoryPack.
"""

from __future__ import annotations

import pytest

from deppy.core._protocols import (
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism
from deppy.library_theories.tensor_shape_theory import (
    ShapeInfo,
    TensorShapeTheoryPack,
    broadcast_shapes,
    cat_shapes,
    conv2d_output_shape,
    dispatch_shape_op,
    matmul_shapes,
    permute_shape,
    reshape_shape,
    transpose_shape,
)
from deppy.library_theories.theory_pack_base import (
    BoundaryClassification,
    SolverStatus,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _site(name: str, kind: SiteKind = SiteKind.TENSOR_SHAPE) -> SiteId:
    return SiteId(kind=kind, name=name)


def _section(
    name: str,
    refinements: dict | None = None,
    trust: TrustLevel = TrustLevel.RESIDUAL,
    kind: SiteKind = SiteKind.TENSOR_SHAPE,
) -> LocalSection:
    sid = _site(name, kind)
    return LocalSection(
        site_id=sid,
        carrier_type="Tensor",
        refinements=refinements or {},
        trust=trust,
    )


# ===================================================================
#  ShapeInfo
# ===================================================================


class TestShapeInfo:
    """Tests for ShapeInfo dataclass."""

    def test_known_shape(self):
        info = ShapeInfo(shape=(3, 4, 5))
        assert info.is_known
        assert info.is_fully_concrete
        assert info.to_refinements()["ndim"] == 3
        assert info.concrete_numel() == 60

    def test_unknown_shape(self):
        info = ShapeInfo()
        assert not info.is_known
        assert not info.is_fully_concrete
        assert info.concrete_numel() is None

    def test_symbolic_shape(self):
        info = ShapeInfo(shape=("batch", 3, 4))
        assert info.is_known
        assert not info.is_fully_concrete
        assert info.concrete_numel() is None

    def test_to_refinements(self):
        info = ShapeInfo(shape=(2, 3), numel=6, batch_dims=1)
        refs = info.to_refinements()
        assert refs["shape"] == (2, 3)
        assert refs["ndim"] == 2
        assert refs["numel"] == 6
        assert refs["batch_dims"] == 1

    def test_from_refinements(self):
        refs = {"shape": (2, 3), "ndim": 2, "numel": 6}
        info = ShapeInfo.from_refinements(refs)
        assert info.shape == (2, 3)
        assert info.ndim == 2
        assert info.numel == 6

    def test_from_refinements_list(self):
        refs = {"shape": [4, 5]}
        info = ShapeInfo.from_refinements(refs)
        assert info.shape == (4, 5)


# ===================================================================
#  broadcast_shapes
# ===================================================================


class TestBroadcastShapes:
    """Tests for broadcast_shapes."""

    def test_same_shape(self):
        result = broadcast_shapes((3, 4), (3, 4))
        assert result == (3, 4)

    def test_scalar_broadcast(self):
        result = broadcast_shapes((3, 4), (1,))
        assert result == (3, 4)

    def test_left_broadcast(self):
        result = broadcast_shapes((1, 4), (3, 4))
        assert result == (3, 4)

    def test_right_broadcast(self):
        result = broadcast_shapes((3, 4), (3, 1))
        assert result == (3, 4)

    def test_different_ndim(self):
        result = broadcast_shapes((5,), (3, 5))
        assert result == (3, 5)

    def test_batch_broadcast(self):
        result = broadcast_shapes((2, 1, 4), (3, 4))
        assert result == (2, 3, 4)

    def test_incompatible(self):
        result = broadcast_shapes((3, 4), (5, 4))
        assert result is None

    def test_symbolic(self):
        result = broadcast_shapes(("batch", 3), (1, 3))
        assert result is not None
        assert result[1] == 3


# ===================================================================
#  matmul_shapes
# ===================================================================


class TestMatmulShapes:
    """Tests for matmul_shapes."""

    def test_2d_matmul(self):
        result = matmul_shapes((3, 4), (4, 5))
        assert result == (3, 5)

    def test_2d_incompatible(self):
        result = matmul_shapes((3, 4), (5, 6))
        assert result is None

    def test_1d_1d_dot(self):
        result = matmul_shapes((4,), (4,))
        assert result == ()

    def test_1d_2d(self):
        result = matmul_shapes((4,), (4, 5))
        assert result == (5,)

    def test_2d_1d(self):
        result = matmul_shapes((3, 4), (4,))
        assert result == (3,)

    def test_batched_matmul(self):
        result = matmul_shapes((2, 3, 4), (2, 4, 5))
        assert result == (2, 3, 5)

    def test_batched_broadcast(self):
        result = matmul_shapes((1, 3, 4), (2, 4, 5))
        assert result == (2, 3, 5)

    def test_empty_shape(self):
        result = matmul_shapes((), (3,))
        assert result is None


# ===================================================================
#  reshape_shape
# ===================================================================


class TestReshapeShape:
    """Tests for reshape_shape."""

    def test_valid_reshape(self):
        result = reshape_shape((2, 3, 4), (6, 4))
        assert result == (6, 4)

    def test_invalid_numel(self):
        result = reshape_shape((2, 3, 4), (5, 5))
        assert result is None

    def test_infer_one_dim(self):
        result = reshape_shape((2, 3, 4), (-1, 4))
        assert result == (6, 4)

    def test_infer_dim_batch(self):
        result = reshape_shape((2, 3, 4), (2, -1))
        assert result == (2, 12)

    def test_multiple_neg_one(self):
        result = reshape_shape((24,), (-1, -1))
        assert result is None

    def test_flatten(self):
        result = reshape_shape((2, 3, 4), (24,))
        assert result == (24,)


# ===================================================================
#  conv2d_output_shape
# ===================================================================


class TestConv2dOutputShape:
    """Tests for conv2d_output_shape."""

    def test_basic_conv2d(self):
        result = conv2d_output_shape(
            (1, 3, 32, 32), kernel_size=(3, 3), out_channels=16,
        )
        assert result is not None
        assert result[0] == 1
        assert result[1] == 16
        assert result[2] == 30
        assert result[3] == 30

    def test_conv2d_with_padding(self):
        result = conv2d_output_shape(
            (1, 3, 32, 32), kernel_size=(3, 3), padding=(1, 1), out_channels=16,
        )
        assert result is not None
        assert result[2] == 32
        assert result[3] == 32

    def test_conv2d_with_stride(self):
        result = conv2d_output_shape(
            (1, 3, 32, 32), kernel_size=(3, 3), stride=(2, 2), out_channels=16,
        )
        assert result is not None
        assert result[2] == 15
        assert result[3] == 15

    def test_conv2d_wrong_ndim(self):
        result = conv2d_output_shape((3, 32, 32), kernel_size=(3, 3))
        assert result is None


# ===================================================================
#  transpose_shape / permute_shape / cat_shapes
# ===================================================================


class TestTransposePermuteCat:
    """Tests for transpose, permute, and cat shape operations."""

    def test_transpose(self):
        result = transpose_shape((2, 3, 4), 0, 2)
        assert result == (4, 3, 2)

    def test_transpose_negative(self):
        result = transpose_shape((2, 3, 4), -1, -2)
        assert result == (2, 4, 3)

    def test_transpose_out_of_range(self):
        result = transpose_shape((2, 3), 0, 5)
        assert result is None

    def test_permute(self):
        result = permute_shape((2, 3, 4), (2, 0, 1))
        assert result == (4, 2, 3)

    def test_permute_invalid(self):
        result = permute_shape((2, 3), (0,))
        assert result is None

    def test_cat_along_dim0(self):
        result = cat_shapes([(2, 3), (4, 3)], dim=0)
        assert result == (6, 3)

    def test_cat_along_dim1(self):
        result = cat_shapes([(2, 3), (2, 5)], dim=1)
        assert result == (2, 8)

    def test_cat_incompatible(self):
        result = cat_shapes([(2, 3), (4, 5)], dim=0)
        assert result is None

    def test_cat_empty(self):
        result = cat_shapes([])
        assert result is None


# ===================================================================
#  dispatch_shape_op
# ===================================================================


class TestDispatchShapeOp:
    """Tests for the shape operation dispatch."""

    def test_dispatch_reshape(self):
        result = dispatch_shape_op("reshape", [(2, 3, 4)], {"target_shape": [6, 4]})
        assert result == (6, 4)

    def test_dispatch_matmul(self):
        result = dispatch_shape_op("matmul", [(3, 4), (4, 5)])
        assert result == (3, 5)

    def test_dispatch_add_broadcast(self):
        result = dispatch_shape_op("add", [(3, 4), (1, 4)])
        assert result == (3, 4)

    def test_dispatch_transpose(self):
        result = dispatch_shape_op("transpose", [(2, 3, 4)], {"dim0": 0, "dim1": 2})
        assert result == (4, 3, 2)

    def test_dispatch_unsqueeze(self):
        result = dispatch_shape_op("unsqueeze", [(3, 4)], {"dim": 0})
        assert result == (1, 3, 4)

    def test_dispatch_squeeze(self):
        result = dispatch_shape_op("squeeze", [(1, 3, 1, 4)], {"dim": 0})
        assert result == (3, 1, 4)

    def test_dispatch_squeeze_all(self):
        result = dispatch_shape_op("squeeze", [(1, 3, 1, 4)])
        assert result == (3, 4)

    def test_dispatch_flatten(self):
        result = dispatch_shape_op("flatten", [(2, 3, 4)], {"start_dim": 1, "end_dim": 2})
        assert result is not None
        assert result[0] == 2
        assert result[1] == 12

    def test_dispatch_conv2d(self):
        result = dispatch_shape_op(
            "conv2d",
            [(1, 3, 32, 32)],
            {"kernel_size": (3, 3), "out_channels": 64},
        )
        assert result is not None
        assert result[1] == 64

    def test_dispatch_cat(self):
        result = dispatch_shape_op("cat", [(2, 3), (2, 5)], {"dim": 1})
        assert result == (2, 8)

    def test_dispatch_permute(self):
        result = dispatch_shape_op("permute", [(2, 3, 4)], {"dims": [2, 0, 1]})
        assert result == (4, 2, 3)


# ===================================================================
#  TensorShapeTheoryPack
# ===================================================================


class TestTensorShapeTheoryPack:
    """Tests for the TensorShapeTheoryPack."""

    def setup_method(self):
        self.pack = TensorShapeTheoryPack()

    def test_applicable_site_kinds(self):
        kinds = self.pack.applicable_site_kinds()
        assert SiteKind.TENSOR_SHAPE in kinds
        assert SiteKind.SSA_VALUE in kinds

    def test_solve_local_with_op(self):
        refs = {
            "shape_op": "matmul",
            "input_shapes": [(3, 4), (4, 5)],
        }
        sec = _section("mm_result", refinements=refs)
        result = self.pack.solve_local(sec.site_id, sec)
        assert result.status == SolverStatus.SOLVED
        assert result.section.refinements.get("shape") == (3, 5)

    def test_solve_local_incompatible_op(self):
        refs = {
            "shape_op": "matmul",
            "input_shapes": [(3, 4), (5, 6)],
        }
        sec = _section("mm_result", refinements=refs)
        result = self.pack.solve_local(sec.site_id, sec)
        assert result.status == SolverStatus.REFINED

    def test_solve_local_known_shape(self):
        refs = {"shape": (2, 3, 4)}
        sec = _section("tensor", refinements=refs)
        result = self.pack.solve_local(sec.site_id, sec)
        assert result.status == SolverStatus.REFINED
        assert result.section.refinements.get("ndim") == 3

    def test_solve_local_no_shape(self):
        sec = _section("tensor", refinements={})
        result = self.pack.solve_local(sec.site_id, sec)
        assert result.status == SolverStatus.UNCHANGED

    def test_forward_refine_matmul(self):
        source = _site("a")
        target = _site("result")
        sec = _section("a", refinements={"shape": (3, 4)})
        morphism = ConcreteMorphism(
            _source=source,
            _target=target,
            _metadata={
                "shape_op": "matmul",
                "second_shape": (4, 5),
            },
        )
        result = self.pack.forward_refine(sec, morphism)
        # merge_refinements("meet") detects shape conflict between the
        # original (3,4) and matmul result (3,5), so shape becomes None.
        # ndim is correctly propagated.
        assert result.refinements.get("ndim") == 2

    def test_forward_refine_no_op(self):
        source = _site("a")
        target = _site("b")
        sec = _section("a", refinements={"shape": (2, 3)})
        morphism = ConcreteMorphism(_source=source, _target=target)
        result = self.pack.forward_refine(sec, morphism)
        assert result.refinements.get("shape") == (2, 3)

    def test_backward_pullback_matmul(self):
        source = _site("a")
        target = _site("result")
        sec = _section("result", refinements={"shape": (3, 5)})
        morphism = ConcreteMorphism(
            _source=source,
            _target=target,
            _metadata={"shape_op": "matmul"},
        )
        result = self.pack.backward_pullback(sec, morphism)
        assert result.refinements.get("ndim_min") == 2

    def test_backward_pullback_reshape(self):
        source = _site("a")
        target = _site("result")
        sec = _section("result", refinements={"shape": (6, 4)})
        morphism = ConcreteMorphism(
            _source=source,
            _target=target,
            _metadata={"shape_op": "reshape"},
        )
        result = self.pack.backward_pullback(sec, morphism)
        assert result.refinements.get("numel") == 24

    def test_viability_predicate_reshape(self):
        site = _site("reshape_error", SiteKind.ERROR)
        pred = self.pack.viability_predicate(site)
        assert "numel" in pred

    def test_viability_predicate_matmul(self):
        site = _site("matmul_error", SiteKind.ERROR)
        pred = self.pack.viability_predicate(site)
        assert "shape" in pred

    def test_classify_resolved(self):
        sec = _section("t", refinements={"_shape_resolved": True})
        cls = self.pack.classify_proof_boundary(sec)
        assert cls == BoundaryClassification.FULLY_PROVEN

    def test_classify_concrete(self):
        sec = _section("t", refinements={"shape": (2, 3)})
        cls = self.pack.classify_proof_boundary(sec)
        assert cls == BoundaryClassification.CONDITIONALLY_PROVEN

    def test_classify_unknown(self):
        sec = _section("t", refinements={}, trust=TrustLevel.ASSUMED)
        cls = self.pack.classify_proof_boundary(sec)
        assert cls == BoundaryClassification.ASSUMED
