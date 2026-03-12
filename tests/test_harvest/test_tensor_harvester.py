"""Tests for deppy.harvest.tensor_harvester -- torch API hint extraction.

Exercises extraction of tensor shape, dtype, device, reshape, construction,
and operation facts from Python AST using the TensorHarvester.
"""

from __future__ import annotations

import ast
import pytest

from deppy.harvest.tensor_harvester import (
    TensorFact,
    TensorFactKind,
    TensorFactOrigin,
    TensorHarvester,
    device_facts,
    dtype_facts,
    filter_by_kind,
    filter_by_variable,
    harvest_tensor_facts,
    shape_facts,
)
from deppy.core._protocols import TrustLevel


# ===================================================================
# Helpers
# ===================================================================

def _harvest(source: str, file: str = "test.py") -> list:
    tree = ast.parse(source)
    return harvest_tensor_facts(tree, file=file)


# ===================================================================
# TestAttributeAccess
# ===================================================================

class TestAttributeAccess:
    """Test tensor attribute access harvesting."""

    def test_shape_access(self):
        facts = _harvest("""
def f(x):
    s = x.shape
""")
        shape = filter_by_kind(facts, TensorFactKind.SHAPE)
        assert len(shape) >= 1
        assert any(f.variable == "x" for f in shape)

    def test_dtype_access(self):
        facts = _harvest("""
def f(x):
    d = x.dtype
""")
        dtype = filter_by_kind(facts, TensorFactKind.DTYPE)
        assert len(dtype) >= 1
        assert any(f.variable == "x" for f in dtype)

    def test_device_access(self):
        facts = _harvest("""
def f(x):
    d = x.device
""")
        device = filter_by_kind(facts, TensorFactKind.DEVICE)
        assert len(device) >= 1

    def test_ndim_access(self):
        facts = _harvest("""
def f(x):
    r = x.ndim
""")
        rank = filter_by_kind(facts, TensorFactKind.RANK)
        assert len(rank) >= 1

    def test_T_access(self):
        facts = _harvest("""
def f(x):
    y = x.T
""")
        transpose = filter_by_kind(facts, TensorFactKind.TRANSPOSE)
        assert len(transpose) >= 1

    def test_attribute_origin(self):
        facts = _harvest("""
def f(x):
    s = x.shape
""")
        shape = filter_by_kind(facts, TensorFactKind.SHAPE)
        assert all(f.fact_origin == TensorFactOrigin.ATTRIBUTE_ACCESS for f in shape)


# ===================================================================
# TestMethodCalls
# ===================================================================

class TestMethodCalls:
    """Test tensor method call harvesting."""

    def test_reshape(self):
        facts = _harvest("""
def f(x):
    y = x.reshape(3, 4)
""")
        reshape_facts = filter_by_kind(facts, TensorFactKind.RESHAPE)
        assert len(reshape_facts) >= 1
        assert any(f.operation_name == "reshape" for f in reshape_facts)

    def test_view(self):
        facts = _harvest("""
def f(x):
    y = x.view(3, 4)
""")
        view_facts = filter_by_kind(facts, TensorFactKind.VIEW)
        assert len(view_facts) >= 1

    def test_reshape_target_shape(self):
        facts = _harvest("""
def f(x):
    y = x.reshape(3, 4)
""")
        reshape_facts = filter_by_kind(facts, TensorFactKind.RESHAPE)
        shaped = [f for f in reshape_facts if f.target_shape is not None]
        assert len(shaped) >= 1
        assert shaped[0].rank_value == 2

    def test_transpose(self):
        facts = _harvest("""
def f(x):
    y = x.transpose(0, 1)
""")
        transpose = filter_by_kind(facts, TensorFactKind.TRANSPOSE)
        assert len(transpose) >= 1

    def test_permute(self):
        facts = _harvest("""
def f(x):
    y = x.permute(2, 0, 1)
""")
        permute = filter_by_kind(facts, TensorFactKind.PERMUTE)
        assert len(permute) >= 1

    def test_squeeze(self):
        facts = _harvest("""
def f(x):
    y = x.squeeze()
""")
        squeeze = filter_by_kind(facts, TensorFactKind.SQUEEZE)
        assert len(squeeze) >= 1

    def test_unsqueeze(self):
        facts = _harvest("""
def f(x):
    y = x.unsqueeze(0)
""")
        unsqueeze = filter_by_kind(facts, TensorFactKind.UNSQUEEZE)
        assert len(unsqueeze) >= 1

    def test_flatten(self):
        facts = _harvest("""
def f(x):
    y = x.flatten()
""")
        flatten = filter_by_kind(facts, TensorFactKind.FLATTEN)
        assert len(flatten) >= 1
        assert flatten[0].rank_value == 1

    def test_contiguous(self):
        facts = _harvest("""
def f(x):
    y = x.contiguous()
""")
        contiguous = filter_by_kind(facts, TensorFactKind.CONTIGUOUS)
        assert len(contiguous) >= 1

    def test_size_method(self):
        facts = _harvest("""
def f(x):
    s = x.size()
""")
        shape = filter_by_kind(facts, TensorFactKind.SHAPE)
        assert len(shape) >= 1

    def test_dim_method(self):
        facts = _harvest("""
def f(x):
    d = x.dim()
""")
        rank = filter_by_kind(facts, TensorFactKind.RANK)
        assert len(rank) >= 1


# ===================================================================
# TestReductionOps
# ===================================================================

class TestReductionOps:
    """Test reduction operation harvesting."""

    def test_sum(self):
        facts = _harvest("""
def f(x):
    y = x.sum()
""")
        reduction = filter_by_kind(facts, TensorFactKind.REDUCTION)
        assert len(reduction) >= 1
        assert any(f.operation_name == "sum" for f in reduction)

    def test_mean(self):
        facts = _harvest("""
def f(x):
    y = x.mean()
""")
        reduction = filter_by_kind(facts, TensorFactKind.REDUCTION)
        assert len(reduction) >= 1

    def test_max(self):
        facts = _harvest("""
def f(x):
    y = x.max()
""")
        reduction = filter_by_kind(facts, TensorFactKind.REDUCTION)
        assert len(reduction) >= 1


# ===================================================================
# TestDeviceAndDtypeCasting
# ===================================================================

class TestDeviceAndDtypeCasting:
    """Test .to(), .float(), .cuda(), .cpu() harvesting."""

    def test_to_device(self):
        facts = _harvest("""
def f(x):
    y = x.to("cuda")
""")
        to_device = filter_by_kind(facts, TensorFactKind.TO_DEVICE)
        assert len(to_device) >= 1
        assert any(f.device_value == "cuda" for f in to_device)

    def test_float_method(self):
        facts = _harvest("""
def f(x):
    y = x.float()
""")
        type_cast = filter_by_kind(facts, TensorFactKind.TYPE_CAST)
        assert len(type_cast) >= 1
        assert any(f.dtype_value == "float32" for f in type_cast)

    def test_half_method(self):
        facts = _harvest("""
def f(x):
    y = x.half()
""")
        type_cast = filter_by_kind(facts, TensorFactKind.TYPE_CAST)
        assert any(f.dtype_value == "float16" for f in type_cast)

    def test_long_method(self):
        facts = _harvest("""
def f(x):
    y = x.long()
""")
        type_cast = filter_by_kind(facts, TensorFactKind.TYPE_CAST)
        assert any(f.dtype_value == "int64" for f in type_cast)

    def test_cuda_method(self):
        facts = _harvest("""
def f(x):
    y = x.cuda()
""")
        to_device = filter_by_kind(facts, TensorFactKind.TO_DEVICE)
        assert any(f.device_value == "cuda" for f in to_device)

    def test_cpu_method(self):
        facts = _harvest("""
def f(x):
    y = x.cpu()
""")
        to_device = filter_by_kind(facts, TensorFactKind.TO_DEVICE)
        assert any(f.device_value == "cpu" for f in to_device)

    def test_clone(self):
        facts = _harvest("""
def f(x):
    y = x.clone()
""")
        clone = filter_by_kind(facts, TensorFactKind.CLONE)
        assert len(clone) >= 1

    def test_detach(self):
        facts = _harvest("""
def f(x):
    y = x.detach()
""")
        detach = filter_by_kind(facts, TensorFactKind.DETACH)
        assert len(detach) >= 1

    def test_to_with_dtype_kwarg(self):
        facts = _harvest("""
def f(x):
    y = x.to(dtype=torch.float32)
""")
        type_cast = filter_by_kind(facts, TensorFactKind.TYPE_CAST)
        assert len(type_cast) >= 1


# ===================================================================
# TestConstructorFunctions
# ===================================================================

class TestConstructorFunctions:
    """Test tensor constructor function harvesting."""

    def test_torch_zeros(self):
        facts = _harvest("""
def f():
    x = torch.zeros(3, 4)
""")
        construction = filter_by_kind(facts, TensorFactKind.CONSTRUCTION)
        assert len(construction) >= 1
        shaped = [f for f in construction if f.shape_dims is not None]
        assert len(shaped) >= 1

    def test_torch_ones(self):
        facts = _harvest("""
def f():
    x = torch.ones(5, 5)
""")
        construction = filter_by_kind(facts, TensorFactKind.CONSTRUCTION)
        assert len(construction) >= 1

    def test_torch_randn(self):
        facts = _harvest("""
def f():
    x = torch.randn(3, 4, 5)
""")
        construction = filter_by_kind(facts, TensorFactKind.CONSTRUCTION)
        assert len(construction) >= 1

    def test_torch_eye(self):
        facts = _harvest("""
def f():
    x = torch.eye(5)
""")
        construction = filter_by_kind(facts, TensorFactKind.CONSTRUCTION)
        assert len(construction) >= 1

    def test_torch_arange(self):
        facts = _harvest("""
def f():
    x = torch.arange(10)
""")
        construction = filter_by_kind(facts, TensorFactKind.CONSTRUCTION)
        assert len(construction) >= 1
        assert any(f.rank_value == 1 for f in construction)

    def test_torch_tensor_list(self):
        facts = _harvest("""
def f():
    x = torch.tensor([1, 2, 3])
""")
        construction = filter_by_kind(facts, TensorFactKind.CONSTRUCTION)
        assert len(construction) >= 1

    def test_constructor_with_dtype(self):
        facts = _harvest("""
def f():
    x = torch.zeros(3, 4, dtype=torch.float64)
""")
        construction = filter_by_kind(facts, TensorFactKind.CONSTRUCTION)
        with_dtype = [f for f in construction if f.dtype_value is not None]
        assert len(with_dtype) >= 1

    def test_constructor_with_device(self):
        facts = _harvest("""
def f():
    x = torch.zeros(3, 4, device="cuda")
""")
        construction = filter_by_kind(facts, TensorFactKind.CONSTRUCTION)
        with_device = [f for f in construction if f.device_value is not None]
        assert len(with_device) >= 1

    def test_numpy_constructor(self):
        facts = _harvest("""
def f():
    x = np.zeros((3, 4))
""")
        construction = filter_by_kind(facts, TensorFactKind.CONSTRUCTION)
        assert len(construction) >= 1
        assert any(f.framework == "numpy" for f in construction)


# ===================================================================
# TestConcatenationAndMatmul
# ===================================================================

class TestConcatenationAndMatmul:
    """Test concatenation and matmul harvesting."""

    def test_torch_cat(self):
        facts = _harvest("""
def f(a, b):
    c = torch.cat([a, b])
""")
        concat = filter_by_kind(facts, TensorFactKind.CONCATENATION)
        assert len(concat) >= 1

    def test_torch_stack(self):
        facts = _harvest("""
def f(a, b):
    c = torch.stack([a, b])
""")
        concat = filter_by_kind(facts, TensorFactKind.CONCATENATION)
        assert len(concat) >= 1

    def test_matmul_operator(self):
        facts = _harvest("""
def f(a, b):
    c = a @ b
""")
        matmul = filter_by_kind(facts, TensorFactKind.MATMUL)
        assert len(matmul) >= 1

    def test_torch_matmul(self):
        facts = _harvest("""
def f(a, b):
    c = torch.matmul(a, b)
""")
        matmul = filter_by_kind(facts, TensorFactKind.MATMUL)
        assert len(matmul) >= 1


# ===================================================================
# TestFilteringUtilities
# ===================================================================

class TestFilteringUtilities:
    """Test filtering convenience functions."""

    def test_filter_by_variable(self):
        facts = _harvest("""
def f(x, y):
    s1 = x.shape
    s2 = y.shape
""")
        x_facts = filter_by_variable(facts, "x")
        assert all(f.variable == "x" for f in x_facts)

    def test_shape_facts(self):
        facts = _harvest("""
def f():
    x = torch.zeros(3, 4)
    s = x.shape
""")
        sf = shape_facts(facts)
        # shape_facts returns facts with shape_dims not None
        for f in sf:
            assert f.shape_dims is not None

    def test_dtype_facts(self):
        facts = _harvest("""
def f(x):
    y = x.float()
""")
        df = dtype_facts(facts)
        assert all(f.dtype_value is not None for f in df)

    def test_device_facts(self):
        facts = _harvest("""
def f(x):
    y = x.cuda()
""")
        devf = device_facts(facts)
        assert all(f.device_value is not None for f in devf)


# ===================================================================
# TestScopeTracking
# ===================================================================

class TestScopeTracking:
    """Test function scope tracking in TensorHarvester."""

    def test_enclosing_function(self):
        facts = _harvest("""
def f(x):
    s = x.shape

def g(y):
    d = y.dtype
""")
        f_facts = [f for f in facts if f.enclosing_function == "f"]
        g_facts = [f for f in facts if f.enclosing_function == "g"]
        assert len(f_facts) >= 1
        assert len(g_facts) >= 1

    def test_class_scope(self):
        facts = _harvest("""
class Model:
    def forward(self, x):
        s = x.shape
""")
        assert any(f.enclosing_function == "forward" for f in facts)


# ===================================================================
# TestTensorFactKind
# ===================================================================

class TestTensorFactKind:
    """Test TensorFactKind enum completeness."""

    def test_core_kinds(self):
        expected_subset = {
            "shape", "rank", "dtype", "device", "reshape", "view",
            "transpose", "permute", "squeeze", "unsqueeze", "flatten",
            "construction", "matmul", "reduction", "concatenation",
        }
        actual = {k.value for k in TensorFactKind}
        assert expected_subset.issubset(actual)
