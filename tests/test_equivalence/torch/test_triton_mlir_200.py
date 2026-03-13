"""
200 hard Triton/MLIR equivalence benchmark pairs.

100 equivalent pairs (structurally same, looking very different)
100 non-equivalent pairs (subtle structural differences)

All pairs are tested against TritonEquivalenceChecker and
MLIREquivalenceChecker and scored for precision/recall/F1.
"""
from __future__ import annotations

import unittest
from dataclasses import dataclass
from typing import List, Tuple

from deppy.core._protocols import SiteId, SiteKind
from deppy.equivalence.torch._protocols import (
    EquivalenceVerdict,
    TensorEquivalenceConfig,
    TritonKernelSpec,
    MLIRModuleSpec,
)
from deppy.equivalence.torch.triton_ir import build_kernel_spec
from deppy.equivalence.torch.triton_equiv import TritonEquivalenceChecker
from deppy.equivalence.torch.triton_mlir import (
    MLIREquivalenceChecker,
    build_mlir_module_spec,
)


def _sid(n: str = "bench") -> SiteId:
    return SiteId(kind=SiteKind.TENSOR_SHAPE, name=n)


# ═══════════════════════════════════════════════════════════════════════
#  TRITON EQUIVALENT PAIRS (50 pairs)
#  Same structure, different surface syntax
# ═══════════════════════════════════════════════════════════════════════

TRITON_EQ: List[Tuple[str, str, str]] = []

# -- 1. Variable renaming: simple add kernel ----------------------------
TRITON_EQ.append(("eq_t01_varnames_add", """
import triton, triton.language as tl
@triton.jit
def add_k(x_ptr, y_ptr, out_ptr, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 1024
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask)
    y = tl.load(y_ptr + offs, mask=mask)
    tl.store(out_ptr + offs, x + y, mask=mask)
""", """
import triton, triton.language as tl
@triton.jit
def vector_add(alpha_ptr, beta_ptr, gamma_ptr, n_elements: tl.constexpr):
    block_id = tl.program_id(0)
    BLOCK_DIM: tl.constexpr = 1024
    indices = block_id * BLOCK_DIM + tl.arange(0, BLOCK_DIM)
    valid = indices < n_elements
    alpha_val = tl.load(alpha_ptr + indices, mask=valid)
    beta_val = tl.load(beta_ptr + indices, mask=valid)
    tl.store(gamma_ptr + indices, alpha_val + beta_val, mask=valid)
"""))

# -- 2. Variable renaming: mul kernel -----------------------------------
TRITON_EQ.append(("eq_t02_varnames_mul", """
import triton, triton.language as tl
@triton.jit
def mul(a, b, c, n: tl.constexpr):
    i = tl.program_id(0)
    BLOCK_M: tl.constexpr = 256
    off = i * BLOCK_M + tl.arange(0, BLOCK_M)
    m = off < n
    va = tl.load(a + off, mask=m)
    vb = tl.load(b + off, mask=m)
    tl.store(c + off, va * vb, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def elementwise_multiply(input_x, input_y, output_z, num_elems: tl.constexpr):
    program_index = tl.program_id(0)
    TILE_N: tl.constexpr = 256
    element_offsets = program_index * TILE_N + tl.arange(0, TILE_N)
    boundary_mask = element_offsets < num_elems
    x_data = tl.load(input_x + element_offsets, mask=boundary_mask)
    y_data = tl.load(input_y + element_offsets, mask=boundary_mask)
    tl.store(output_z + element_offsets, x_data * y_data, mask=boundary_mask)
"""))

# -- 3. Different intermediate computations (same L/S/R) ---------------
TRITON_EQ.append(("eq_t03_intermediates", """
import triton, triton.language as tl
@triton.jit
def k(x, y, o, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 512
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    a = tl.load(x + off, mask=m)
    b = tl.load(y + off, mask=m)
    tl.store(o + off, a + b, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def k(x, y, o, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 512
    base = pid * BLOCK_SIZE
    off = base + tl.arange(0, BLOCK_SIZE)
    m = off < N
    a = tl.load(x + off, mask=m)
    b = tl.load(y + off, mask=m)
    c = a * 2 + b * 3
    d = a + b
    result = d
    tl.store(o + off, result, mask=m)
"""))

# -- 4. Swapped operand order -------------------------------------------
TRITON_EQ.append(("eq_t04_swap_operands", """
import triton, triton.language as tl
@triton.jit
def k(A, B, C, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 128
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    a = tl.load(A + off, mask=m)
    b = tl.load(B + off, mask=m)
    tl.store(C + off, a + b, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def k(B, A, C, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 128
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    b = tl.load(B + off, mask=m)
    a = tl.load(A + off, mask=m)
    tl.store(C + off, b + a, mask=m)
"""))

# -- 5. Different address arithmetic ------------------------------------
TRITON_EQ.append(("eq_t05_addr_arith", """
import triton, triton.language as tl
@triton.jit
def k(x, o, N: tl.constexpr, stride: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 1024
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    a = tl.load(x + off * stride, mask=m)
    tl.store(o + off, a, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def copy_strided(src, dst, count: tl.constexpr, s: tl.constexpr):
    idx = tl.program_id(0)
    BLOCK_DIM: tl.constexpr = 1024
    offsets = idx * BLOCK_DIM + tl.arange(0, BLOCK_DIM)
    valid = offsets < count
    val = tl.load(src + offsets * s, mask=valid)
    tl.store(dst + offsets, val, mask=valid)
"""))

# -- 6. Different arange styles -----------------------------------------
TRITON_EQ.append(("eq_t06_arange_style", """
import triton, triton.language as tl
@triton.jit
def k(x, y, o, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    r = tl.arange(0, BLOCK_SIZE)
    off = pid * BLOCK_SIZE + r
    m = off < N
    a = tl.load(x + off, mask=m)
    b = tl.load(y + off, mask=m)
    tl.store(o + off, a - b, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def sub_kernel(input_a, input_b, output_c, size: tl.constexpr):
    block_idx = tl.program_id(0)
    TILE_DIM: tl.constexpr = 256
    lane_ids = tl.arange(0, TILE_DIM)
    global_ids = block_idx * TILE_DIM + lane_ids
    in_bounds = global_ids < size
    data_a = tl.load(input_a + global_ids, mask=in_bounds)
    data_b = tl.load(input_b + global_ids, mask=in_bounds)
    tl.store(output_c + global_ids, data_a - data_b, mask=in_bounds)
"""))

# -- 7. Reduction sum with different variable names ----------------------
TRITON_EQ.append(("eq_t07_sum_rename", """
import triton, triton.language as tl
@triton.jit
def sum_k(x_ptr, out_ptr, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 1024
    offs = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offs < N
    x = tl.load(x_ptr + offs, mask=mask)
    s = tl.sum(x, axis=0)
    tl.store(out_ptr + pid, s)
""", """
import triton, triton.language as tl
@triton.jit
def reduce_add(input_data, result, n_elements: tl.constexpr):
    block_id = tl.program_id(0)
    TILE_SIZE: tl.constexpr = 1024
    indices = block_id * TILE_SIZE + tl.arange(0, TILE_SIZE)
    valid = indices < n_elements
    data = tl.load(input_data + indices, mask=valid)
    total = tl.sum(data, axis=0)
    tl.store(result + block_id, total)
"""))

# -- 8. Max reduction with different naming ------------------------------
TRITON_EQ.append(("eq_t08_max_rename", """
import triton, triton.language as tl
@triton.jit
def max_k(x, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 512
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    mx = tl.max(v, axis=0)
    tl.store(out + pid, mx)
""", """
import triton, triton.language as tl
@triton.jit
def find_maximum(arr_ptr, result_ptr, length: tl.constexpr):
    gid = tl.program_id(0)
    TILE_M: tl.constexpr = 512
    positions = gid * TILE_M + tl.arange(0, TILE_M)
    boundary = positions < length
    values = tl.load(arr_ptr + positions, mask=boundary)
    peak = tl.max(values, axis=0)
    tl.store(result_ptr + gid, peak)
"""))

# -- 9. Min reduction ---------------------------------------------------
TRITON_EQ.append(("eq_t09_min_rename", """
import triton, triton.language as tl
@triton.jit
def min_k(x, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    mn = tl.min(v, axis=0)
    tl.store(out + pid, mn)
""", """
import triton, triton.language as tl
@triton.jit
def minimum_element(data_ptr, out_ptr, count: tl.constexpr):
    tid = tl.program_id(0)
    TILE_K: tl.constexpr = 256
    idx = tid * TILE_K + tl.arange(0, TILE_K)
    valid = idx < count
    elements = tl.load(data_ptr + idx, mask=valid)
    smallest = tl.min(elements, axis=0)
    tl.store(out_ptr + tid, smallest)
"""))

# -- 10. Copy kernel, extra intermediates --------------------------------
TRITON_EQ.append(("eq_t10_copy_intermediates", """
import triton, triton.language as tl
@triton.jit
def copy(src, dst, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 2048
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(src + off, mask=m)
    tl.store(dst + off, v, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def memcpy_kernel(source_ptr, dest_ptr, length: tl.constexpr):
    program_id = tl.program_id(0)
    TILE_SIZE: tl.constexpr = 2048
    base_offset = program_id * TILE_SIZE
    lane_offset = tl.arange(0, TILE_SIZE)
    global_offset = base_offset + lane_offset
    is_valid = global_offset < length
    temp = tl.load(source_ptr + global_offset, mask=is_valid)
    result = temp + 0.0
    final = result
    tl.store(dest_ptr + global_offset, final, mask=is_valid)
"""))

# -- 11. Softmax-style: exp + sum + store (same structure) ---------------
TRITON_EQ.append(("eq_t11_softmax_style", """
import triton, triton.language as tl
@triton.jit
def softmax_k(x, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    s = tl.sum(v, axis=0)
    tl.store(out + pid, s)
""", """
import triton, triton.language as tl
@triton.jit
def normalized_sum(input_ptr, output_ptr, num_elements: tl.constexpr):
    block_idx = tl.program_id(0)
    TILE_WIDTH: tl.constexpr = 256
    positions = block_idx * TILE_WIDTH + tl.arange(0, TILE_WIDTH)
    active = positions < num_elements
    raw_data = tl.load(input_ptr + positions, mask=active)
    accumulated = tl.sum(raw_data, axis=0)
    tl.store(output_ptr + block_idx, accumulated)
"""))

# -- 12. Two loads, one store, reduction ---------------------------------
TRITON_EQ.append(("eq_t12_dot_style", """
import triton, triton.language as tl
@triton.jit
def dot_k(a, b, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 512
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    va = tl.load(a + off, mask=m)
    vb = tl.load(b + off, mask=m)
    s = tl.sum(va * vb, axis=0)
    tl.store(out + pid, s)
""", """
import triton, triton.language as tl
@triton.jit
def inner_product(left_ptr, right_ptr, result_ptr, length: tl.constexpr):
    block_id = tl.program_id(0)
    TILE_DIM: tl.constexpr = 512
    offsets = block_id * TILE_DIM + tl.arange(0, TILE_DIM)
    valid = offsets < length
    left_vals = tl.load(left_ptr + offsets, mask=valid)
    right_vals = tl.load(right_ptr + offsets, mask=valid)
    product_sum = tl.sum(left_vals * right_vals, axis=0)
    tl.store(result_ptr + block_id, product_sum)
"""))

# -- 13. Scale kernel (1 load, 1 store) --------------------------------
TRITON_EQ.append(("eq_t13_scale_rename", """
import triton, triton.language as tl
@triton.jit
def scale(x, out, N: tl.constexpr, s: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 1024
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    tl.store(out + off, v * s, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def scalar_multiply(data_ptr, output_ptr, count: tl.constexpr, factor: tl.constexpr):
    tid = tl.program_id(0)
    TILE_K: tl.constexpr = 1024
    idx = tid * TILE_K + tl.arange(0, TILE_K)
    active = idx < count
    input_val = tl.load(data_ptr + idx, mask=active)
    scaled = input_val * factor
    tl.store(output_ptr + idx, scaled, mask=active)
"""))

# -- 14. Three inputs, one output --------------------------------------
TRITON_EQ.append(("eq_t14_fma_style", """
import triton, triton.language as tl
@triton.jit
def fma_k(a, b, c, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    va = tl.load(a + off, mask=m)
    vb = tl.load(b + off, mask=m)
    vc = tl.load(c + off, mask=m)
    tl.store(out + off, va * vb + vc, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def fused_multiply_add(x_ptr, y_ptr, z_ptr, result_ptr, n: tl.constexpr):
    gid = tl.program_id(0)
    TILE_SIZE: tl.constexpr = 256
    indices = gid * TILE_SIZE + tl.arange(0, TILE_SIZE)
    in_range = indices < n
    x = tl.load(x_ptr + indices, mask=in_range)
    y = tl.load(y_ptr + indices, mask=in_range)
    z = tl.load(z_ptr + indices, mask=in_range)
    tl.store(result_ptr + indices, x * y + z, mask=in_range)
"""))

# -- 15. Two stores (scatter-like) -------------------------------------
TRITON_EQ.append(("eq_t15_two_stores", """
import triton, triton.language as tl
@triton.jit
def k(x, out1, out2, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 512
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    tl.store(out1 + off, v, mask=m)
    tl.store(out2 + off, v * 2.0, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def duplicate_and_scale(src, dest_a, dest_b, length: tl.constexpr):
    block_id = tl.program_id(0)
    TILE_N: tl.constexpr = 512
    offsets = block_id * TILE_N + tl.arange(0, TILE_N)
    valid = offsets < length
    data = tl.load(src + offsets, mask=valid)
    tl.store(dest_a + offsets, data, mask=valid)
    tl.store(dest_b + offsets, data * 2.0, mask=valid)
"""))

# -- 16. Unmasked loads (both unmasked = equivalent) --------------------
TRITON_EQ.append(("eq_t16_unmasked_both", """
import triton, triton.language as tl
@triton.jit
def k(x, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 64
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    v = tl.load(x + off)
    tl.store(out + off, v)
""", """
import triton, triton.language as tl
@triton.jit
def raw_copy(src_ptr, dst_ptr, count: tl.constexpr):
    idx = tl.program_id(0)
    TILE_SIZE: tl.constexpr = 64
    positions = idx * TILE_SIZE + tl.arange(0, TILE_SIZE)
    vals = tl.load(src_ptr + positions)
    tl.store(dst_ptr + positions, vals)
"""))

# -- 17. Complex address computation (same structure) --------------------
TRITON_EQ.append(("eq_t17_complex_addr", """
import triton, triton.language as tl
@triton.jit
def k(x, y, out, N: tl.constexpr, stride_x: tl.constexpr, stride_y: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 128
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    a = tl.load(x + off * stride_x, mask=m)
    b = tl.load(y + off * stride_y, mask=m)
    tl.store(out + off, a + b, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def strided_add(p, q, r, count: tl.constexpr, sp: tl.constexpr, sq: tl.constexpr):
    block_idx = tl.program_id(0)
    TILE_DIM: tl.constexpr = 128
    offsets = block_idx * TILE_DIM + tl.arange(0, TILE_DIM)
    active = offsets < count
    p_val = tl.load(p + offsets * sp, mask=active)
    q_val = tl.load(q + offsets * sq, mask=active)
    tl.store(r + offsets, p_val + q_val, mask=active)
"""))

# -- 18. Different constant expression style ----------------------------
TRITON_EQ.append(("eq_t18_const_style", """
import triton, triton.language as tl
@triton.jit
def k(x, o, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    result = v * 3.14159
    tl.store(o + off, result, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def pi_scale(input_p, output_p, elements: tl.constexpr):
    lane = tl.program_id(0)
    TILE_M: tl.constexpr = 256
    ids = lane * TILE_M + tl.arange(0, TILE_M)
    ok = ids < elements
    data = tl.load(input_p + ids, mask=ok)
    pi_val = 3.14159
    scaled = data * pi_val
    tl.store(output_p + ids, scaled, mask=ok)
"""))

# -- 19. Conditional that doesn't affect L/S/R -------------------------
TRITON_EQ.append(("eq_t19_dead_conditional", """
import triton, triton.language as tl
@triton.jit
def k(x, y, o, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 512
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    a = tl.load(x + off, mask=m)
    b = tl.load(y + off, mask=m)
    tl.store(o + off, a + b, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def k(x, y, o, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 512
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    a = tl.load(x + off, mask=m)
    b = tl.load(y + off, mask=m)
    c = a + b
    tl.store(o + off, c, mask=m)
"""))

# -- 20. Sum reduction, different accumulator style ----------------------
TRITON_EQ.append(("eq_t20_sum_accum_style", """
import triton, triton.language as tl
@triton.jit
def k(x, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 128
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    x_val = tl.load(x + off, mask=m)
    total = tl.sum(x_val, axis=0)
    tl.store(out + pid, total)
""", """
import triton, triton.language as tl
@triton.jit
def accumulate(src_ptr, dst_ptr, length: tl.constexpr):
    warp_id = tl.program_id(0)
    TILE_K: tl.constexpr = 128
    positions = warp_id * TILE_K + tl.arange(0, TILE_K)
    within_bounds = positions < length
    chunk = tl.load(src_ptr + positions, mask=within_bounds)
    reduction_result = tl.sum(chunk, axis=0)
    tl.store(dst_ptr + warp_id, reduction_result)
"""))

# -- 21-30. More complex equivalent pairs with different surface syntax --
TRITON_EQ.append(("eq_t21_relu_style", """
import triton, triton.language as tl
@triton.jit
def relu_k(x, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 1024
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    tl.store(out + off, v, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def activation_forward(input_data, output_data, num_elems: tl.constexpr):
    block_id = tl.program_id(0)
    TILE_SIZE: tl.constexpr = 1024
    indices = block_id * TILE_SIZE + tl.arange(0, TILE_SIZE)
    active = indices < num_elems
    values = tl.load(input_data + indices, mask=active)
    tl.store(output_data + indices, values, mask=active)
"""))

TRITON_EQ.append(("eq_t22_layernorm_loads", """
import triton, triton.language as tl
@triton.jit
def k(x, w, b, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    xv = tl.load(x + off, mask=m)
    wv = tl.load(w + off, mask=m)
    bv = tl.load(b + off, mask=m)
    r = tl.sum(xv, axis=0)
    tl.store(out + off, xv * wv + bv, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def norm_affine(input_ptr, gamma_ptr, beta_ptr, result_ptr, dim: tl.constexpr):
    gid = tl.program_id(0)
    TILE_N: tl.constexpr = 256
    offsets = gid * TILE_N + tl.arange(0, TILE_N)
    valid = offsets < dim
    inp = tl.load(input_ptr + offsets, mask=valid)
    scale = tl.load(gamma_ptr + offsets, mask=valid)
    shift = tl.load(beta_ptr + offsets, mask=valid)
    mean_val = tl.sum(inp, axis=0)
    tl.store(result_ptr + offsets, inp * scale + shift, mask=valid)
"""))

TRITON_EQ.append(("eq_t23_gather_style", """
import triton, triton.language as tl
@triton.jit
def k(src, idx_ptr, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 128
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    idx = tl.load(idx_ptr + off, mask=m)
    v = tl.load(src + idx, mask=m)
    tl.store(out + off, v, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def indexed_read(data_ptr, index_ptr, output_ptr, length: tl.constexpr):
    block_id = tl.program_id(0)
    TILE_DIM: tl.constexpr = 128
    positions = block_id * TILE_DIM + tl.arange(0, TILE_DIM)
    active = positions < length
    indices = tl.load(index_ptr + positions, mask=active)
    gathered = tl.load(data_ptr + indices, mask=active)
    tl.store(output_ptr + positions, gathered, mask=active)
"""))

TRITON_EQ.append(("eq_t24_two_reductions", """
import triton, triton.language as tl
@triton.jit
def k(x, out_sum, out_max, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    s = tl.sum(v, axis=0)
    mx = tl.max(v, axis=0)
    tl.store(out_sum + pid, s)
    tl.store(out_max + pid, mx)
""", """
import triton, triton.language as tl
@triton.jit
def stats_kernel(data_ptr, sum_out, max_out, count: tl.constexpr):
    block_idx = tl.program_id(0)
    TILE_K: tl.constexpr = 256
    offsets = block_idx * TILE_K + tl.arange(0, TILE_K)
    valid = offsets < count
    values = tl.load(data_ptr + offsets, mask=valid)
    total = tl.sum(values, axis=0)
    peak = tl.max(values, axis=0)
    tl.store(sum_out + block_idx, total)
    tl.store(max_out + block_idx, peak)
"""))

TRITON_EQ.append(("eq_t25_four_loads", """
import triton, triton.language as tl
@triton.jit
def k(a, b, c, d, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 128
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    va = tl.load(a + off, mask=m)
    vb = tl.load(b + off, mask=m)
    vc = tl.load(c + off, mask=m)
    vd = tl.load(d + off, mask=m)
    tl.store(out + off, va + vb + vc + vd, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def add4(p0, p1, p2, p3, result, length: tl.constexpr):
    gid = tl.program_id(0)
    TILE_SIZE: tl.constexpr = 128
    idx = gid * TILE_SIZE + tl.arange(0, TILE_SIZE)
    ok = idx < length
    v0 = tl.load(p0 + idx, mask=ok)
    v1 = tl.load(p1 + idx, mask=ok)
    v2 = tl.load(p2 + idx, mask=ok)
    v3 = tl.load(p3 + idx, mask=ok)
    tl.store(result + idx, v0 + v1 + v2 + v3, mask=ok)
"""))

# 26-35: More patterns
for i, (op_a, op_b) in enumerate([
    ("a + b", "b + a"), ("a * b", "b * a"), ("a - b", "a - b"),
    ("a + b + 1.0", "1.0 + a + b"), ("a * b * 2.0", "2.0 * a * b"),
], start=26):
    TRITON_EQ.append((f"eq_t{i}_commutative_{i}", f"""
import triton, triton.language as tl
@triton.jit
def k(x, y, o, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    a = tl.load(x + off, mask=m)
    b = tl.load(y + off, mask=m)
    tl.store(o + off, {op_a}, mask=m)
""", f"""
import triton, triton.language as tl
@triton.jit
def kernel_func(input_a, input_b, output_c, size: tl.constexpr):
    block_id = tl.program_id(0)
    TILE_DIM: tl.constexpr = 256
    offsets = block_id * TILE_DIM + tl.arange(0, TILE_DIM)
    valid = offsets < size
    a = tl.load(input_a + offsets, mask=valid)
    b = tl.load(input_b + offsets, mask=valid)
    tl.store(output_c + offsets, {op_b}, mask=valid)
"""))

# 31-40: Different block names but same structure
for i, (bname_a, bname_b) in enumerate([
    ("BLOCK_M", "TILE_K"), ("BLOCK_N", "TILE_M"), ("BLOCK_K", "BLOCK_J"),
    ("TILE_X", "BLOCK_Y"), ("TILE_A", "TILE_B"),
], start=31):
    TRITON_EQ.append((f"eq_t{i}_blockname_{bname_a}_{bname_b}", f"""
import triton, triton.language as tl
@triton.jit
def k(x, y, o, N: tl.constexpr):
    pid = tl.program_id(0)
    {bname_a}: tl.constexpr = 256
    off = pid * {bname_a} + tl.arange(0, {bname_a})
    m = off < N
    a = tl.load(x + off, mask=m)
    b = tl.load(y + off, mask=m)
    tl.store(o + off, a + b, mask=m)
""", f"""
import triton, triton.language as tl
@triton.jit
def kernel(p, q, r, count: tl.constexpr):
    idx = tl.program_id(0)
    {bname_b}: tl.constexpr = 256
    offsets = idx * {bname_b} + tl.arange(0, {bname_b})
    valid = offsets < count
    pv = tl.load(p + offsets, mask=valid)
    qv = tl.load(q + offsets, mask=valid)
    tl.store(r + offsets, pv + qv, mask=valid)
"""))

# 36-45: More equivalent variants
for i, (nloads, nstores, has_mask) in enumerate([
    (1, 1, True), (2, 1, True), (3, 1, True), (1, 2, True), (2, 2, True),
    (1, 1, False), (2, 1, False), (3, 2, True), (4, 1, True), (1, 3, True),
], start=36):
    loads_a = "\n    ".join(f"v{j} = tl.load(x{j} + off{', mask=m' if has_mask else ''})"
                           for j in range(nloads))
    loads_b = "\n    ".join(f"data_{j} = tl.load(ptr_{j} + idx{', mask=valid' if has_mask else ''})"
                           for j in range(nloads))
    sum_expr_a = " + ".join(f"v{j}" for j in range(nloads))
    sum_expr_b = " + ".join(f"data_{j}" for j in range(nloads))
    stores_a = "\n    ".join(
        f"tl.store(o{j} + off, {sum_expr_a}{', mask=m' if has_mask else ''})"
        for j in range(nstores))
    stores_b = "\n    ".join(
        f"tl.store(out_{j} + idx, {sum_expr_b}{', mask=valid' if has_mask else ''})"
        for j in range(nstores))
    params_a = ", ".join([f"x{j}" for j in range(nloads)] +
                         [f"o{j}" for j in range(nstores)] + ["N: tl.constexpr"])
    params_b = ", ".join([f"ptr_{j}" for j in range(nloads)] +
                         [f"out_{j}" for j in range(nstores)] + ["count: tl.constexpr"])
    mask_line_a = "\n    m = off < N" if has_mask else ""
    mask_line_b = "\n    valid = idx < count" if has_mask else ""

    TRITON_EQ.append((f"eq_t{i}_L{nloads}S{nstores}M{int(has_mask)}", f"""
import triton, triton.language as tl
@triton.jit
def k({params_a}):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE){mask_line_a}
    {loads_a}
    {stores_a}
""", f"""
import triton, triton.language as tl
@triton.jit
def kernel({params_b}):
    block_id = tl.program_id(0)
    TILE_SIZE: tl.constexpr = 256
    idx = block_id * TILE_SIZE + tl.arange(0, TILE_SIZE){mask_line_b}
    {loads_b}
    {stores_b}
"""))

# 46-50: Reduction variants
for i, (red_op, n_inputs) in enumerate([
    ("sum", 1), ("max", 1), ("min", 1), ("sum", 2), ("max", 2),
], start=46):
    in_params_a = ", ".join(f"x{j}" for j in range(n_inputs))
    in_params_b = ", ".join(f"inp_{j}" for j in range(n_inputs))
    loads_a = "\n    ".join(f"v{j} = tl.load(x{j} + off, mask=m)" for j in range(n_inputs))
    loads_b = "\n    ".join(f"d{j} = tl.load(inp_{j} + idx, mask=valid)" for j in range(n_inputs))
    red_input_a = " + ".join(f"v{j}" for j in range(n_inputs)) if n_inputs > 1 else "v0"
    red_input_b = " + ".join(f"d{j}" for j in range(n_inputs)) if n_inputs > 1 else "d0"

    TRITON_EQ.append((f"eq_t{i}_red_{red_op}_L{n_inputs}", f"""
import triton, triton.language as tl
@triton.jit
def k({in_params_a}, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    {loads_a}
    r = tl.{red_op}({red_input_a}, axis=0)
    tl.store(out + pid, r)
""", f"""
import triton, triton.language as tl
@triton.jit
def reduction_kernel({in_params_b}, result, count: tl.constexpr):
    gid = tl.program_id(0)
    TILE_DIM: tl.constexpr = 256
    idx = gid * TILE_DIM + tl.arange(0, TILE_DIM)
    valid = idx < count
    {loads_b}
    reduced = tl.{red_op}({red_input_b}, axis=0)
    tl.store(result + gid, reduced)
"""))


# ═══════════════════════════════════════════════════════════════════════
#  TRITON NON-EQUIVALENT PAIRS (50 pairs)
#  Subtle structural differences
# ═══════════════════════════════════════════════════════════════════════

TRITON_NEQ: List[Tuple[str, str, str]] = []

# -- 1-5: Extra load ---------------------------------------------------
TRITON_NEQ.append(("neq_t01_extra_load", """
import triton, triton.language as tl
@triton.jit
def k(x, y, o, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    a = tl.load(x + off, mask=m)
    b = tl.load(y + off, mask=m)
    tl.store(o + off, a + b, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def k(x, y, z, o, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    a = tl.load(x + off, mask=m)
    b = tl.load(y + off, mask=m)
    c = tl.load(z + off, mask=m)
    tl.store(o + off, a + b + c, mask=m)
"""))

TRITON_NEQ.append(("neq_t02_missing_load", """
import triton, triton.language as tl
@triton.jit
def k(x, y, o, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    a = tl.load(x + off, mask=m)
    b = tl.load(y + off, mask=m)
    tl.store(o + off, a + b, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def k(x, o, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    a = tl.load(x + off, mask=m)
    tl.store(o + off, a, mask=m)
"""))

TRITON_NEQ.append(("neq_t03_extra_store", """
import triton, triton.language as tl
@triton.jit
def k(x, o, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    a = tl.load(x + off, mask=m)
    tl.store(o + off, a, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def k(x, o1, o2, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    a = tl.load(x + off, mask=m)
    tl.store(o1 + off, a, mask=m)
    tl.store(o2 + off, a * 2, mask=m)
"""))

TRITON_NEQ.append(("neq_t04_masked_vs_unmasked_load", """
import triton, triton.language as tl
@triton.jit
def k(x, o, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    a = tl.load(x + off, mask=m)
    tl.store(o + off, a, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def k(x, o, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    a = tl.load(x + off)
    tl.store(o + off, a)
"""))

TRITON_NEQ.append(("neq_t05_sum_vs_max", """
import triton, triton.language as tl
@triton.jit
def k(x, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    r = tl.sum(v, axis=0)
    tl.store(out + pid, r)
""", """
import triton, triton.language as tl
@triton.jit
def k(x, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    r = tl.max(v, axis=0)
    tl.store(out + pid, r)
"""))

# -- 6-10: Reduction differences ----------------------------------------
TRITON_NEQ.append(("neq_t06_sum_vs_min", """
import triton, triton.language as tl
@triton.jit
def k(x, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 512
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    r = tl.sum(v, axis=0)
    tl.store(out + pid, r)
""", """
import triton, triton.language as tl
@triton.jit
def k(x, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 512
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    r = tl.min(v, axis=0)
    tl.store(out + pid, r)
"""))

TRITON_NEQ.append(("neq_t07_max_vs_min", """
import triton, triton.language as tl
@triton.jit
def k(x, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 128
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    r = tl.max(v, axis=0)
    tl.store(out + pid, r)
""", """
import triton, triton.language as tl
@triton.jit
def k(x, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 128
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    r = tl.min(v, axis=0)
    tl.store(out + pid, r)
"""))

TRITON_NEQ.append(("neq_t08_one_red_vs_two", """
import triton, triton.language as tl
@triton.jit
def k(x, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    s = tl.sum(v, axis=0)
    tl.store(out + pid, s)
""", """
import triton, triton.language as tl
@triton.jit
def k(x, out_s, out_m, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    s = tl.sum(v, axis=0)
    mx = tl.max(v, axis=0)
    tl.store(out_s + pid, s)
    tl.store(out_m + pid, mx)
"""))

TRITON_NEQ.append(("neq_t09_no_red_vs_red", """
import triton, triton.language as tl
@triton.jit
def k(x, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    tl.store(out + off, v, mask=m)
""", """
import triton, triton.language as tl
@triton.jit
def k(x, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    s = tl.sum(v, axis=0)
    tl.store(out + pid, s)
"""))

TRITON_NEQ.append(("neq_t10_atomic_vs_regular", """
import triton, triton.language as tl
@triton.jit
def k(x, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    s = tl.sum(v, axis=0)
    tl.store(out + pid, s)
""", """
import triton, triton.language as tl
@triton.jit
def k(x, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    s = tl.sum(v, axis=0)
    tl.atomic_add(out, s)
"""))

# -- 11-20: Mixed load/store count diffs --------------------------------
for i, (nl_a, ns_a, nr_a, nl_b, ns_b, nr_b, mask_a, mask_b) in enumerate([
    (2, 1, 0, 3, 1, 0, True, True),    # Extra load
    (1, 2, 0, 1, 1, 0, True, True),    # Missing store
    (3, 2, 0, 3, 1, 0, True, True),    # Missing store
    (2, 1, 1, 2, 1, 0, True, True),    # Missing reduction
    (1, 1, 0, 1, 1, 1, True, True),    # Extra reduction
    (4, 1, 0, 3, 1, 0, True, True),    # Different load counts
    (2, 3, 0, 2, 2, 0, True, True),    # Different store counts
    (1, 1, 2, 1, 1, 1, True, True),    # Different reduction counts
    (2, 1, 0, 2, 1, 0, True, False),   # Masked vs unmasked
    (3, 2, 1, 3, 2, 1, True, False),   # Masked vs unmasked (complex)
], start=11):
    def _gen_kernel(nl, ns, nr, masked, suffix):
        params = ", ".join([f"x{j}" for j in range(nl)] +
                          [f"o{j}" for j in range(ns)] + ["N: tl.constexpr"])
        mask_line = "\n    m = off < N" if masked else ""
        m_arg = ", mask=m" if masked else ""
        loads = "\n    ".join(f"v{j} = tl.load(x{j} + off{m_arg})" for j in range(nl))
        red_input = "v0"
        reds = "\n    ".join(f"r{j} = tl.sum({red_input}, axis=0)" for j in range(nr))
        store_val = "r0" if nr > 0 else "v0"
        stores = "\n    ".join(
            f"tl.store(o{j} + {'pid' if nr > 0 else 'off'}, {store_val}{m_arg if nr == 0 else ''})"
            for j in range(ns))
        return f"""
import triton, triton.language as tl
@triton.jit
def k{suffix}({params}):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE){mask_line}
    {loads}
    {reds}
    {stores}
"""
    TRITON_NEQ.append((
        f"neq_t{i}_L{nl_a}S{ns_a}R{nr_a}_vs_L{nl_b}S{ns_b}R{nr_b}_M{int(mask_a)}{int(mask_b)}",
        _gen_kernel(nl_a, ns_a, nr_a, mask_a, "_a"),
        _gen_kernel(nl_b, ns_b, nr_b, mask_b, "_b"),
    ))

# -- 21-30: Subtle differences in masking patterns ----------------------
for i in range(21, 31):
    # First kernel: all loads masked, second: first load unmasked
    n_loads = 2 + (i % 3)
    loads_a = "\n    ".join(f"v{j} = tl.load(x{j} + off, mask=m)" for j in range(n_loads))
    loads_b_parts = [f"v0 = tl.load(x0 + off)"]  # First load unmasked
    loads_b_parts += [f"v{j} = tl.load(x{j} + off, mask=m)" for j in range(1, n_loads)]
    loads_b = "\n    ".join(loads_b_parts)
    params = ", ".join([f"x{j}" for j in range(n_loads)] + ["o", "N: tl.constexpr"])

    TRITON_NEQ.append((f"neq_t{i}_mask_pattern_L{n_loads}", f"""
import triton, triton.language as tl
@triton.jit
def k({params}):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    {loads_a}
    tl.store(o + off, v0, mask=m)
""", f"""
import triton, triton.language as tl
@triton.jit
def k({params}):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    {loads_b}
    tl.store(o + off, v0, mask=m)
"""))

# -- 31-40: Different reduction operations (subtle) ---------------------
_RED_OPS = ["sum", "max", "min"]
for i in range(31, 41):
    op_a = _RED_OPS[i % 3]
    op_b = _RED_OPS[(i + 1) % 3]
    TRITON_NEQ.append((f"neq_t{i}_{op_a}_vs_{op_b}", f"""
import triton, triton.language as tl
@triton.jit
def k(x, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    r = tl.{op_a}(v, axis=0)
    tl.store(out + pid, r)
""", f"""
import triton, triton.language as tl
@triton.jit
def k(x, out, N: tl.constexpr):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    v = tl.load(x + off, mask=m)
    r = tl.{op_b}(v, axis=0)
    tl.store(out + pid, r)
"""))

# -- 41-50: Store masked vs unmasked -----------------------------------
for i in range(41, 51):
    n_loads = 1 + (i % 3)
    loads = "\n    ".join(f"v{j} = tl.load(x{j} + off, mask=m)" for j in range(n_loads))
    params = ", ".join([f"x{j}" for j in range(n_loads)] + ["o", "N: tl.constexpr"])

    TRITON_NEQ.append((f"neq_t{i}_store_mask_L{n_loads}", f"""
import triton, triton.language as tl
@triton.jit
def k({params}):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    {loads}
    tl.store(o + off, v0, mask=m)
""", f"""
import triton, triton.language as tl
@triton.jit
def k({params}):
    pid = tl.program_id(0)
    BLOCK_SIZE: tl.constexpr = 256
    off = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    m = off < N
    {loads}
    tl.store(o + off, v0)
"""))


# ═══════════════════════════════════════════════════════════════════════
#  MLIR EQUIVALENT PAIRS (50 pairs)
# ═══════════════════════════════════════════════════════════════════════

MLIR_EQ: List[Tuple[str, str, str]] = []

# -- 1-5: Renamed variables / functions --------------------------------
MLIR_EQ.append(("eq_m01_rename_func", """
module {
  func.func @add(%arg0: tensor<4xf32>, %arg1: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.addf %arg0, %arg1 : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
""", """
module {
  func.func @vector_addition(%x: tensor<4xf32>, %y: tensor<4xf32>) -> tensor<4xf32> {
    %result = arith.addf %x, %y : tensor<4xf32>
    return %result : tensor<4xf32>
  }
}
"""))

MLIR_EQ.append(("eq_m02_rename_mul", """
module {
  func.func @mul(%a: tensor<8xf32>, %b: tensor<8xf32>) -> tensor<8xf32> {
    %0 = arith.mulf %a, %b : tensor<8xf32>
    return %0 : tensor<8xf32>
  }
}
""", """
module {
  func.func @elementwise_product(%input_x: tensor<8xf32>, %input_y: tensor<8xf32>) -> tensor<8xf32> {
    %product = arith.mulf %input_x, %input_y : tensor<8xf32>
    return %product : tensor<8xf32>
  }
}
"""))

MLIR_EQ.append(("eq_m03_rename_sub", """
module {
  func.func @sub(%p: tensor<16xf64>, %q: tensor<16xf64>) -> tensor<16xf64> {
    %0 = arith.subf %p, %q : tensor<16xf64>
    return %0 : tensor<16xf64>
  }
}
""", """
module {
  func.func @difference(%alpha: tensor<16xf64>, %beta: tensor<16xf64>) -> tensor<16xf64> {
    %diff = arith.subf %alpha, %beta : tensor<16xf64>
    return %diff : tensor<16xf64>
  }
}
"""))

# -- 4-5: Different type annotations (same op) -------------------------
MLIR_EQ.append(("eq_m04_type_f32_vs_f64", """
module {
  func.func @f(%arg0: tensor<4xf32>, %arg1: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.addf %arg0, %arg1 : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
""", """
module {
  func.func @f(%arg0: tensor<4xf64>, %arg1: tensor<4xf64>) -> tensor<4xf64> {
    %0 = arith.addf %arg0, %arg1 : tensor<4xf64>
    return %0 : tensor<4xf64>
  }
}
"""))

MLIR_EQ.append(("eq_m05_type_i32_vs_i64", """
module {
  func.func @f(%arg0: tensor<8xi32>, %arg1: tensor<8xi32>) -> tensor<8xi32> {
    %0 = arith.addi %arg0, %arg1 : tensor<8xi32>
    return %0 : tensor<8xi32>
  }
}
""", """
module {
  func.func @f(%arg0: tensor<8xi64>, %arg1: tensor<8xi64>) -> tensor<8xi64> {
    %0 = arith.addi %arg0, %arg1 : tensor<8xi64>
    return %0 : tensor<8xi64>
  }
}
"""))

# -- 6-10: Different module names / comments ----------------------------
MLIR_EQ.append(("eq_m06_module_name", """
module @my_module {
  func.func @f(%a: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.negf %a : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
""", """
module @different_name {
  func.func @g(%x: tensor<4xf32>) -> tensor<4xf32> {
    %result = arith.negf %x : tensor<4xf32>
    return %result : tensor<4xf32>
  }
}
"""))

MLIR_EQ.append(("eq_m07_comments", """
module {
  // This is module A
  func.func @f(%arg0: tensor<4xf32>, %arg1: tensor<4xf32>) -> tensor<4xf32> {
    // Add the tensors
    %0 = arith.addf %arg0, %arg1 : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
""", """
module {
  func.func @f(%arg0: tensor<4xf32>, %arg1: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.addf %arg0, %arg1 : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
"""))

# -- 8-10: Different shapes (same ops) ---------------------------------
for i, shape in enumerate(["2x2xf32", "16x16xf32", "1024xf32"], start=8):
    MLIR_EQ.append((f"eq_m{i:02d}_shape_{shape.replace('x','_')}", f"""
module {{
  func.func @f(%a: tensor<{shape}>, %b: tensor<{shape}>) -> tensor<{shape}> {{
    %0 = arith.addf %a, %b : tensor<{shape}>
    return %0 : tensor<{shape}>
  }}
}}
""", f"""
module {{
  func.func @g(%x: tensor<{shape}>, %y: tensor<{shape}>) -> tensor<{shape}> {{
    %r = arith.addf %x, %y : tensor<{shape}>
    return %r : tensor<{shape}>
  }}
}}
"""))

# -- 11-25: Systematic op equivalences ---------------------------------
_MLIR_OPS = [
    ("arith", "addf"), ("arith", "mulf"), ("arith", "subf"),
    ("arith", "divf"), ("arith", "negf"), ("arith", "addi"),
    ("arith", "muli"), ("arith", "subi"), ("arith", "andi"),
    ("arith", "ori"), ("arith", "xori"), ("arith", "maxf"),
    ("arith", "minf"), ("arith", "cmpf"), ("arith", "cmpi"),
]

for i, (dialect, op) in enumerate(_MLIR_OPS, start=11):
    n_operands = 1 if op in ("negf",) else 2
    if n_operands == 1:
        mlir_a = f"""
module {{
  func.func @f(%arg0: tensor<4xf32>) -> tensor<4xf32> {{
    %0 = {dialect}.{op} %arg0 : tensor<4xf32>
    return %0 : tensor<4xf32>
  }}
}}
"""
        mlir_b = f"""
module {{
  func.func @g(%x: tensor<4xf32>) -> tensor<4xf32> {{
    %r = {dialect}.{op} %x : tensor<4xf32>
    return %r : tensor<4xf32>
  }}
}}
"""
    else:
        mlir_a = f"""
module {{
  func.func @f(%arg0: tensor<4xf32>, %arg1: tensor<4xf32>) -> tensor<4xf32> {{
    %0 = {dialect}.{op} %arg0, %arg1 : tensor<4xf32>
    return %0 : tensor<4xf32>
  }}
}}
"""
        mlir_b = f"""
module {{
  func.func @g(%x: tensor<4xf32>, %y: tensor<4xf32>) -> tensor<4xf32> {{
    %r = {dialect}.{op} %x, %y : tensor<4xf32>
    return %r : tensor<4xf32>
  }}
}}
"""
    MLIR_EQ.append((f"eq_m{i:02d}_{dialect}_{op}", mlir_a, mlir_b))

# -- 26-35: Multi-op sequences (same ops, different names) ---------------
for i in range(26, 36):
    n_ops = 2 + (i % 4)
    ops_list = [_MLIR_OPS[j % len(_MLIR_OPS)] for j in range(n_ops)]
    # Filter to only binary ops for simplicity
    ops_list = [(d, o) for d, o in ops_list if o not in ("negf",)][:n_ops]
    if not ops_list:
        ops_list = [("arith", "addf")]

    lines_a = []
    lines_b = []
    prev_a = "%arg0"
    prev_b = "%x"
    for j, (d, o) in enumerate(ops_list):
        lines_a.append(f"    %t{j} = {d}.{o} {prev_a}, %arg1 : tensor<4xf32>")
        lines_b.append(f"    %r{j} = {d}.{o} {prev_b}, %y : tensor<4xf32>")
        prev_a = f"%t{j}"
        prev_b = f"%r{j}"

    MLIR_EQ.append((f"eq_m{i:02d}_chain_{n_ops}ops", f"""
module {{
  func.func @f(%arg0: tensor<4xf32>, %arg1: tensor<4xf32>) -> tensor<4xf32> {{
{chr(10).join(lines_a)}
    return {prev_a} : tensor<4xf32>
  }}
}}
""", f"""
module {{
  func.func @g(%x: tensor<4xf32>, %y: tensor<4xf32>) -> tensor<4xf32> {{
{chr(10).join(lines_b)}
    return {prev_b} : tensor<4xf32>
  }}
}}
"""))

# -- 36-40: Triton dialect equivalent pairs -----------------------------
MLIR_EQ.append(("eq_m36_tt_func_rename", """
module {
  tt.func @add_kernel(%arg0: !tt.ptr<f32>, %arg1: !tt.ptr<f32>, %arg2: !tt.ptr<f32>) {
    %0 = tt.get_program_id x : i32
    tt.return
  }
}
""", """
module {
  tt.func @vector_add(%ptr_x: !tt.ptr<f32>, %ptr_y: !tt.ptr<f32>, %ptr_out: !tt.ptr<f32>) {
    %pid = tt.get_program_id x : i32
    tt.return
  }
}
"""))

MLIR_EQ.append(("eq_m37_tt_two_ops", """
module {
  tt.func @k(%a: !tt.ptr<f32>, %b: !tt.ptr<f32>) {
    %0 = tt.get_program_id x : i32
    %1 = tt.get_program_id y : i32
    tt.return
  }
}
""", """
module {
  tt.func @kernel(%p: !tt.ptr<f32>, %q: !tt.ptr<f32>) {
    %pid_x = tt.get_program_id x : i32
    %pid_y = tt.get_program_id y : i32
    tt.return
  }
}
"""))

MLIR_EQ.append(("eq_m38_scf_rename", """
module {
  func.func @f(%arg0: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.addf %arg0, %arg0 : tensor<4xf32>
    %1 = arith.mulf %0, %arg0 : tensor<4xf32>
    return %1 : tensor<4xf32>
  }
}
""", """
module {
  func.func @g(%x: tensor<4xf32>) -> tensor<4xf32> {
    %doubled = arith.addf %x, %x : tensor<4xf32>
    %result = arith.mulf %doubled, %x : tensor<4xf32>
    return %result : tensor<4xf32>
  }
}
"""))

MLIR_EQ.append(("eq_m39_three_ops_rename", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.addf %a, %b : tensor<4xf32>
    %1 = arith.mulf %0, %a : tensor<4xf32>
    %2 = arith.subf %1, %b : tensor<4xf32>
    return %2 : tensor<4xf32>
  }
}
""", """
module {
  func.func @compute(%x: tensor<4xf32>, %y: tensor<4xf32>) -> tensor<4xf32> {
    %sum = arith.addf %x, %y : tensor<4xf32>
    %prod = arith.mulf %sum, %x : tensor<4xf32>
    %diff = arith.subf %prod, %y : tensor<4xf32>
    return %diff : tensor<4xf32>
  }
}
"""))

MLIR_EQ.append(("eq_m40_four_ops", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.addf %a, %b : tensor<4xf32>
    %1 = arith.mulf %a, %b : tensor<4xf32>
    %2 = arith.subf %0, %1 : tensor<4xf32>
    %3 = arith.divf %2, %a : tensor<4xf32>
    return %3 : tensor<4xf32>
  }
}
""", """
module {
  func.func @g(%x: tensor<4xf32>, %y: tensor<4xf32>) -> tensor<4xf32> {
    %sum = arith.addf %x, %y : tensor<4xf32>
    %prod = arith.mulf %x, %y : tensor<4xf32>
    %diff = arith.subf %sum, %prod : tensor<4xf32>
    %ratio = arith.divf %diff, %x : tensor<4xf32>
    return %ratio : tensor<4xf32>
  }
}
"""))

# -- 41-50: More MLIR equivalent patterns ------------------------------
for i in range(41, 51):
    n_ops = 1 + (i % 5)
    ops = [("arith", ["addf", "mulf", "subf", "divf", "addf"][j % 5]) for j in range(n_ops)]
    lines_a, lines_b = [], []
    prev_a, prev_b = "%arg0", "%x"
    for j, (d, o) in enumerate(ops):
        lines_a.append(f"    %v{j} = {d}.{o} {prev_a}, %arg1 : tensor<4xf32>")
        lines_b.append(f"    %w{j} = {d}.{o} {prev_b}, %y : tensor<4xf32>")
        prev_a, prev_b = f"%v{j}", f"%w{j}"
    MLIR_EQ.append((f"eq_m{i:02d}_chain_{n_ops}", f"""
module {{
  func.func @f(%arg0: tensor<4xf32>, %arg1: tensor<4xf32>) -> tensor<4xf32> {{
{chr(10).join(lines_a)}
    return {prev_a} : tensor<4xf32>
  }}
}}
""", f"""
module {{
  func.func @g(%x: tensor<4xf32>, %y: tensor<4xf32>) -> tensor<4xf32> {{
{chr(10).join(lines_b)}
    return {prev_b} : tensor<4xf32>
  }}
}}
"""))


# ═══════════════════════════════════════════════════════════════════════
#  MLIR NON-EQUIVALENT PAIRS (50 pairs)
# ═══════════════════════════════════════════════════════════════════════

MLIR_NEQ: List[Tuple[str, str, str]] = []

# -- 1-5: Different operations -----------------------------------------
MLIR_NEQ.append(("neq_m01_addf_vs_mulf", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.addf %a, %b : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
""", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.mulf %a, %b : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
"""))

MLIR_NEQ.append(("neq_m02_addf_vs_subf", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.addf %a, %b : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
""", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.subf %a, %b : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
"""))

MLIR_NEQ.append(("neq_m03_mulf_vs_divf", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.mulf %a, %b : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
""", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.divf %a, %b : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
"""))

MLIR_NEQ.append(("neq_m04_addi_vs_muli", """
module {
  func.func @f(%a: tensor<4xi32>, %b: tensor<4xi32>) -> tensor<4xi32> {
    %0 = arith.addi %a, %b : tensor<4xi32>
    return %0 : tensor<4xi32>
  }
}
""", """
module {
  func.func @f(%a: tensor<4xi32>, %b: tensor<4xi32>) -> tensor<4xi32> {
    %0 = arith.muli %a, %b : tensor<4xi32>
    return %0 : tensor<4xi32>
  }
}
"""))

MLIR_NEQ.append(("neq_m05_maxf_vs_minf", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.maxf %a, %b : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
""", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.minf %a, %b : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
"""))

# -- 6-10: Extra operations ---------------------------------------------
MLIR_NEQ.append(("neq_m06_extra_op", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.addf %a, %b : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
""", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.addf %a, %b : tensor<4xf32>
    %1 = arith.negf %0 : tensor<4xf32>
    return %1 : tensor<4xf32>
  }
}
"""))

MLIR_NEQ.append(("neq_m07_missing_op", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.addf %a, %b : tensor<4xf32>
    %1 = arith.mulf %0, %a : tensor<4xf32>
    return %1 : tensor<4xf32>
  }
}
""", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.addf %a, %b : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
"""))

MLIR_NEQ.append(("neq_m08_extra_two_ops", """
module {
  func.func @f(%a: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.negf %a : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
""", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.addf %a, %b : tensor<4xf32>
    %1 = arith.mulf %0, %a : tensor<4xf32>
    %2 = arith.negf %1 : tensor<4xf32>
    return %2 : tensor<4xf32>
  }
}
"""))

MLIR_NEQ.append(("neq_m09_different_chain", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.addf %a, %b : tensor<4xf32>
    %1 = arith.addf %0, %a : tensor<4xf32>
    return %1 : tensor<4xf32>
  }
}
""", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.addf %a, %b : tensor<4xf32>
    %1 = arith.mulf %0, %a : tensor<4xf32>
    return %1 : tensor<4xf32>
  }
}
"""))

MLIR_NEQ.append(("neq_m10_swapped_op_type", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.addf %a, %b : tensor<4xf32>
    %1 = arith.mulf %0, %b : tensor<4xf32>
    return %1 : tensor<4xf32>
  }
}
""", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.mulf %a, %b : tensor<4xf32>
    %1 = arith.addf %0, %b : tensor<4xf32>
    return %1 : tensor<4xf32>
  }
}
"""))

# -- 11-15: Different function count -----------------------------------
MLIR_NEQ.append(("neq_m11_one_vs_two_funcs", """
module {
  func.func @f(%a: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.negf %a : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
""", """
module {
  func.func @f(%a: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.negf %a : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
  func.func @g(%a: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.negf %a : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
"""))

for i in range(12, 16):
    n_funcs_a = 1
    n_funcs_b = 2 + (i % 3)
    funcs_a = """
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.addf %a, %b : tensor<4xf32>
    return %0 : tensor<4xf32>
  }"""
    funcs_b = "\n".join(f"""
  func.func @f{j}(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {{
    %0 = arith.addf %a, %b : tensor<4xf32>
    return %0 : tensor<4xf32>
  }}""" for j in range(n_funcs_b))
    MLIR_NEQ.append((f"neq_m{i:02d}_{n_funcs_a}_vs_{n_funcs_b}_funcs", f"""
module {{{funcs_a}
}}
""", f"""
module {{{funcs_b}
}}
"""))

# -- 16-20: Different dialects -----------------------------------------
MLIR_NEQ.append(("neq_m16_arith_vs_tt", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.addf %a, %b : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
""", """
module {
  tt.func @f(%a: !tt.ptr<f32>, %b: !tt.ptr<f32>) {
    %0 = tt.get_program_id x : i32
    tt.return
  }
}
"""))

MLIR_NEQ.append(("neq_m17_arith_vs_memref", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.addf %a, %b : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
""", """
module {
  func.func @f(%a: memref<4xf32>, %b: memref<4xf32>) -> memref<4xf32> {
    %0 = memref.alloc() : memref<4xf32>
    return %0 : memref<4xf32>
  }
}
"""))

MLIR_NEQ.append(("neq_m18_tt_vs_ttg", """
module {
  tt.func @k(%a: !tt.ptr<f32>) {
    %0 = tt.get_program_id x : i32
    tt.return
  }
}
""", """
module {
  tt.func @k(%a: !tt.ptr<f32>) {
    %0 = tt.get_program_id x : i32
    %1 = ttg.local_alloc : () -> !ttg.memdesc<128xf32>
    tt.return
  }
}
"""))

MLIR_NEQ.append(("neq_m19_arith_vs_linalg", """
module {
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.addf %a, %b : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
""", """
module {
  func.func @f(%a: tensor<4x4xf32>, %b: tensor<4x4xf32>) -> tensor<4x4xf32> {
    %0 = linalg.matmul ins(%a, %b : tensor<4x4xf32>, tensor<4x4xf32>) outs(%a : tensor<4x4xf32>) -> tensor<4x4xf32>
    return %0 : tensor<4x4xf32>
  }
}
"""))

MLIR_NEQ.append(("neq_m20_scf_vs_arith", """
module {
  func.func @f(%a: tensor<4xf32>) -> tensor<4xf32> {
    %0 = arith.negf %a : tensor<4xf32>
    return %0 : tensor<4xf32>
  }
}
""", """
module {
  func.func @f(%a: tensor<4xf32>, %n: index) -> tensor<4xf32> {
    %c0 = arith.constant 0 : index
    %c1 = arith.constant 1 : index
    %0 = scf.for %i = %c0 to %n step %c1 iter_args(%acc = %a) -> tensor<4xf32> {
      scf.yield %acc : tensor<4xf32>
    }
    return %0 : tensor<4xf32>
  }
}
"""))

# -- 21-35: Systematic single-op differences ---------------------------
_OP_PAIRS = [
    ("addf", "subf"), ("mulf", "divf"), ("addf", "mulf"),
    ("subf", "divf"), ("addf", "divf"), ("mulf", "subf"),
    ("addi", "subi"), ("muli", "addi"), ("andi", "ori"),
    ("xori", "andi"), ("addf", "maxf"), ("addf", "minf"),
    ("maxf", "minf"), ("mulf", "maxf"), ("subf", "minf"),
]

for i, (op_a, op_b) in enumerate(_OP_PAIRS, start=21):
    MLIR_NEQ.append((f"neq_m{i:02d}_{op_a}_vs_{op_b}", f"""
module {{
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {{
    %0 = arith.{op_a} %a, %b : tensor<4xf32>
    return %0 : tensor<4xf32>
  }}
}}
""", f"""
module {{
  func.func @f(%a: tensor<4xf32>, %b: tensor<4xf32>) -> tensor<4xf32> {{
    %0 = arith.{op_b} %a, %b : tensor<4xf32>
    return %0 : tensor<4xf32>
  }}
}}
"""))

# -- 36-45: Different op counts in multi-op chains ----------------------
for i in range(36, 46):
    n_a = 2 + (i % 3)
    n_b = n_a + 1
    ops_a, ops_b = [], []
    prev_a, prev_b = "%arg0", "%arg0"
    for j in range(n_a):
        ops_a.append(f"    %t{j} = arith.addf {prev_a}, %arg1 : tensor<4xf32>")
        prev_a = f"%t{j}"
    for j in range(n_b):
        ops_b.append(f"    %t{j} = arith.addf {prev_b}, %arg1 : tensor<4xf32>")
        prev_b = f"%t{j}"
    MLIR_NEQ.append((f"neq_m{i:02d}_chain_{n_a}_vs_{n_b}", f"""
module {{
  func.func @f(%arg0: tensor<4xf32>, %arg1: tensor<4xf32>) -> tensor<4xf32> {{
{chr(10).join(ops_a)}
    return {prev_a} : tensor<4xf32>
  }}
}}
""", f"""
module {{
  func.func @f(%arg0: tensor<4xf32>, %arg1: tensor<4xf32>) -> tensor<4xf32> {{
{chr(10).join(ops_b)}
    return {prev_b} : tensor<4xf32>
  }}
}}
"""))

# -- 46-50: Subtle op sequence differences (same count, different ops) --
_CHAIN_DIFFS = [
    (["addf", "mulf"], ["mulf", "addf"]),
    (["addf", "addf"], ["addf", "mulf"]),
    (["mulf", "subf"], ["mulf", "addf"]),
    (["addf", "mulf", "subf"], ["addf", "mulf", "divf"]),
    (["addf", "subf", "mulf"], ["addf", "mulf", "subf"]),
]

for i, (chain_a, chain_b) in enumerate(_CHAIN_DIFFS, start=46):
    ops_a, ops_b = [], []
    prev_a, prev_b = "%arg0", "%arg0"
    for j, op in enumerate(chain_a):
        ops_a.append(f"    %t{j} = arith.{op} {prev_a}, %arg1 : tensor<4xf32>")
        prev_a = f"%t{j}"
    for j, op in enumerate(chain_b):
        ops_b.append(f"    %t{j} = arith.{op} {prev_b}, %arg1 : tensor<4xf32>")
        prev_b = f"%t{j}"
    MLIR_NEQ.append((f"neq_m{i:02d}_chain_diff_{i}", f"""
module {{
  func.func @f(%arg0: tensor<4xf32>, %arg1: tensor<4xf32>) -> tensor<4xf32> {{
{chr(10).join(ops_a)}
    return {prev_a} : tensor<4xf32>
  }}
}}
""", f"""
module {{
  func.func @f(%arg0: tensor<4xf32>, %arg1: tensor<4xf32>) -> tensor<4xf32> {{
{chr(10).join(ops_b)}
    return {prev_b} : tensor<4xf32>
  }}
}}
"""))


# ═══════════════════════════════════════════════════════════════════════
#  TEST HARNESS
# ═══════════════════════════════════════════════════════════════════════

class TestTritonEquivalent(unittest.TestCase):
    """All 50 Triton equivalent pairs must be judged EQUIVALENT."""

    @classmethod
    def setUpClass(cls):
        cls.checker = TritonEquivalenceChecker(TensorEquivalenceConfig())

    def _check_eq(self, name: str, src_a: str, src_b: str):
        spec_a = build_kernel_spec(src_a, name=f"{name}_a")
        spec_b = build_kernel_spec(src_b, name=f"{name}_b")
        j = self.checker.check_site(spec_a, spec_b, _sid(name))
        self.assertEqual(
            j.verdict, EquivalenceVerdict.EQUIVALENT,
            f"{name}: expected EQUIVALENT, got {j.verdict}: {j.explanation}"
        )


for _name, _src_a, _src_b in TRITON_EQ:
    def _make_test(n=_name, a=_src_a, b=_src_b):
        def test(self):
            self._check_eq(n, a, b)
        return test
    setattr(TestTritonEquivalent, f"test_{_name}", _make_test())


class TestTritonNonEquivalent(unittest.TestCase):
    """All 50 Triton non-equivalent pairs must be judged INEQUIVALENT."""

    @classmethod
    def setUpClass(cls):
        cls.checker = TritonEquivalenceChecker(TensorEquivalenceConfig())

    def _check_neq(self, name: str, src_a: str, src_b: str):
        spec_a = build_kernel_spec(src_a, name=f"{name}_a")
        spec_b = build_kernel_spec(src_b, name=f"{name}_b")
        j = self.checker.check_site(spec_a, spec_b, _sid(name))
        self.assertEqual(
            j.verdict, EquivalenceVerdict.INEQUIVALENT,
            f"{name}: expected INEQUIVALENT, got {j.verdict}: {j.explanation}"
        )


for _name, _src_a, _src_b in TRITON_NEQ:
    def _make_test(n=_name, a=_src_a, b=_src_b):
        def test(self):
            self._check_neq(n, a, b)
        return test
    setattr(TestTritonNonEquivalent, f"test_{_name}", _make_test())


class TestMLIREquivalent(unittest.TestCase):
    """All 50 MLIR equivalent pairs must be judged EQUIVALENT."""

    @classmethod
    def setUpClass(cls):
        cls.checker = MLIREquivalenceChecker(TensorEquivalenceConfig())

    def _check_eq(self, name: str, src_a: str, src_b: str):
        spec_a = build_mlir_module_spec(src_a, name=f"{name}_a")
        spec_b = build_mlir_module_spec(src_b, name=f"{name}_b")
        j = self.checker.check_site(spec_a, spec_b, _sid(name))
        self.assertEqual(
            j.verdict, EquivalenceVerdict.EQUIVALENT,
            f"{name}: expected EQUIVALENT, got {j.verdict}: {j.explanation}"
        )


for _name, _src_a, _src_b in MLIR_EQ:
    def _make_test(n=_name, a=_src_a, b=_src_b):
        def test(self):
            self._check_eq(n, a, b)
        return test
    setattr(TestMLIREquivalent, f"test_{_name}", _make_test())


class TestMLIRNonEquivalent(unittest.TestCase):
    """All 50 MLIR non-equivalent pairs must be judged INEQUIVALENT."""

    @classmethod
    def setUpClass(cls):
        cls.checker = MLIREquivalenceChecker(TensorEquivalenceConfig())

    def _check_neq(self, name: str, src_a: str, src_b: str):
        spec_a = build_mlir_module_spec(src_a, name=f"{name}_a")
        spec_b = build_mlir_module_spec(src_b, name=f"{name}_b")
        j = self.checker.check_site(spec_a, spec_b, _sid(name))
        self.assertEqual(
            j.verdict, EquivalenceVerdict.INEQUIVALENT,
            f"{name}: expected INEQUIVALENT, got {j.verdict}: {j.explanation}"
        )


for _name, _src_a, _src_b in MLIR_NEQ:
    def _make_test(n=_name, a=_src_a, b=_src_b):
        def test(self):
            self._check_neq(n, a, b)
        return test
    setattr(TestMLIRNonEquivalent, f"test_{_name}", _make_test())


# ═══════════════════════════════════════════════════════════════════════
#  F1 SCORE COMPUTATION
# ═══════════════════════════════════════════════════════════════════════

class TestF1Score(unittest.TestCase):
    """Compute overall F1 score across all 200 pairs."""

    def test_f1_equals_one(self):
        triton_checker = TritonEquivalenceChecker(TensorEquivalenceConfig())
        mlir_checker = MLIREquivalenceChecker(TensorEquivalenceConfig())

        tp = fp = tn = fn = 0

        # Triton equivalent (positive = equivalent)
        for name, src_a, src_b in TRITON_EQ:
            spec_a = build_kernel_spec(src_a)
            spec_b = build_kernel_spec(src_b)
            j = triton_checker.check_site(spec_a, spec_b, _sid(name))
            if j.verdict == EquivalenceVerdict.EQUIVALENT:
                tp += 1
            else:
                fn += 1

        # Triton non-equivalent (negative = inequivalent)
        for name, src_a, src_b in TRITON_NEQ:
            spec_a = build_kernel_spec(src_a)
            spec_b = build_kernel_spec(src_b)
            j = triton_checker.check_site(spec_a, spec_b, _sid(name))
            if j.verdict == EquivalenceVerdict.INEQUIVALENT:
                tn += 1
            else:
                fp += 1

        # MLIR equivalent
        for name, src_a, src_b in MLIR_EQ:
            spec_a = build_mlir_module_spec(src_a)
            spec_b = build_mlir_module_spec(src_b)
            j = mlir_checker.check_site(spec_a, spec_b, _sid(name))
            if j.verdict == EquivalenceVerdict.EQUIVALENT:
                tp += 1
            else:
                fn += 1

        # MLIR non-equivalent
        for name, src_a, src_b in MLIR_NEQ:
            spec_a = build_mlir_module_spec(src_a)
            spec_b = build_mlir_module_spec(src_b)
            j = mlir_checker.check_site(spec_a, spec_b, _sid(name))
            if j.verdict == EquivalenceVerdict.INEQUIVALENT:
                tn += 1
            else:
                fp += 1

        total = tp + fp + tn + fn
        precision = tp / (tp + fp) if (tp + fp) > 0 else 0.0
        recall = tp / (tp + fn) if (tp + fn) > 0 else 0.0
        f1 = 2 * precision * recall / (precision + recall) if (precision + recall) > 0 else 0.0

        print(f"\n{'='*60}")
        print(f"  BENCHMARK RESULTS: {total} pairs")
        print(f"  TP={tp}  FP={fp}  TN={tn}  FN={fn}")
        print(f"  Precision={precision:.4f}  Recall={recall:.4f}  F1={f1:.4f}")
        print(f"{'='*60}")

        self.assertEqual(f1, 1.0, f"F1={f1:.4f} (TP={tp}, FP={fp}, TN={tn}, FN={fn})")


if __name__ == "__main__":
    # Print pair counts
    print(f"Triton equivalent: {len(TRITON_EQ)} pairs")
    print(f"Triton non-equivalent: {len(TRITON_NEQ)} pairs")
    print(f"MLIR equivalent: {len(MLIR_EQ)} pairs")
    print(f"MLIR non-equivalent: {len(MLIR_NEQ)} pairs")
    print(f"Total: {len(TRITON_EQ) + len(TRITON_NEQ) + len(MLIR_EQ) + len(MLIR_NEQ)} pairs")
    unittest.main()
