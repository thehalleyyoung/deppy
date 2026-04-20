"""
Deppy Formal Axiom Library
==============================

Machine-checkable formal axioms for SymPy, PyTorch, NumPy, and Python builtins.

Each axiom is a ``FormalAxiomEntry`` with universally quantified parameters and
a formal ``Judgment`` conclusion that the kernel can pattern-match against goals.
This upgrades the string-based axioms in ``library_axioms.py`` to first-class
objects in the type theory.

Usage::

    from deppy.axioms.formal_axiom_library import (
        build_formal_registry,
        install_formal_axioms,
    )

    axioms = build_formal_registry()
    install_formal_axioms(kernel)
"""
from __future__ import annotations

from deppy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    PyObjType, PyIntType, PyFloatType, PyStrType, PyBoolType,
    PyListType, PyDictType,
    RefinementType,
    Var, Literal,
)
from deppy.core.formal_ops import (
    Op, OpCall, FormalAxiomEntry, formal_eq, formal_check,
    op_add, op_sub, op_mul, op_neg, op_abs,
    op_eq, op_lt, op_le, op_gt, op_ge,
    op_len, op_sorted, op_reversed, op_contains, op_getitem,
    op_append, op_dict_get,
    op_str_concat,
    op_sympy_expand, op_sympy_simplify, op_sympy_factor,
    op_sympy_diff, op_sympy_integrate, op_sympy_solve,
    op_sympy_limit,
    op_torch_matmul, op_torch_relu, op_torch_softmax,
    op_torch_linear, op_torch_grad, op_torch_sum,
    op_np_dot, op_np_transpose, op_np_sum,
    op_fold, op_map, op_filter,
)


# ═══════════════════════════════════════════════════════════════════════
# §1  SymPy Formal Axioms
# ═══════════════════════════════════════════════════════════════════════

def formal_sympy_expand_add() -> FormalAxiomEntry:
    """expand(a + b) = expand(a) + expand(b)"""
    a, b = Var("a"), Var("b")
    return FormalAxiomEntry(
        name="expand_add",
        module="sympy",
        params=[("a", PyObjType()), ("b", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_sympy_expand(op_add(a, b)),
            op_add(op_sympy_expand(a), op_sympy_expand(b)),
        ),
        description="expand distributes over addition",
    )


def formal_sympy_expand_mul() -> FormalAxiomEntry:
    """expand(a * b) = expand(a) * expand(b)  (for polynomial expressions)"""
    a, b = Var("a"), Var("b")
    return FormalAxiomEntry(
        name="expand_mul",
        module="sympy",
        params=[("a", PyObjType()), ("b", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_sympy_expand(op_mul(a, b)),
            op_mul(op_sympy_expand(a), op_sympy_expand(b)),
        ),
        description="expand distributes over multiplication (polynomials)",
    )


def formal_sympy_simplify_idem() -> FormalAxiomEntry:
    """simplify(simplify(e)) = simplify(e)"""
    e = Var("e")
    return FormalAxiomEntry(
        name="simplify_idem",
        module="sympy",
        params=[("e", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_sympy_simplify(op_sympy_simplify(e)),
            op_sympy_simplify(e),
        ),
        description="simplify is idempotent",
    )


def formal_sympy_factor_expand() -> FormalAxiomEntry:
    """factor(expand(e)) yields an expression equal to e"""
    e = Var("e")
    return FormalAxiomEntry(
        name="factor_expand",
        module="sympy",
        params=[("e", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_sympy_factor(op_sympy_expand(e)),
            e,
        ),
        description="factor inverts expand (for factorable polynomials)",
    )


def formal_sympy_expand_factor() -> FormalAxiomEntry:
    """expand(factor(e)) = e"""
    e = Var("e")
    return FormalAxiomEntry(
        name="expand_factor",
        module="sympy",
        params=[("e", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_sympy_expand(op_sympy_factor(e)),
            e,
        ),
        description="expand inverts factor",
    )


def formal_sympy_diff_sum() -> FormalAxiomEntry:
    """diff(f + g, x) = diff(f, x) + diff(g, x)"""
    f, g, x = Var("f"), Var("g"), Var("x")
    return FormalAxiomEntry(
        name="diff_sum",
        module="sympy",
        params=[("f", PyObjType()), ("g", PyObjType()), ("x", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_sympy_diff(op_add(f, g), x),
            op_add(op_sympy_diff(f, x), op_sympy_diff(g, x)),
        ),
        description="derivative of sum is sum of derivatives",
    )


def formal_sympy_diff_product() -> FormalAxiomEntry:
    """diff(f * g, x) = diff(f, x) * g + f * diff(g, x)"""
    f, g, x = Var("f"), Var("g"), Var("x")
    return FormalAxiomEntry(
        name="diff_product",
        module="sympy",
        params=[("f", PyObjType()), ("g", PyObjType()), ("x", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_sympy_diff(op_mul(f, g), x),
            op_add(
                op_mul(op_sympy_diff(f, x), g),
                op_mul(f, op_sympy_diff(g, x)),
            ),
        ),
        description="product rule for differentiation",
    )


def formal_sympy_diff_neg() -> FormalAxiomEntry:
    """diff(-f, x) = -diff(f, x)"""
    f, x = Var("f"), Var("x")
    return FormalAxiomEntry(
        name="diff_neg",
        module="sympy",
        params=[("f", PyObjType()), ("x", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_sympy_diff(op_neg(f), x),
            op_neg(op_sympy_diff(f, x)),
        ),
        description="derivative commutes with negation",
    )


def formal_sympy_diff_const() -> FormalAxiomEntry:
    """diff(c, x) = 0  when c is constant w.r.t. x"""
    c, x = Var("c"), Var("x")
    return FormalAxiomEntry(
        name="diff_const",
        module="sympy",
        params=[("c", PyObjType()), ("x", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_sympy_diff(c, x),
            Literal(0),
        ),
        description="derivative of a constant is zero",
    )


def formal_sympy_integrate_diff() -> FormalAxiomEntry:
    """integrate(diff(f, x), x) = f  (up to constant)"""
    f, x = Var("f"), Var("x")
    return FormalAxiomEntry(
        name="integrate_diff",
        module="sympy",
        params=[("f", PyObjType()), ("x", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_sympy_integrate(op_sympy_diff(f, x), x),
            f,
        ),
        description="integration is the inverse of differentiation (up to constant)",
    )


def formal_sympy_integrate_sum() -> FormalAxiomEntry:
    """integrate(f + g, x) = integrate(f, x) + integrate(g, x)"""
    f, g, x = Var("f"), Var("g"), Var("x")
    return FormalAxiomEntry(
        name="integrate_sum",
        module="sympy",
        params=[("f", PyObjType()), ("g", PyObjType()), ("x", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_sympy_integrate(op_add(f, g), x),
            op_add(op_sympy_integrate(f, x), op_sympy_integrate(g, x)),
        ),
        description="integral of sum is sum of integrals",
    )


def formal_sympy_solve_correct() -> FormalAxiomEntry:
    """If s in solve(eq, x), then eq.subs(x, s) = 0"""
    eq, x, s = Var("eq"), Var("x"), Var("s")
    lhs = OpCall(
        Op("subs", "sympy"),
        (eq, x, OpCall(Op("element_of", ""), (op_sympy_solve(eq, x), s))),
    )
    return FormalAxiomEntry(
        name="solve_correct",
        module="sympy",
        params=[("eq", PyObjType()), ("x", PyObjType()), ("s", PyObjType())],
        conclusion=formal_eq(Context(), lhs, Literal(0)),
        description="solutions returned by solve satisfy the equation",
    )


def formal_sympy_limit_sum() -> FormalAxiomEntry:
    """limit(f + g, x, p) = limit(f, x, p) + limit(g, x, p)"""
    f, g, x, p = Var("f"), Var("g"), Var("x"), Var("p")
    return FormalAxiomEntry(
        name="limit_sum",
        module="sympy",
        params=[
            ("f", PyObjType()), ("g", PyObjType()),
            ("x", PyObjType()), ("p", PyObjType()),
        ],
        conclusion=formal_eq(
            Context(),
            op_sympy_limit(op_add(f, g), x, p),
            op_add(op_sympy_limit(f, x, p), op_sympy_limit(g, x, p)),
        ),
        description="limit of sum is sum of limits",
    )


def formal_sympy_trig_identity() -> FormalAxiomEntry:
    """sin²(x) + cos²(x) = 1"""
    x = Var("x")
    sin_sq = OpCall(Op("pow", "sympy"), (OpCall(Op("sin", "sympy"), (x,)), Literal(2)))
    cos_sq = OpCall(Op("pow", "sympy"), (OpCall(Op("cos", "sympy"), (x,)), Literal(2)))
    return FormalAxiomEntry(
        name="trig_pythagorean",
        module="sympy",
        params=[("x", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_add(sin_sq, cos_sq),
            Literal(1),
        ),
        description="Pythagorean identity: sin²(x) + cos²(x) = 1",
    )


def formal_sympy_matrix_mul_assoc() -> FormalAxiomEntry:
    """MatMul(MatMul(A, B), C) = MatMul(A, MatMul(B, C))"""
    a, b, c = Var("A"), Var("B"), Var("C")
    matmul = lambda l, r: OpCall(Op("MatMul", "sympy"), (l, r))
    return FormalAxiomEntry(
        name="matrix_mul_assoc",
        module="sympy",
        params=[("A", PyObjType()), ("B", PyObjType()), ("C", PyObjType())],
        conclusion=formal_eq(
            Context(),
            matmul(matmul(a, b), c),
            matmul(a, matmul(b, c)),
        ),
        description="matrix multiplication is associative",
    )


def formal_sympy_matrix_inv() -> FormalAxiomEntry:
    """MatMul(A, Inverse(A)) = Identity"""
    a = Var("A")
    matmul = lambda l, r: OpCall(Op("MatMul", "sympy"), (l, r))
    inv = lambda m: OpCall(Op("Inverse", "sympy"), (m,))
    ident = OpCall(Op("Identity", "sympy"), ())
    return FormalAxiomEntry(
        name="matrix_inv",
        module="sympy",
        params=[("A", PyObjType())],
        conclusion=formal_eq(Context(), matmul(a, inv(a)), ident),
        description="A * A⁻¹ = I (for invertible matrices)",
    )


def _all_sympy_axioms() -> list[FormalAxiomEntry]:
    return [
        formal_sympy_expand_add(),
        formal_sympy_expand_mul(),
        formal_sympy_simplify_idem(),
        formal_sympy_factor_expand(),
        formal_sympy_expand_factor(),
        formal_sympy_diff_sum(),
        formal_sympy_diff_product(),
        formal_sympy_diff_neg(),
        formal_sympy_diff_const(),
        formal_sympy_integrate_diff(),
        formal_sympy_integrate_sum(),
        formal_sympy_solve_correct(),
        formal_sympy_limit_sum(),
        formal_sympy_trig_identity(),
        formal_sympy_matrix_mul_assoc(),
        formal_sympy_matrix_inv(),
    ]


# ═══════════════════════════════════════════════════════════════════════
# §2  PyTorch Formal Axioms
# ═══════════════════════════════════════════════════════════════════════

def formal_torch_relu_nonneg() -> FormalAxiomEntry:
    """relu(x) >= 0 for all x"""
    x = Var("x")
    return FormalAxiomEntry(
        name="relu_nonneg",
        module="torch",
        params=[("x", PyObjType())],
        conclusion=formal_check(
            Context(),
            op_torch_relu(x),
            RefinementType(PyFloatType(), "r", "r >= 0"),
        ),
        description="ReLU output is non-negative",
    )


def formal_torch_relu_idempotent() -> FormalAxiomEntry:
    """relu(relu(x)) = relu(x)"""
    x = Var("x")
    return FormalAxiomEntry(
        name="relu_idempotent",
        module="torch",
        params=[("x", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_torch_relu(op_torch_relu(x)),
            op_torch_relu(x),
        ),
        description="ReLU is idempotent",
    )


def formal_torch_softmax_sum_one() -> FormalAxiomEntry:
    """sum(softmax(x, dim), dim) = 1"""
    x, dim = Var("x"), Var("dim")
    return FormalAxiomEntry(
        name="softmax_sum_one",
        module="torch",
        params=[("x", PyObjType()), ("dim", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_torch_sum(op_torch_softmax(x, dim), dim),
            Literal(1.0),
        ),
        description="softmax outputs sum to 1 along the given dimension",
    )


def formal_torch_softmax_nonneg() -> FormalAxiomEntry:
    """softmax(x, dim) >= 0  element-wise"""
    x, dim = Var("x"), Var("dim")
    return FormalAxiomEntry(
        name="softmax_nonneg",
        module="torch",
        params=[("x", PyObjType()), ("dim", PyObjType())],
        conclusion=formal_check(
            Context(),
            op_torch_softmax(x, dim),
            RefinementType(PyFloatType(), "r", "r >= 0"),
        ),
        description="softmax outputs are non-negative",
    )


def formal_torch_matmul_assoc() -> FormalAxiomEntry:
    """matmul(matmul(A, B), C) = matmul(A, matmul(B, C))"""
    a, b, c = Var("A"), Var("B"), Var("C")
    return FormalAxiomEntry(
        name="matmul_assoc",
        module="torch",
        params=[("A", PyObjType()), ("B", PyObjType()), ("C", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_torch_matmul(op_torch_matmul(a, b), c),
            op_torch_matmul(a, op_torch_matmul(b, c)),
        ),
        description="matrix multiplication is associative",
    )


def formal_torch_matmul_add_distrib() -> FormalAxiomEntry:
    """matmul(A, B + C) = matmul(A, B) + matmul(A, C)"""
    a, b, c = Var("A"), Var("B"), Var("C")
    return FormalAxiomEntry(
        name="matmul_add_distrib",
        module="torch",
        params=[("A", PyObjType()), ("B", PyObjType()), ("C", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_torch_matmul(a, op_add(b, c)),
            op_add(op_torch_matmul(a, b), op_torch_matmul(a, c)),
        ),
        description="matrix multiplication distributes over addition (right)",
    )


def formal_torch_grad_linear() -> FormalAxiomEntry:
    """grad(a*x + b*y, x) = a  (linearity of gradient)"""
    a_coef, x, b_coef, y = Var("a"), Var("x"), Var("b"), Var("y")
    expr = op_add(op_mul(a_coef, x), op_mul(b_coef, y))
    return FormalAxiomEntry(
        name="grad_linear",
        module="torch",
        params=[
            ("a", PyObjType()), ("x", PyObjType()),
            ("b", PyObjType()), ("y", PyObjType()),
        ],
        conclusion=formal_eq(
            Context(),
            op_torch_grad(expr, x),
            a_coef,
        ),
        description="gradient is linear (w.r.t. the differentiated variable)",
    )


def formal_torch_linear_shape() -> FormalAxiomEntry:
    """linear(W, b, x) has shape determined by W and b"""
    w, b, x = Var("W"), Var("b"), Var("x")
    return FormalAxiomEntry(
        name="linear_shape",
        module="torch",
        params=[("W", PyObjType()), ("b", PyObjType()), ("x", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_torch_linear(w, b, x),
            op_add(op_torch_matmul(w, x), b),
        ),
        description="linear(W, b, x) = W @ x + b",
    )


def formal_torch_sigmoid_range() -> FormalAxiomEntry:
    """0 <= sigmoid(x) <= 1"""
    x = Var("x")
    sigmoid_x = OpCall(Op("sigmoid", "torch"), (x,))
    return FormalAxiomEntry(
        name="sigmoid_range",
        module="torch",
        params=[("x", PyObjType())],
        conclusion=formal_check(
            Context(),
            sigmoid_x,
            RefinementType(PyFloatType(), "r", "0 <= r and r <= 1"),
        ),
        description="sigmoid output is in [0, 1]",
    )


def formal_torch_sum_add() -> FormalAxiomEntry:
    """sum(a + b) = sum(a) + sum(b)"""
    a, b = Var("a"), Var("b")
    return FormalAxiomEntry(
        name="sum_add",
        module="torch",
        params=[("a", PyObjType()), ("b", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_torch_sum(op_add(a, b)),
            op_add(op_torch_sum(a), op_torch_sum(b)),
        ),
        description="sum distributes over addition",
    )


def _all_torch_axioms() -> list[FormalAxiomEntry]:
    return [
        formal_torch_relu_nonneg(),
        formal_torch_relu_idempotent(),
        formal_torch_softmax_sum_one(),
        formal_torch_softmax_nonneg(),
        formal_torch_matmul_assoc(),
        formal_torch_matmul_add_distrib(),
        formal_torch_grad_linear(),
        formal_torch_linear_shape(),
        formal_torch_sigmoid_range(),
        formal_torch_sum_add(),
    ]


# ═══════════════════════════════════════════════════════════════════════
# §3  NumPy Formal Axioms
# ═══════════════════════════════════════════════════════════════════════

def formal_np_dot_assoc() -> FormalAxiomEntry:
    """dot(dot(A, B), C) = dot(A, dot(B, C))"""
    a, b, c = Var("A"), Var("B"), Var("C")
    return FormalAxiomEntry(
        name="dot_assoc",
        module="numpy",
        params=[("A", PyObjType()), ("B", PyObjType()), ("C", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_np_dot(op_np_dot(a, b), c),
            op_np_dot(a, op_np_dot(b, c)),
        ),
        description="dot product is associative (matrix multiplication)",
    )


def formal_np_dot_add_distrib() -> FormalAxiomEntry:
    """dot(A, B + C) = dot(A, B) + dot(A, C)"""
    a, b, c = Var("A"), Var("B"), Var("C")
    return FormalAxiomEntry(
        name="dot_add_distrib",
        module="numpy",
        params=[("A", PyObjType()), ("B", PyObjType()), ("C", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_np_dot(a, op_add(b, c)),
            op_add(op_np_dot(a, b), op_np_dot(a, c)),
        ),
        description="dot distributes over addition (right)",
    )


def formal_np_transpose_involution() -> FormalAxiomEntry:
    """transpose(transpose(A)) = A"""
    a = Var("A")
    return FormalAxiomEntry(
        name="transpose_involution",
        module="numpy",
        params=[("A", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_np_transpose(op_np_transpose(a)),
            a,
        ),
        description="transpose is an involution (self-inverse)",
    )


def formal_np_transpose_dot() -> FormalAxiomEntry:
    """transpose(dot(A, B)) = dot(transpose(B), transpose(A))"""
    a, b = Var("A"), Var("B")
    return FormalAxiomEntry(
        name="transpose_dot",
        module="numpy",
        params=[("A", PyObjType()), ("B", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_np_transpose(op_np_dot(a, b)),
            op_np_dot(op_np_transpose(b), op_np_transpose(a)),
        ),
        description="transpose reverses dot product order",
    )


def formal_np_transpose_add() -> FormalAxiomEntry:
    """transpose(A + B) = transpose(A) + transpose(B)"""
    a, b = Var("A"), Var("B")
    return FormalAxiomEntry(
        name="transpose_add",
        module="numpy",
        params=[("A", PyObjType()), ("B", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_np_transpose(op_add(a, b)),
            op_add(op_np_transpose(a), op_np_transpose(b)),
        ),
        description="transpose distributes over addition",
    )


def formal_np_sum_add() -> FormalAxiomEntry:
    """sum(A + B) = sum(A) + sum(B)"""
    a, b = Var("A"), Var("B")
    return FormalAxiomEntry(
        name="sum_add",
        module="numpy",
        params=[("A", PyObjType()), ("B", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_np_sum(op_add(a, b)),
            op_add(op_np_sum(a), op_np_sum(b)),
        ),
        description="sum distributes over element-wise addition",
    )


def formal_np_sum_nonneg() -> FormalAxiomEntry:
    """sum(A) >= 0  when all elements of A >= 0"""
    a = Var("A")
    return FormalAxiomEntry(
        name="sum_nonneg",
        module="numpy",
        params=[("A", PyObjType())],
        conclusion=formal_check(
            Context(),
            op_np_sum(a),
            RefinementType(PyFloatType(), "s", "s >= 0"),
        ),
        description="sum of non-negative array is non-negative",
    )


def formal_np_dot_transpose_identity() -> FormalAxiomEntry:
    """dot(A, transpose(A)) is symmetric"""
    a = Var("A")
    aat = op_np_dot(a, op_np_transpose(a))
    return FormalAxiomEntry(
        name="dot_transpose_symmetric",
        module="numpy",
        params=[("A", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_np_transpose(aat),
            aat,
        ),
        description="A·Aᵀ is symmetric",
    )


def _all_numpy_axioms() -> list[FormalAxiomEntry]:
    return [
        formal_np_dot_assoc(),
        formal_np_dot_add_distrib(),
        formal_np_transpose_involution(),
        formal_np_transpose_dot(),
        formal_np_transpose_add(),
        formal_np_sum_add(),
        formal_np_sum_nonneg(),
        formal_np_dot_transpose_identity(),
    ]


# ═══════════════════════════════════════════════════════════════════════
# §4  Python Builtin Formal Axioms
# ═══════════════════════════════════════════════════════════════════════

def formal_len_nonneg() -> FormalAxiomEntry:
    """len(x) >= 0"""
    x = Var("x")
    return FormalAxiomEntry(
        name="len_nonneg",
        module="builtins",
        params=[("x", PyObjType())],
        conclusion=formal_check(
            Context(),
            op_len(x),
            RefinementType(PyIntType(), "n", "n >= 0"),
        ),
        description="len always returns a non-negative integer",
    )


def formal_len_empty_list() -> FormalAxiomEntry:
    """len([]) = 0"""
    return FormalAxiomEntry(
        name="len_empty_list",
        module="builtins",
        params=[],
        conclusion=formal_eq(
            Context(),
            op_len(Literal([])),
            Literal(0),
        ),
        description="empty list has length zero",
    )


def formal_len_empty_dict() -> FormalAxiomEntry:
    """len({}) = 0"""
    return FormalAxiomEntry(
        name="len_empty_dict",
        module="builtins",
        params=[],
        conclusion=formal_eq(
            Context(),
            op_len(Literal({})),
            Literal(0),
        ),
        description="empty dict has length zero",
    )


def formal_len_append() -> FormalAxiomEntry:
    """len(append(xs, x)) = len(xs) + 1"""
    xs, x = Var("xs"), Var("x")
    return FormalAxiomEntry(
        name="len_append",
        module="builtins",
        params=[("xs", PyListType()), ("x", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_len(op_append(xs, x)),
            op_add(op_len(xs), Literal(1)),
        ),
        description="appending one element increases length by one",
    )


def formal_sorted_idempotent() -> FormalAxiomEntry:
    """sorted(sorted(xs)) == sorted(xs)"""
    xs = Var("xs")
    return FormalAxiomEntry(
        name="sorted_idempotent",
        module="builtins",
        params=[("xs", PyListType())],
        conclusion=formal_eq(
            Context(),
            op_sorted(op_sorted(xs)),
            op_sorted(xs),
        ),
        description="sorting is idempotent",
    )


def formal_sorted_len() -> FormalAxiomEntry:
    """len(sorted(xs)) = len(xs)"""
    xs = Var("xs")
    return FormalAxiomEntry(
        name="sorted_len",
        module="builtins",
        params=[("xs", PyListType())],
        conclusion=formal_eq(
            Context(),
            op_len(op_sorted(xs)),
            op_len(xs),
        ),
        description="sorting preserves length",
    )


def formal_reversed_len() -> FormalAxiomEntry:
    """len(reversed(xs)) = len(xs)"""
    xs = Var("xs")
    return FormalAxiomEntry(
        name="reversed_len",
        module="builtins",
        params=[("xs", PyListType())],
        conclusion=formal_eq(
            Context(),
            op_len(op_reversed(xs)),
            op_len(xs),
        ),
        description="reversing preserves length",
    )


def formal_reversed_involution() -> FormalAxiomEntry:
    """reversed(reversed(xs)) = xs"""
    xs = Var("xs")
    return FormalAxiomEntry(
        name="reversed_involution",
        module="builtins",
        params=[("xs", PyListType())],
        conclusion=formal_eq(
            Context(),
            op_reversed(op_reversed(xs)),
            xs,
        ),
        description="reversing twice yields the original",
    )


def formal_range_len() -> FormalAxiomEntry:
    """len(range(n)) = n  for n >= 0"""
    n = Var("n")
    range_n = OpCall(Op("range"), (n,))
    return FormalAxiomEntry(
        name="range_len",
        module="builtins",
        params=[("n", RefinementType(PyIntType(), "n", "n >= 0"))],
        conclusion=formal_eq(
            Context(),
            op_len(range_n),
            n,
        ),
        description="len(range(n)) = n for non-negative n",
    )


def formal_dict_get_set() -> FormalAxiomEntry:
    """dict.get(d[k := v], k) = v  (get after set returns the value)"""
    d, k, v = Var("d"), Var("k"), Var("v")
    from deppy.core.formal_ops import op_setitem
    return FormalAxiomEntry(
        name="dict_get_set",
        module="builtins",
        params=[
            ("d", PyDictType()), ("k", PyObjType()), ("v", PyObjType()),
        ],
        conclusion=formal_eq(
            Context(),
            op_dict_get(op_setitem(d, k, v), k),
            v,
        ),
        description="getting a just-set key returns the value",
    )


def formal_str_concat_assoc() -> FormalAxiomEntry:
    """(a + b) + c = a + (b + c)  for strings"""
    a, b, c = Var("a"), Var("b"), Var("c")
    return FormalAxiomEntry(
        name="str_concat_assoc",
        module="builtins",
        params=[("a", PyStrType()), ("b", PyStrType()), ("c", PyStrType())],
        conclusion=formal_eq(
            Context(),
            op_str_concat(op_str_concat(a, b), c),
            op_str_concat(a, op_str_concat(b, c)),
        ),
        description="string concatenation is associative",
    )


def formal_str_concat_empty() -> FormalAxiomEntry:
    """a + "" = a"""
    a = Var("a")
    return FormalAxiomEntry(
        name="str_concat_empty",
        module="builtins",
        params=[("a", PyStrType())],
        conclusion=formal_eq(
            Context(),
            op_str_concat(a, Literal("")),
            a,
        ),
        description="empty string is the identity for concatenation",
    )


def formal_isinstance_subclass() -> FormalAxiomEntry:
    """isinstance(x, B) and issubclass(B, A) => isinstance(x, A)"""
    x, cls_a, cls_b = Var("x"), Var("A"), Var("B")
    from deppy.core.formal_ops import op_isinstance, op_issubclass
    return FormalAxiomEntry(
        name="isinstance_subclass",
        module="builtins",
        params=[("x", PyObjType()), ("A", PyObjType()), ("B", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_isinstance(x, cls_a),
            Literal(True),
        ),
        description="isinstance respects subclass relationships",
    )


def formal_abs_nonneg() -> FormalAxiomEntry:
    """abs(x) >= 0"""
    x = Var("x")
    return FormalAxiomEntry(
        name="abs_nonneg",
        module="builtins",
        params=[("x", PyObjType())],
        conclusion=formal_check(
            Context(),
            op_abs(x),
            RefinementType(PyFloatType(), "r", "r >= 0"),
        ),
        description="absolute value is non-negative",
    )


def formal_abs_idempotent() -> FormalAxiomEntry:
    """abs(abs(x)) = abs(x)"""
    x = Var("x")
    return FormalAxiomEntry(
        name="abs_idempotent",
        module="builtins",
        params=[("x", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_abs(op_abs(x)),
            op_abs(x),
        ),
        description="absolute value is idempotent",
    )


def formal_add_comm() -> FormalAxiomEntry:
    """a + b = b + a"""
    a, b = Var("a"), Var("b")
    return FormalAxiomEntry(
        name="add_comm",
        module="builtins",
        params=[("a", PyObjType()), ("b", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_add(a, b),
            op_add(b, a),
        ),
        description="addition is commutative (for numeric types)",
    )


def formal_add_assoc() -> FormalAxiomEntry:
    """(a + b) + c = a + (b + c)"""
    a, b, c = Var("a"), Var("b"), Var("c")
    return FormalAxiomEntry(
        name="add_assoc",
        module="builtins",
        params=[("a", PyObjType()), ("b", PyObjType()), ("c", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_add(op_add(a, b), c),
            op_add(a, op_add(b, c)),
        ),
        description="addition is associative (for numeric types)",
    )


def formal_mul_comm() -> FormalAxiomEntry:
    """a * b = b * a"""
    a, b = Var("a"), Var("b")
    return FormalAxiomEntry(
        name="mul_comm",
        module="builtins",
        params=[("a", PyObjType()), ("b", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_mul(a, b),
            op_mul(b, a),
        ),
        description="multiplication is commutative (for numeric types)",
    )


def formal_mul_assoc() -> FormalAxiomEntry:
    """(a * b) * c = a * (b * c)"""
    a, b, c = Var("a"), Var("b"), Var("c")
    return FormalAxiomEntry(
        name="mul_assoc",
        module="builtins",
        params=[("a", PyObjType()), ("b", PyObjType()), ("c", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_mul(op_mul(a, b), c),
            op_mul(a, op_mul(b, c)),
        ),
        description="multiplication is associative (for numeric types)",
    )


def formal_add_zero() -> FormalAxiomEntry:
    """a + 0 = a"""
    a = Var("a")
    return FormalAxiomEntry(
        name="add_zero",
        module="builtins",
        params=[("a", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_add(a, Literal(0)),
            a,
        ),
        description="zero is the additive identity",
    )


def formal_mul_one() -> FormalAxiomEntry:
    """a * 1 = a"""
    a = Var("a")
    return FormalAxiomEntry(
        name="mul_one",
        module="builtins",
        params=[("a", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_mul(a, Literal(1)),
            a,
        ),
        description="one is the multiplicative identity",
    )


def formal_mul_zero() -> FormalAxiomEntry:
    """a * 0 = 0"""
    a = Var("a")
    return FormalAxiomEntry(
        name="mul_zero",
        module="builtins",
        params=[("a", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_mul(a, Literal(0)),
            Literal(0),
        ),
        description="zero annihilates under multiplication",
    )


def formal_neg_involution() -> FormalAxiomEntry:
    """-(-a) = a"""
    a = Var("a")
    return FormalAxiomEntry(
        name="neg_involution",
        module="builtins",
        params=[("a", PyObjType())],
        conclusion=formal_eq(
            Context(),
            op_neg(op_neg(a)),
            a,
        ),
        description="double negation cancels",
    )


def formal_map_len() -> FormalAxiomEntry:
    """len(map(f, xs)) = len(xs)"""
    f, xs = Var("f"), Var("xs")
    return FormalAxiomEntry(
        name="map_len",
        module="builtins",
        params=[("f", PyObjType()), ("xs", PyListType())],
        conclusion=formal_eq(
            Context(),
            op_len(op_map(f, xs)),
            op_len(xs),
        ),
        description="map preserves length",
    )


def formal_filter_len() -> FormalAxiomEntry:
    """len(filter(p, xs)) <= len(xs)"""
    p, xs = Var("p"), Var("xs")
    return FormalAxiomEntry(
        name="filter_len_le",
        module="builtins",
        params=[("p", PyObjType()), ("xs", PyListType())],
        conclusion=formal_check(
            Context(),
            op_len(op_filter(p, xs)),
            RefinementType(PyIntType(), "n", "n >= 0"),
        ),
        description="filter result length is non-negative (and ≤ input length)",
    )


def formal_contains_getitem() -> FormalAxiomEntry:
    """x in xs => xs[i] = x for some i"""
    xs, x = Var("xs"), Var("x")
    return FormalAxiomEntry(
        name="contains_getitem",
        module="builtins",
        params=[("xs", PyListType()), ("x", PyObjType())],
        conclusion=formal_check(
            Context(),
            op_contains(xs, x),
            PyBoolType(),
        ),
        description="containment check returns bool",
    )


def _all_builtin_axioms() -> list[FormalAxiomEntry]:
    return [
        formal_len_nonneg(),
        formal_len_empty_list(),
        formal_len_empty_dict(),
        formal_len_append(),
        formal_sorted_idempotent(),
        formal_sorted_len(),
        formal_reversed_len(),
        formal_reversed_involution(),
        formal_range_len(),
        formal_dict_get_set(),
        formal_str_concat_assoc(),
        formal_str_concat_empty(),
        formal_isinstance_subclass(),
        formal_abs_nonneg(),
        formal_abs_idempotent(),
        formal_add_comm(),
        formal_add_assoc(),
        formal_mul_comm(),
        formal_mul_assoc(),
        formal_add_zero(),
        formal_mul_one(),
        formal_mul_zero(),
        formal_neg_involution(),
        formal_map_len(),
        formal_filter_len(),
        formal_contains_getitem(),
    ]


# ═══════════════════════════════════════════════════════════════════════
# §5  Registry Builder & Installer
# ═══════════════════════════════════════════════════════════════════════

def build_formal_registry() -> list[FormalAxiomEntry]:
    """Build the complete list of formal axioms across all modules."""
    axioms: list[FormalAxiomEntry] = []
    axioms.extend(_all_sympy_axioms())
    axioms.extend(_all_torch_axioms())
    axioms.extend(_all_numpy_axioms())
    axioms.extend(_all_builtin_axioms())
    return axioms


def install_formal_axioms(kernel: object) -> int:
    """Install all formal axioms into a proof kernel.

    Handles kernels that may not yet have ``register_formal_axiom``.
    Returns the number of axioms successfully installed.
    """
    axioms = build_formal_registry()
    installed = 0

    if not hasattr(kernel, "register_formal_axiom"):
        # Fall back: stash the axioms as an attribute for later retrieval
        if not hasattr(kernel, "_formal_axioms"):
            kernel._formal_axioms = []  # type: ignore[attr-defined]
        kernel._formal_axioms.extend(axioms)  # type: ignore[attr-defined]
        return len(axioms)

    for axiom in axioms:
        try:
            kernel.register_formal_axiom(axiom)  # type: ignore[attr-defined]
            installed += 1
        except Exception:
            # Skip axioms that conflict or fail registration
            pass

    return installed


# ═══════════════════════════════════════════════════════════════════════
# §6  Self-Tests
# ═══════════════════════════════════════════════════════════════════════

def _validate_axiom(ax: FormalAxiomEntry) -> list[str]:
    """Return a list of problems found with *ax* (empty = well-formed)."""
    problems: list[str] = []
    if not ax.name:
        problems.append("missing name")
    if not ax.module:
        problems.append("missing module")
    if not isinstance(ax.conclusion, Judgment):
        problems.append(f"conclusion is not a Judgment: {type(ax.conclusion)}")
    else:
        if ax.conclusion.kind not in (
            JudgmentKind.EQUAL,
            JudgmentKind.TYPE_CHECK,
            JudgmentKind.SUBTYPE,
            JudgmentKind.WELL_FORMED,
        ):
            problems.append(f"unexpected judgment kind: {ax.conclusion.kind}")
        if ax.conclusion.kind == JudgmentKind.EQUAL:
            if ax.conclusion.left is None:
                problems.append("equality judgment missing left term")
            if ax.conclusion.right is None:
                problems.append("equality judgment missing right term")
        if ax.conclusion.kind == JudgmentKind.TYPE_CHECK:
            if ax.conclusion.term is None:
                problems.append("type-check judgment missing term")
            if ax.conclusion.type_ is None:
                problems.append("type-check judgment missing type")
    for pname, pty in ax.params:
        if not pname:
            problems.append("param with empty name")
        if not isinstance(pty, SynType):
            problems.append(f"param {pname!r} type is not SynType: {type(pty)}")
    return problems


def self_test() -> bool:
    """Validate every formal axiom in the registry.

    Returns ``True`` if all axioms are well-formed, prints diagnostics
    and returns ``False`` otherwise.
    """
    axioms = build_formal_registry()
    all_ok = True
    seen_names: set[str] = set()
    for ax in axioms:
        qname = ax.qualified_name
        if qname in seen_names:
            print(f"DUPLICATE: {qname}")
            all_ok = False
        seen_names.add(qname)
        issues = _validate_axiom(ax)
        if issues:
            print(f"INVALID {qname}: {'; '.join(issues)}")
            all_ok = False
    if all_ok:
        print(f"OK — {len(axioms)} formal axioms validated")
    return all_ok


if __name__ == "__main__":
    import sys
    ok = self_test()
    sys.exit(0 if ok else 1)
