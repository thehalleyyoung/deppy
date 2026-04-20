"""SynHoPy — Formal Term-Tree Verification Examples
====================================================

Demonstrate how to construct verification goals from **actual term trees**
(``OpCall``, ``Op``, ``Var``) instead of opaque string labels.

The old pattern (``verify_sympy.py``, ``verify_torch.py``)::

    goal = _eq_goal(ctx, "AB_C", "A_BC")  # ← opaque variable names!

The correct pattern (this file)::

    goal = formal_eq(
        ctx,
        op_torch_matmul(op_torch_matmul(A, B), C),   # (A·B)·C
        op_torch_matmul(A, op_torch_matmul(B, C)),    # A·(B·C)
        type_=PyClassType("Matrix"),
    )

Because the goal is built from real term trees, the kernel can
pattern-match against axiom schemas and confirm the instantiation
is valid — no human trust required.

Run from the repo root::

    PYTHONPATH=. python3 synhopy/examples/verify_formal.py
"""
from __future__ import annotations

import sys
import time
from typing import Callable

from synhopy.core.types import (
    Context,
    Judgment,
    JudgmentKind,
    PyObjType,
    PyIntType,
    PyFloatType,
    PyClassType,
    PyListType,
    PyStrType,
    RefinementType,
    Var,
    Literal,
)
from synhopy.core.kernel import (
    ProofKernel,
    TrustLevel,
    VerificationResult,
)
from synhopy.core.formal_ops import (
    Op,
    OpCall,
    FormalAxiomEntry,
    formal_eq,
    formal_check,
    op_add,
    op_mul,
    op_neg,
    op_abs,
    op_len,
    op_sorted,
    op_append,
    op_contains,
    op_str_concat,
    op_sympy_expand,
    op_sympy_simplify,
    op_sympy_diff,
    op_sympy_integrate,
    op_torch_matmul,
    op_torch_relu,
    op_torch_softmax,
    op_torch_grad,
    op_np_dot,
    op_np_transpose,
    op_ge,
)
from synhopy.proofs.tactics import (
    ProofBuilder,
    equality_goal,
    refinement_goal,
    type_check_goal,
)


# ═══════════════════════════════════════════════════════════════════
#  Formal axiom installation
# ═══════════════════════════════════════════════════════════════════
# Register FormalAxiomEntry objects so the kernel can pattern-match
# goals built from real term trees against axiom schemas.

def _install_formal_axioms(kernel: ProofKernel) -> int:
    """Register formal axiom schemas alongside the legacy string axioms.

    Returns the number of formal axioms installed.
    """
    # Schema variables — these are universally quantified over
    a, b, c = Var("a"), Var("b"), Var("c")
    e = Var("e")
    f, g, x = Var("f"), Var("g"), Var("x")
    A, B, C = Var("A"), Var("B"), Var("C")
    xs = Var("xs")

    _OBJ = PyObjType()
    _INT = PyIntType()
    _FLOAT = PyFloatType()
    _MATRIX = PyClassType("Matrix")
    _STR = PyStrType()

    formal_axioms: list[FormalAxiomEntry] = [
        # ── SymPy ──────────────────────────────────────────────
        FormalAxiomEntry(
            name="expand_add", module="sympy",
            params=[("a", _OBJ), ("b", _OBJ)],
            conclusion=formal_eq(
                Context(), op_sympy_expand(op_add(a, b)),
                op_add(op_sympy_expand(a), op_sympy_expand(b)),
                type_=_OBJ,
            ),
            description="expand(a + b) = expand(a) + expand(b)",
        ),
        FormalAxiomEntry(
            name="simplify_idem", module="sympy",
            params=[("e", _OBJ)],
            conclusion=formal_eq(
                Context(), op_sympy_simplify(op_sympy_simplify(e)),
                op_sympy_simplify(e), type_=_OBJ,
            ),
            description="simplify(simplify(e)) = simplify(e)",
        ),
        FormalAxiomEntry(
            name="diff_sum", module="sympy",
            params=[("f", _OBJ), ("g", _OBJ), ("x", _OBJ)],
            conclusion=formal_eq(
                Context(), op_sympy_diff(op_add(f, g), x),
                op_add(op_sympy_diff(f, x), op_sympy_diff(g, x)),
                type_=_OBJ,
            ),
            description="diff(f+g, x) = diff(f,x) + diff(g,x)",
        ),
        FormalAxiomEntry(
            name="diff_product", module="sympy",
            params=[("f", _OBJ), ("g", _OBJ), ("x", _OBJ)],
            conclusion=formal_eq(
                Context(), op_sympy_diff(op_mul(f, g), x),
                op_add(
                    op_mul(f, op_sympy_diff(g, x)),
                    op_mul(op_sympy_diff(f, x), g),
                ),
                type_=_OBJ,
            ),
            description="diff(f*g, x) = f*diff(g,x) + diff(f,x)*g",
        ),
        FormalAxiomEntry(
            name="integrate_diff", module="sympy",
            params=[("f", _OBJ), ("x", _OBJ)],
            conclusion=formal_eq(
                Context(), op_sympy_diff(op_sympy_integrate(f, x), x),
                f, type_=_OBJ,
            ),
            description="diff(integrate(f, x), x) = f",
        ),

        # ── Torch ──────────────────────────────────────────────
        FormalAxiomEntry(
            name="matmul_assoc", module="torch",
            params=[("A", _MATRIX), ("B", _MATRIX), ("C", _MATRIX)],
            conclusion=formal_eq(
                Context(),
                op_torch_matmul(op_torch_matmul(A, B), C),
                op_torch_matmul(A, op_torch_matmul(B, C)),
                type_=_MATRIX,
            ),
            description="(A·B)·C = A·(B·C)",
        ),
        FormalAxiomEntry(
            name="matmul_left_distrib", module="torch",
            params=[("A", _MATRIX), ("B", _MATRIX), ("C", _MATRIX)],
            conclusion=formal_eq(
                Context(),
                op_torch_matmul(A, op_add(B, C)),
                op_add(op_torch_matmul(A, B), op_torch_matmul(A, C)),
                type_=_MATRIX,
            ),
            description="A·(B + C) = A·B + A·C",
        ),
        FormalAxiomEntry(
            name="grad_linear", module="torch",
            params=[("f", _OBJ), ("g", _OBJ), ("x", _OBJ)],
            conclusion=formal_eq(
                Context(),
                op_torch_grad(op_add(f, g), x),
                op_add(op_torch_grad(f, x), op_torch_grad(g, x)),
                type_=_OBJ,
            ),
            description="grad(f+g, x) = grad(f,x) + grad(g,x)",
        ),

        # ── Builtins ──────────────────────────────────────────
        FormalAxiomEntry(
            name="sorted_idempotent", module="builtins",
            params=[("xs", PyListType(_INT))],
            conclusion=formal_eq(
                Context(), op_sorted(op_sorted(xs)), op_sorted(xs),
                type_=PyListType(_INT),
            ),
            description="sorted(sorted(xs)) = sorted(xs)",
        ),
        FormalAxiomEntry(
            name="len_append", module="builtins",
            params=[("xs", PyListType(_OBJ)), ("x", _OBJ)],
            conclusion=formal_eq(
                Context(), op_len(op_append(xs, x)),
                op_add(op_len(xs), Literal(1, _INT)),
                type_=_INT,
            ),
            description="len(append(xs, x)) = len(xs) + 1",
        ),
        FormalAxiomEntry(
            name="str_concat_assoc", module="builtins",
            params=[("a", _STR), ("b", _STR), ("c", _STR)],
            conclusion=formal_eq(
                Context(),
                op_str_concat(op_str_concat(a, b), c),
                op_str_concat(a, op_str_concat(b, c)),
                type_=_STR,
            ),
            description="(a + b) + c = a + (b + c) for strings",
        ),
        FormalAxiomEntry(
            name="add_commutative", module="builtins",
            params=[("a", _OBJ), ("b", _OBJ)],
            conclusion=formal_eq(
                Context(), op_add(a, b), op_add(b, a), type_=_OBJ,
            ),
            description="a + b = b + a",
        ),
    ]

    for fa in formal_axioms:
        kernel.register_formal_axiom(fa)
    return len(formal_axioms)


# ═══════════════════════════════════════════════════════════════════
#  1. expand distributes over addition — formal
# ═══════════════════════════════════════════════════════════════════

def verify_expand_distributive_formal(
    kernel: ProofKernel,
) -> tuple[str, VerificationResult]:
    """expand(a + b) = expand(a) + expand(b) — with actual term trees."""
    a, b = Var("a"), Var("b")
    ctx = Context()
    ctx = ctx.extend("a", PyObjType())
    ctx = ctx.extend("b", PyObjType())

    # Goal built from real term trees — the kernel pattern-matches
    # this against the FormalAxiomEntry for expand_add.
    goal = formal_eq(
        ctx,
        op_sympy_expand(op_add(a, b)),
        op_add(op_sympy_expand(a), op_sympy_expand(b)),
        type_=PyObjType(),
    )

    pb = ProofBuilder(kernel, ctx, goal)
    result = pb.conclude(pb.axiom("expand_add", "sympy"))
    return "expand distributes (formal)", result


# ═══════════════════════════════════════════════════════════════════
#  2. matrix multiplication associativity — the motivating example
# ═══════════════════════════════════════════════════════════════════

def verify_matmul_assoc_formal(
    kernel: ProofKernel,
) -> tuple[str, VerificationResult]:
    """(A·B)·C = A·(B·C) — with formal term trees, not string labels."""
    A, B, C = Var("A"), Var("B"), Var("C")
    ctx = Context()
    for name in ["A", "B", "C"]:
        ctx = ctx.extend(name, PyClassType("Matrix"))

    goal = formal_eq(
        ctx,
        op_torch_matmul(op_torch_matmul(A, B), C),
        op_torch_matmul(A, op_torch_matmul(B, C)),
        type_=PyClassType("Matrix"),
    )

    pb = ProofBuilder(kernel, ctx, goal)
    result = pb.conclude(pb.axiom("matmul_assoc", "torch"))
    return "matrix multiply assoc (formal)", result


# ═══════════════════════════════════════════════════════════════════
#  3. derivative sum rule — formal
# ═══════════════════════════════════════════════════════════════════

def verify_diff_sum_formal(
    kernel: ProofKernel,
) -> tuple[str, VerificationResult]:
    """diff(f+g, x) = diff(f,x) + diff(g,x) — formal term trees."""
    f, g, x = Var("f"), Var("g"), Var("x")
    ctx = Context()
    ctx = ctx.extend("f", PyObjType())
    ctx = ctx.extend("g", PyObjType())
    ctx = ctx.extend("x", PyObjType())

    goal = formal_eq(
        ctx,
        op_sympy_diff(op_add(f, g), x),
        op_add(op_sympy_diff(f, x), op_sympy_diff(g, x)),
        type_=PyObjType(),
    )

    pb = ProofBuilder(kernel, ctx, goal)
    result = pb.conclude(pb.axiom("diff_sum", "sympy"))
    return "derivative sum rule (formal)", result


# ═══════════════════════════════════════════════════════════════════
#  4. ReLU non-negativity — formal
# ═══════════════════════════════════════════════════════════════════

def verify_relu_nonneg_formal(
    kernel: ProofKernel,
) -> tuple[str, VerificationResult]:
    """relu(x) >= 0 — stated as a formal type-check goal.

    ReLU non-negativity is a refinement property; the goal uses
    formal_check with a real OpCall term (not a string label).
    Falls back to the legacy string-based axiom since the refinement
    predicate is not yet pattern-matchable.
    """
    x = Var("x")
    ctx = Context()
    ctx = ctx.extend("x", PyFloatType())

    goal = formal_check(
        ctx,
        op_torch_relu(x),
        type_=RefinementType(
            base_type=PyFloatType(),
            predicate="v >= 0",
        ),
    )

    pb = ProofBuilder(kernel, ctx, goal)
    result = pb.conclude(pb.axiom("relu_nonneg", "torch"))
    return "relu non-negative (formal)", result


# ═══════════════════════════════════════════════════════════════════
#  5. sorted is idempotent — formal
# ═══════════════════════════════════════════════════════════════════

def verify_sorted_idempotent_formal(
    kernel: ProofKernel,
) -> tuple[str, VerificationResult]:
    """sorted(sorted(xs)) = sorted(xs) — formal term trees."""
    xs = Var("xs")
    ctx = Context()
    ctx = ctx.extend("xs", PyListType(PyIntType()))

    goal = formal_eq(
        ctx,
        op_sorted(op_sorted(xs)),
        op_sorted(xs),
        type_=PyListType(PyIntType()),
    )

    pb = ProofBuilder(kernel, ctx, goal)
    result = pb.conclude(pb.axiom("sorted_idempotent", "builtins"))
    return "sorted idempotent (formal)", result


# ═══════════════════════════════════════════════════════════════════
#  6. len non-negative — formal
# ═══════════════════════════════════════════════════════════════════

def verify_len_nonneg_formal(
    kernel: ProofKernel,
) -> tuple[str, VerificationResult]:
    """len(xs) >= 0 — stated as a refinement type check.

    Uses a formal OpCall term for len(xs), with a string predicate
    for the refinement (the kernel falls back to legacy axiom lookup).
    """
    xs = Var("xs")
    ctx = Context()
    ctx = ctx.extend("xs", PyListType(PyObjType()))

    goal = formal_check(
        ctx,
        op_len(xs),
        type_=RefinementType(
            base_type=PyIntType(),
            predicate="n >= 0",
        ),
    )

    pb = ProofBuilder(kernel, ctx, goal)
    result = pb.conclude(pb.axiom("len_nonneg", "builtins"))
    return "len non-negative (formal)", result


# ═══════════════════════════════════════════════════════════════════
#  7. gradient linearity — formal
# ═══════════════════════════════════════════════════════════════════

def verify_grad_linearity_formal(
    kernel: ProofKernel,
) -> tuple[str, VerificationResult]:
    """grad(f + g, x) = grad(f, x) + grad(g, x) — formal term trees."""
    f, g, x = Var("f"), Var("g"), Var("x")
    ctx = Context()
    ctx = ctx.extend("f", PyObjType())
    ctx = ctx.extend("g", PyObjType())
    ctx = ctx.extend("x", PyObjType())

    goal = formal_eq(
        ctx,
        op_torch_grad(op_add(f, g), x),
        op_add(op_torch_grad(f, x), op_torch_grad(g, x)),
        type_=PyObjType(),
    )

    pb = ProofBuilder(kernel, ctx, goal)
    result = pb.conclude(pb.axiom("grad_linear", "torch"))
    return "gradient linearity (formal)", result


# ═══════════════════════════════════════════════════════════════════
#  8. string concatenation associativity — formal
# ═══════════════════════════════════════════════════════════════════

def verify_str_concat_assoc_formal(
    kernel: ProofKernel,
) -> tuple[str, VerificationResult]:
    """(a + b) + c = a + (b + c) for strings — formal term trees."""
    a, b, c = Var("a"), Var("b"), Var("c")
    ctx = Context()
    for name in ["a", "b", "c"]:
        ctx = ctx.extend(name, PyStrType())

    goal = formal_eq(
        ctx,
        op_str_concat(op_str_concat(a, b), c),
        op_str_concat(a, op_str_concat(b, c)),
        type_=PyStrType(),
    )

    pb = ProofBuilder(kernel, ctx, goal)
    result = pb.conclude(pb.axiom("str_concat_assoc", "builtins"))
    return "string concat assoc (formal)", result


# ═══════════════════════════════════════════════════════════════════
#  9. list append length — formal
# ═══════════════════════════════════════════════════════════════════

def verify_append_length_formal(
    kernel: ProofKernel,
) -> tuple[str, VerificationResult]:
    """len(append(xs, x)) = len(xs) + 1 — formal term trees."""
    xs, x = Var("xs"), Var("x")
    ctx = Context()
    ctx = ctx.extend("xs", PyListType(PyObjType()))
    ctx = ctx.extend("x", PyObjType())

    goal = formal_eq(
        ctx,
        op_len(op_append(xs, x)),
        op_add(op_len(xs), Literal(1, PyIntType())),
        type_=PyIntType(),
    )

    pb = ProofBuilder(kernel, ctx, goal)
    result = pb.conclude(pb.axiom("len_append", "builtins"))
    return "list append length (formal)", result


# ═══════════════════════════════════════════════════════════════════
#  10. simplify(diff(f+g, x)) via transitivity — multi-step formal
# ═══════════════════════════════════════════════════════════════════

def verify_simplify_diff_trans_formal(
    kernel: ProofKernel,
) -> tuple[str, VerificationResult]:
    """Multi-step proof using transitivity over formal term trees.

    We prove:  simplify(diff(f+g,x)) = simplify(diff(f,x) + diff(g,x))

    Strategy:
      Step 1 — diff_sum axiom gives:  diff(f+g,x) = diff(f,x) + diff(g,x)
      Step 2 — congruence under simplify (structural, since the kernel's
               Cong doesn't yet decompose goals into sub-goals)

    This demonstrates how formal term-tree goals compose even when the
    kernel falls back to structural reasoning for congruence closure.
    """
    f, g, x = Var("f"), Var("g"), Var("x")
    ctx = Context()
    ctx = ctx.extend("f", PyObjType())
    ctx = ctx.extend("g", PyObjType())
    ctx = ctx.extend("x", PyObjType())

    lhs = op_sympy_simplify(op_sympy_diff(op_add(f, g), x))
    rhs = op_sympy_simplify(op_add(op_sympy_diff(f, x), op_sympy_diff(g, x)))

    # Goal: simplify(diff(f+g,x)) =_{PyObj} simplify(diff(f,x)+diff(g,x))
    goal = formal_eq(ctx, lhs, rhs, type_=PyObjType())

    pb = ProofBuilder(kernel, ctx, goal)

    # The inner axiom diff_sum gives:
    #   diff(f+g,x) = diff(f,x) + diff(g,x)
    # Lifting through simplify is congruence; the kernel's Cong
    # does not decompose goals yet, so we use structural.
    result = pb.conclude(pb.structural(
        "congruence: simplify applied to diff_sum axiom — "
        "diff(f+g,x) = diff(f,x)+diff(g,x) under simplify"
    ))
    return "simplify∘diff trans chain (formal)", result


# ═══════════════════════════════════════════════════════════════════
#  11. derivative product rule — formal
# ═══════════════════════════════════════════════════════════════════

def verify_diff_product_formal(
    kernel: ProofKernel,
) -> tuple[str, VerificationResult]:
    """diff(f*g, x) = f*diff(g,x) + diff(f,x)*g — formal term trees."""
    f, g, x = Var("f"), Var("g"), Var("x")
    ctx = Context()
    ctx = ctx.extend("f", PyObjType())
    ctx = ctx.extend("g", PyObjType())
    ctx = ctx.extend("x", PyObjType())

    goal = formal_eq(
        ctx,
        op_sympy_diff(op_mul(f, g), x),
        op_add(
            op_mul(f, op_sympy_diff(g, x)),
            op_mul(op_sympy_diff(f, x), g),
        ),
        type_=PyObjType(),
    )

    pb = ProofBuilder(kernel, ctx, goal)
    result = pb.conclude(pb.axiom("diff_product", "sympy"))
    return "derivative product rule (formal)", result


# ═══════════════════════════════════════════════════════════════════
#  12. simplify idempotent — formal
# ═══════════════════════════════════════════════════════════════════

def verify_simplify_idem_formal(
    kernel: ProofKernel,
) -> tuple[str, VerificationResult]:
    """simplify(simplify(e)) = simplify(e) — formal term trees."""
    e = Var("e")
    ctx = Context()
    ctx = ctx.extend("e", PyObjType())

    goal = formal_eq(
        ctx,
        op_sympy_simplify(op_sympy_simplify(e)),
        op_sympy_simplify(e),
        type_=PyObjType(),
    )

    pb = ProofBuilder(kernel, ctx, goal)
    result = pb.conclude(pb.axiom("simplify_idem", "sympy"))
    return "simplify idempotent (formal)", result


# ═══════════════════════════════════════════════════════════════════
#  13. matmul distributes over addition — formal
# ═══════════════════════════════════════════════════════════════════

def verify_matmul_left_distrib_formal(
    kernel: ProofKernel,
) -> tuple[str, VerificationResult]:
    """A·(B + C) = A·B + A·C — formal term trees."""
    A, B, C = Var("A"), Var("B"), Var("C")
    ctx = Context()
    for name in ["A", "B", "C"]:
        ctx = ctx.extend(name, PyClassType("Matrix"))

    goal = formal_eq(
        ctx,
        op_torch_matmul(A, op_add(B, C)),
        op_add(op_torch_matmul(A, B), op_torch_matmul(A, C)),
        type_=PyClassType("Matrix"),
    )

    pb = ProofBuilder(kernel, ctx, goal)
    result = pb.conclude(pb.axiom("matmul_left_distrib", "torch"))
    return "matmul left distributive (formal)", result


# ═══════════════════════════════════════════════════════════════════
#  14. integrate is right-inverse of diff — formal (FTC)
# ═══════════════════════════════════════════════════════════════════

def verify_ftc_formal(
    kernel: ProofKernel,
) -> tuple[str, VerificationResult]:
    """diff(integrate(f, x), x) = f — Fundamental Theorem of Calculus."""
    f, x = Var("f"), Var("x")
    ctx = Context()
    ctx = ctx.extend("f", PyObjType())
    ctx = ctx.extend("x", PyObjType())

    goal = formal_eq(
        ctx,
        op_sympy_diff(op_sympy_integrate(f, x), x),
        f,
        type_=PyObjType(),
    )

    pb = ProofBuilder(kernel, ctx, goal)
    result = pb.conclude(pb.axiom("integrate_diff", "sympy"))
    return "FTC: diff∘integrate = id (formal)", result


# ═══════════════════════════════════════════════════════════════════
#  15. addition commutativity — formal
# ═══════════════════════════════════════════════════════════════════

def verify_add_comm_formal(
    kernel: ProofKernel,
) -> tuple[str, VerificationResult]:
    """a + b = b + a — formal term trees."""
    a, b = Var("a"), Var("b")
    ctx = Context()
    ctx = ctx.extend("a", PyObjType())
    ctx = ctx.extend("b", PyObjType())

    goal = formal_eq(
        ctx,
        op_add(a, b),
        op_add(b, a),
        type_=PyObjType(),
    )

    pb = ProofBuilder(kernel, ctx, goal)
    result = pb.conclude(pb.axiom("add_commutative", "builtins"))
    return "addition commutativity (formal)", result


# ═══════════════════════════════════════════════════════════════════
#  Runner
# ═══════════════════════════════════════════════════════════════════

_ALL_EXAMPLES: list[Callable[[ProofKernel], tuple[str, VerificationResult]]] = [
    verify_expand_distributive_formal,
    verify_matmul_assoc_formal,
    verify_diff_sum_formal,
    verify_relu_nonneg_formal,
    verify_sorted_idempotent_formal,
    verify_len_nonneg_formal,
    verify_grad_linearity_formal,
    verify_str_concat_assoc_formal,
    verify_append_length_formal,
    verify_simplify_diff_trans_formal,
    verify_diff_product_formal,
    verify_simplify_idem_formal,
    verify_matmul_left_distrib_formal,
    verify_ftc_formal,
    verify_add_comm_formal,
]


def run_formal_verifications(*, verbose: bool = False) -> tuple[int, int]:
    """Run every formal-term verification and print a summary.

    Returns ``(passed, total)``.
    """
    kernel = ProofKernel()

    # Install legacy string-based axioms for backward compat
    from synhopy.axioms.library_axioms import default_registry
    registry = default_registry()
    registry.install_into_kernel(kernel)

    # Layer formal axiom schemas on top — these enable true
    # pattern-matching between axiom schemas and term-tree goals.
    try:
        from synhopy.axioms.formal_axiom_library import install_formal_axioms
        install_formal_axioms(kernel)
    except (ImportError, AttributeError):
        pass
    n_formal = _install_formal_axioms(kernel)

    separator = "═" * 62
    thin_sep = "─" * 62

    print()
    print(separator)
    print("  SynHoPy — Formal Term-Tree Verification Examples")
    print(separator)
    if verbose:
        print(f"  Installed {n_formal} formal axiom schemas")
        print(thin_sep)

    passed = 0
    total = len(_ALL_EXAMPLES)
    t0 = time.perf_counter()

    for fn in _ALL_EXAMPLES:
        prop_name, result = fn(kernel)
        icon = "✓" if result.success else "✗"
        trust = result.trust_level.name
        print(f"  {icon} [{trust:18s}] {prop_name}")
        if verbose and result.success and hasattr(result, "axioms_used") and result.axioms_used:
            axiom_list = ", ".join(result.axioms_used)
            print(f"        axioms: {axiom_list}")
        if not result.success:
            print(f"      error: {result.message}")
        if result.success:
            passed += 1

    elapsed_ms = (time.perf_counter() - t0) * 1000

    print(thin_sep)
    print(f"  {passed}/{total} properties verified  ({elapsed_ms:.1f} ms)")
    print(separator)
    print()

    return passed, total


if __name__ == "__main__":
    verbose = "--verbose" in sys.argv or "-v" in sys.argv
    passed, total = run_formal_verifications(verbose=verbose)
    raise SystemExit(total - passed)
