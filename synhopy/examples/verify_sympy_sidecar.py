"""SynHoPy — SymPy Sidecar Verification Demo
=============================================

Demonstrates **external ("sidecar") verification** of the real SymPy library.
SymPy's source code is never modified — all axioms, proofs, and runtime
checks live entirely in this file and use the existing SynHoPy infrastructure.

Key insight
-----------
A sidecar proof is an external proof artifact that attaches to a library
without touching it.  The verified properties can be stripped away at any
time, leaving the original library completely untouched.

Run from the repo root::

    PYTHONPATH=. python3 synhopy/examples/verify_sympy_sidecar.py

Categories of proved properties
-------------------------------
A. Algebraic identities  (5 proofs)
B. Calculus               (6 proofs)
C. Linear algebra         (5 proofs)
D. Number theory          (4 proofs)
E. Runtime validation     (5 checks)
"""
from __future__ import annotations

import sys
import time
from typing import Callable

# ── sympy (the library under verification — UNMODIFIED) ─────────
import sympy
from sympy import (
    symbols, Symbol, expand, simplify, factor, collect,
    diff, integrate, cos, sin, exp, log, sqrt, pi, oo,
    factorial, binomial, Rational,
    Matrix, eye, det, trace,
)

# ── SynHoPy proof infrastructure ────────────────────────────────
from synhopy.core.kernel import (
    ProofKernel,
    TrustLevel,
    VerificationResult,
)
from synhopy.core.types import (
    Context,
    Judgment,
    JudgmentKind,
    PyObjType,
    PyIntType,
    PyClassType,
    Var,
    Literal,
)
from synhopy.core.formal_ops import (
    Op,
    OpCall,
    FormalAxiomEntry,
    formal_eq,
    op_add,
    op_mul,
    op_sub,
    op_sympy_expand,
    op_sympy_simplify,
    op_sympy_factor,
    op_sympy_diff,
    op_sympy_integrate,
)
from synhopy.proofs.tactics import ProofBuilder
from synhopy.proofs.sugar import (
    Proof,
    FormalProof,
    library_trust,
    by_axiom,
    by_z3,
)

# ═════════════════════════════════════════════════════════════════
# Globals
# ═════════════════════════════════════════════════════════════════

_PASS = 0
_FAIL = 0
_RUNTIME_PASS = 0
_RUNTIME_TOTAL = 0

_CATEGORY_STATS: dict[str, tuple[int, int]] = {}
_CATEGORY_TRUST: dict[str, str] = {}

_OBJ = PyObjType()
_INT = PyIntType()
_MATRIX = PyClassType("Matrix")


# ═════════════════════════════════════════════════════════════════
# Helpers
# ═════════════════════════════════════════════════════════════════

def _show(label: str, result: VerificationResult | None = None,
          ok: bool | None = None, trust_override: str = "") -> None:
    global _PASS, _FAIL
    if result is not None:
        ok = result.success
        trust = result.trust_level.name
    else:
        trust = trust_override or "N/A"
    mark = "✓" if ok else "✗"
    if ok:
        _PASS += 1
    else:
        _FAIL += 1
    print(f"  {mark} [{trust:20s}] {label}")


def _runtime_check(description: str, actual, expected, *,
                   use_equals: bool = False) -> bool:
    """Validate a sympy computation against expected result."""
    global _RUNTIME_PASS, _RUNTIME_TOTAL
    _RUNTIME_TOTAL += 1
    if use_equals:
        ok = actual.equals(expected)
    else:
        ok = (actual == expected)
        if hasattr(ok, '__bool__'):
            ok = bool(ok)
    if ok:
        _RUNTIME_PASS += 1
        print(f"    runtime: {description} ✓")
    else:
        print(f"    runtime: {description} ✗  (got {actual})")
    return ok


def _category_header(name: str) -> None:
    print(f"\n  {'─' * 60}")
    print(f"  Category {name}")
    print(f"  {'─' * 60}")


def _record_category(name: str, proved: int, total: int, trust: str) -> None:
    _CATEGORY_STATS[name] = (proved, total)
    _CATEGORY_TRUST[name] = trust


# ═════════════════════════════════════════════════════════════════
# Sidecar axiom installation
# ═════════════════════════════════════════════════════════════════

def _install_sympy_sidecar_axioms(kernel: ProofKernel) -> int:
    """Register axioms about sympy into the kernel — EXTERNALLY.

    SymPy's source code is never touched.  These axioms encode
    mathematical properties that sympy is expected to satisfy.
    """
    # Schema variables (universally quantified)
    a, b, c = Var("a"), Var("b"), Var("c")
    e = Var("e")
    f, g, x = Var("f"), Var("g"), Var("x")
    n = Var("n")
    A, B, C, I_mat = Var("A"), Var("B"), Var("C"), Var("I")
    p = Var("p")

    # ── string-based axioms (library_trust style) ────────────────
    with library_trust("sympy", kernel) as sp:
        # Algebra
        sp.axiom("expand(a + b) = expand(a) + expand(b)",
                  name="expand_add")
        sp.axiom("expand(expand(e)) = expand(e)",
                  name="expand_idem")
        sp.axiom("simplify(simplify(e)) = simplify(e)",
                  name="simplify_idem")
        sp.axiom("expand(factor(e)) = expand(e) for polynomials",
                  name="expand_factor")
        sp.axiom("collect(e, x) = expand(e) reorganized by powers of x",
                  name="collect_expand")

        # Calculus
        sp.axiom("diff(integrate(f, x), x) = f",
                  name="ftc")
        sp.axiom("diff(a*f + b*g, x) = a*diff(f,x) + b*diff(g,x)",
                  name="diff_linear")
        sp.axiom("diff(f*g, x) = diff(f,x)*g + f*diff(g,x)",
                  name="diff_product")
        sp.axiom("diff(f(g(x)), x) = f'(g(x)) * g'(x)",
                  name="diff_chain")
        sp.axiom("integrate(diff(f, x), x) = f + C",
                  name="antidiff_ftc")
        sp.axiom("diff(c, x) = 0 when c is constant w.r.t. x",
                  name="diff_constant_zero")

        # Linear algebra
        sp.axiom("det(eye(n)) = 1",
                  name="det_identity")
        sp.axiom("det(A * B) = det(A) * det(B)",
                  name="det_product")
        sp.axiom("(A * B) * C = A * (B * C) for matrices",
                  name="matmul_assoc")
        sp.axiom("A.inv().inv() = A for invertible A",
                  name="inv_involution")
        sp.axiom("trace(A + B) = trace(A) + trace(B)",
                  name="trace_add")

        # Number theory / combinatorics
        sp.axiom("factorial(n+1) = (n+1) * factorial(n)",
                  name="factorial_rec")
        sp.axiom("binomial(n, 0) = 1",
                  name="binomial_zero")
        sp.axiom("binomial(n, n) = 1",
                  name="binomial_n_n")
        sp.axiom("binomial(n, k) = binomial(n, n-k)",
                  name="binomial_symmetry")

    # ── formal axioms (term-tree style) ──────────────────────────
    formal_axioms: list[FormalAxiomEntry] = [
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
            name="expand_idem", module="sympy",
            params=[("e", _OBJ)],
            conclusion=formal_eq(
                Context(), op_sympy_expand(op_sympy_expand(e)),
                op_sympy_expand(e), type_=_OBJ,
            ),
            description="expand(expand(e)) = expand(e)",
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
            name="expand_factor", module="sympy",
            params=[("e", _OBJ)],
            conclusion=formal_eq(
                Context(), op_sympy_expand(op_sympy_factor(e)),
                op_sympy_expand(e), type_=_OBJ,
            ),
            description="expand(factor(e)) = expand(e)",
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
                    op_mul(op_sympy_diff(f, x), g),
                    op_mul(f, op_sympy_diff(g, x)),
                ),
                type_=_OBJ,
            ),
            description="diff(f*g, x) = diff(f,x)*g + f*diff(g,x)",
        ),
        FormalAxiomEntry(
            name="ftc", module="sympy",
            params=[("f", _OBJ), ("x", _OBJ)],
            conclusion=formal_eq(
                Context(), op_sympy_diff(op_sympy_integrate(f, x), x),
                f, type_=_OBJ,
            ),
            description="diff(integrate(f, x), x) = f",
        ),
    ]

    for fa in formal_axioms:
        kernel.register_formal_axiom(fa)

    return len(formal_axioms)


# ═════════════════════════════════════════════════════════════════
# A. Algebraic Identities (5 proofs)
# ═════════════════════════════════════════════════════════════════

def prove_algebra(kernel: ProofKernel) -> tuple[int, int]:
    """Prove 5 algebraic properties of sympy."""
    _category_header("A — Algebraic Identities")
    passed = 0
    total = 5

    # ── A1. expand is idempotent ─────────────────────────────────
    e = Var("e")
    ctx = Context().extend("e", _OBJ)
    goal = formal_eq(ctx, op_sympy_expand(op_sympy_expand(e)),
                     op_sympy_expand(e), type_=_OBJ)
    pb = ProofBuilder(kernel, ctx, goal)
    r = pb.conclude(pb.axiom("expand_idem", "sympy"))
    _show("A1  expand(expand(e)) = expand(e)", result=r)
    if r.success:
        passed += 1

    x, y = symbols('x y')
    expr = (x + y)**3
    _runtime_check("expand(expand((x+y)³)) == expand((x+y)³)",
                    expand(expand(expr)), expand(expr))

    # ── A2. expand distributes over addition ─────────────────────
    a, b = Var("a"), Var("b")
    ctx = Context().extend("a", _OBJ).extend("b", _OBJ)
    goal = formal_eq(ctx, op_sympy_expand(op_add(a, b)),
                     op_add(op_sympy_expand(a), op_sympy_expand(b)),
                     type_=_OBJ)
    pb = ProofBuilder(kernel, ctx, goal)
    r = pb.conclude(pb.axiom("expand_add", "sympy"))
    _show("A2  expand(a + b) = expand(a) + expand(b)", result=r)
    if r.success:
        passed += 1

    e1, e2 = (x + 1)**2, (y - 1)**2
    _runtime_check("expand((x+1)² + (y-1)²) == expand((x+1)²) + expand((y-1)²)",
                    expand(e1 + e2), expand(e1) + expand(e2))

    # ── A3. expand(factor(p)) == expand(p) ───────────────────────
    ev = Var("e")
    ctx = Context().extend("e", _OBJ)
    goal = formal_eq(ctx, op_sympy_expand(op_sympy_factor(ev)),
                     op_sympy_expand(ev), type_=_OBJ)
    pb = ProofBuilder(kernel, ctx, goal)
    r = pb.conclude(pb.axiom("expand_factor", "sympy"))
    _show("A3  expand(factor(e)) = expand(e)", result=r)
    if r.success:
        passed += 1

    poly = x**2 + 2*x*y + y**2
    _runtime_check("expand(factor(x²+2xy+y²)) == expand(x²+2xy+y²)",
                    expand(factor(poly)), expand(poly))

    # ── A4. simplify is idempotent ───────────────────────────────
    ctx = Context().extend("e", _OBJ)
    goal = formal_eq(ctx, op_sympy_simplify(op_sympy_simplify(ev)),
                     op_sympy_simplify(ev), type_=_OBJ)
    pb = ProofBuilder(kernel, ctx, goal)
    r = pb.conclude(pb.axiom("simplify_idem", "sympy"))
    _show("A4  simplify(simplify(e)) = simplify(e)", result=r)
    if r.success:
        passed += 1

    messy = (x**2 - 1)/(x - 1)
    _runtime_check("simplify(simplify((x²-1)/(x-1))) == simplify(...)",
                    simplify(simplify(messy)), simplify(messy))

    # ── A5. collect vs expand (axiom-based proof) ────────────────
    r = (
        Proof("collect(e, x) reorganizes expand(e) by powers of x")
        .using(kernel)
        .given(e="object", x="object")
        .by_axiom("collect_expand", "sympy")
        .qed()
    )
    _show("A5  collect(e, x) ≡ expand reorganized", result=r)
    if r.success:
        passed += 1

    poly2 = x**3 + 2*x**2*y + x*y**2 + x + 1
    _runtime_check("collect(poly, x) expands correctly",
                    expand(collect(poly2, x)), expand(poly2))

    _record_category("Algebra", passed, total, "AXIOM_TRUSTED")
    return passed, total


# ═════════════════════════════════════════════════════════════════
# B. Calculus (6 proofs)
# ═════════════════════════════════════════════════════════════════

def prove_calculus(kernel: ProofKernel) -> tuple[int, int]:
    """Prove 6 calculus properties of sympy."""
    _category_header("B — Calculus")
    passed = 0
    total = 6

    x_sym = Symbol('x')

    # ── B1. FTC: diff(integrate(f, x), x) = f ───────────────────
    f_v, x_v = Var("f"), Var("x")
    ctx = Context().extend("f", _OBJ).extend("x", _OBJ)
    goal = formal_eq(ctx, op_sympy_diff(op_sympy_integrate(f_v, x_v), x_v),
                     f_v, type_=_OBJ)
    pb = ProofBuilder(kernel, ctx, goal)
    r = pb.conclude(pb.axiom("ftc", "sympy"))
    _show("B1  diff(∫f dx, x) = f  [FTC]", result=r)
    if r.success:
        passed += 1

    _runtime_check("diff(integrate(x³, x), x) == x³",
                    diff(integrate(x_sym**3, x_sym), x_sym), x_sym**3)

    # ── B2. Linearity of diff: diff(a*f+b*g) = a*diff(f)+b*diff(g)
    r = (
        Proof("diff(a*f + b*g, x) = a*diff(f,x) + b*diff(g,x)")
        .using(kernel)
        .given(a="object", b="object", f="object", g="object", x="object")
        .by_axiom("diff_linear", "sympy")
        .qed()
    )
    _show("B2  diff(a·f + b·g) = a·diff(f) + b·diff(g)", result=r)
    if r.success:
        passed += 1

    f_expr, g_expr = x_sym**2, sin(x_sym)
    lhs = diff(3*f_expr + 5*g_expr, x_sym)
    rhs = 3*diff(f_expr, x_sym) + 5*diff(g_expr, x_sym)
    _runtime_check("diff(3x² + 5sin(x)) = 6x + 5cos(x)",
                    expand(lhs), expand(rhs))

    # ── B3. Product rule ─────────────────────────────────────────
    f_v, g_v, x_v = Var("f"), Var("g"), Var("x")
    ctx = Context().extend("f", _OBJ).extend("g", _OBJ).extend("x", _OBJ)
    goal = formal_eq(
        ctx,
        op_sympy_diff(op_mul(f_v, g_v), x_v),
        op_add(
            op_mul(op_sympy_diff(f_v, x_v), g_v),
            op_mul(f_v, op_sympy_diff(g_v, x_v)),
        ),
        type_=_OBJ,
    )
    pb = ProofBuilder(kernel, ctx, goal)
    r = pb.conclude(pb.axiom("diff_product", "sympy"))
    _show("B3  diff(f·g) = diff(f)·g + f·diff(g)  [product rule]", result=r)
    if r.success:
        passed += 1

    fg = x_sym**2 * cos(x_sym)
    _runtime_check("product rule for x²·cos(x)",
                    expand(diff(fg, x_sym)),
                    expand(diff(x_sym**2, x_sym)*cos(x_sym) +
                           x_sym**2 * diff(cos(x_sym), x_sym)))

    # ── B4. Chain rule ───────────────────────────────────────────
    r = (
        Proof("diff(f(g(x)), x) = f'(g(x)) * g'(x)")
        .using(kernel)
        .given(f="object", g="object", x="object")
        .by_axiom("diff_chain", "sympy")
        .qed()
    )
    _show("B4  diff(f∘g) = (f'∘g)·g'  [chain rule]", result=r)
    if r.success:
        passed += 1

    composite = sin(x_sym**2)
    _runtime_check("chain rule: diff(sin(x²)) = 2x·cos(x²)",
                    diff(composite, x_sym),
                    2*x_sym*cos(x_sym**2))

    # ── B5. Integration undoes differentiation (up to constant) ──
    r = (
        Proof("integrate(diff(f, x), x) = f + C")
        .using(kernel)
        .given(f="object", x="object")
        .by_axiom("antidiff_ftc", "sympy")
        .qed()
    )
    _show("B5  ∫diff(f)dx = f + C", result=r)
    if r.success:
        passed += 1

    expr = x_sym**4 / 4
    _runtime_check("integrate(diff(x⁴/4)) == x⁴/4",
                    integrate(diff(expr, x_sym), x_sym), expr)

    # ── B6. Derivative of constant is zero ───────────────────────
    r = (
        Proof("diff(c, x) = 0 when c is constant w.r.t. x")
        .using(kernel)
        .given(c="object", x="object")
        .by_axiom("diff_constant_zero", "sympy")
        .qed()
    )
    _show("B6  diff(constant, x) = 0", result=r)
    if r.success:
        passed += 1

    _runtime_check("diff(42, x) == 0",
                    diff(sympy.Integer(42), x_sym), sympy.Integer(0))

    _record_category("Calculus", passed, total, "AXIOM_TRUSTED")
    return passed, total


# ═════════════════════════════════════════════════════════════════
# C. Linear Algebra (5 proofs)
# ═════════════════════════════════════════════════════════════════

def prove_linear_algebra(kernel: ProofKernel) -> tuple[int, int]:
    """Prove 5 linear algebra properties of sympy."""
    _category_header("C — Linear Algebra")
    passed = 0
    total = 5

    # ── C1. det(I) == 1 ──────────────────────────────────────────
    r = (
        Proof("det(eye(n)) = 1")
        .using(kernel)
        .given(n="int")
        .by_axiom("det_identity", "sympy")
        .qed()
    )
    _show("C1  det(I_n) = 1", result=r)
    if r.success:
        passed += 1

    for n in (1, 2, 3, 5):
        _runtime_check(f"det(I_{n}) == 1",
                        eye(n).det(), sympy.Integer(1))

    # ── C2. det(A*B) == det(A)*det(B) ────────────────────────────
    r = (
        Proof("det(A * B) = det(A) * det(B)")
        .using(kernel)
        .given(A="object", B="object")
        .by_axiom("det_product", "sympy")
        .qed()
    )
    _show("C2  det(A·B) = det(A)·det(B)", result=r)
    if r.success:
        passed += 1

    A_m = Matrix([[1, 2], [3, 4]])
    B_m = Matrix([[5, 6], [7, 8]])
    _runtime_check("det([[1,2],[3,4]] · [[5,6],[7,8]]) check",
                    (A_m * B_m).det(), A_m.det() * B_m.det())

    # ── C3. Matrix multiplication associativity ──────────────────
    r = (
        Proof("(A * B) * C = A * (B * C) for matrices")
        .using(kernel)
        .given(A="object", B="object", C="object")
        .by_axiom("matmul_assoc", "sympy")
        .qed()
    )
    _show("C3  (A·B)·C = A·(B·C)", result=r)
    if r.success:
        passed += 1

    C_m = Matrix([[9, 10], [11, 12]])
    _runtime_check("matrix multiply assoc 2×2",
                    (A_m * B_m) * C_m, A_m * (B_m * C_m))

    # ── C4. inv(inv(A)) == A ─────────────────────────────────────
    r = (
        Proof("A.inv().inv() = A for invertible A")
        .using(kernel)
        .given(A="object")
        .by_axiom("inv_involution", "sympy")
        .qed()
    )
    _show("C4  inv(inv(A)) = A", result=r)
    if r.success:
        passed += 1

    _runtime_check("inv(inv([[1,2],[3,4]])) == original",
                    A_m.inv().inv(), A_m)

    # ── C5. trace(A + B) == trace(A) + trace(B) ─────────────────
    r = (
        Proof("trace(A + B) = trace(A) + trace(B)")
        .using(kernel)
        .given(A="object", B="object")
        .by_axiom("trace_add", "sympy")
        .qed()
    )
    _show("C5  trace(A + B) = trace(A) + trace(B)", result=r)
    if r.success:
        passed += 1

    _runtime_check("trace([[1,2],[3,4]] + [[5,6],[7,8]])",
                    (A_m + B_m).trace(), A_m.trace() + B_m.trace())

    _record_category("Linear Algebra", passed, total, "AXIOM_TRUSTED")
    return passed, total


# ═════════════════════════════════════════════════════════════════
# D. Number Theory / Combinatorics (4 proofs)
# ═════════════════════════════════════════════════════════════════

def prove_number_theory(kernel: ProofKernel) -> tuple[int, int]:
    """Prove 4 number theory / combinatorics properties of sympy."""
    _category_header("D — Number Theory / Combinatorics")
    passed = 0
    total = 4

    # ── D1. factorial(n+1) == (n+1)*factorial(n) ─────────────────
    r = (
        Proof("factorial(n+1) = (n+1) * factorial(n)")
        .using(kernel)
        .given(n="int")
        .by_axiom("factorial_rec", "sympy")
        .qed()
    )
    _show("D1  factorial(n+1) = (n+1)·factorial(n)", result=r)
    if r.success:
        passed += 1

    for n_val in range(8):
        _runtime_check(f"factorial({n_val+1}) == {n_val+1}·factorial({n_val})",
                        factorial(n_val + 1),
                        (n_val + 1) * factorial(n_val))

    # ── D2. binomial(n, 0) == 1 ──────────────────────────────────
    r = (
        Proof("binomial(n, 0) = 1")
        .using(kernel)
        .given(n="int")
        .by_axiom("binomial_zero", "sympy")
        .qed()
    )
    _show("D2  C(n, 0) = 1", result=r)
    if r.success:
        passed += 1

    for n_val in (0, 1, 5, 10, 100):
        _runtime_check(f"binomial({n_val}, 0) == 1",
                        binomial(n_val, 0), 1)

    # ── D3. binomial(n, n) == 1 ──────────────────────────────────
    r = (
        Proof("binomial(n, n) = 1")
        .using(kernel)
        .given(n="int")
        .by_axiom("binomial_n_n", "sympy")
        .qed()
    )
    _show("D3  C(n, n) = 1", result=r)
    if r.success:
        passed += 1

    for n_val in (0, 1, 5, 10, 100):
        _runtime_check(f"binomial({n_val}, {n_val}) == 1",
                        binomial(n_val, n_val), 1)

    # ── D4. binomial symmetry: C(n,k) == C(n,n-k) ───────────────
    r = (
        Proof("binomial(n, k) = binomial(n, n-k)")
        .using(kernel)
        .given(n="int", k="int")
        .by_axiom("binomial_symmetry", "sympy")
        .qed()
    )
    _show("D4  C(n, k) = C(n, n−k)  [symmetry]", result=r)
    if r.success:
        passed += 1

    for n_val, k_val in [(5, 2), (10, 3), (7, 0), (8, 8), (20, 7)]:
        _runtime_check(f"binomial({n_val},{k_val}) == binomial({n_val},{n_val-k_val})",
                        binomial(n_val, k_val),
                        binomial(n_val, n_val - k_val))

    _record_category("Number Theory", passed, total, "AXIOM_TRUSTED")
    return passed, total


# ═════════════════════════════════════════════════════════════════
# E. Runtime Validation / Z3 Cross-checks (5 proofs)
# ═════════════════════════════════════════════════════════════════

def prove_runtime_validation(kernel: ProofKernel) -> tuple[int, int]:
    """Runtime validation: use Z3 arithmetic + direct sympy calls."""
    _category_header("E — Runtime Validation (Z3 cross-checks)")
    passed = 0
    total = 5

    x, y = symbols('x y')

    # ── E1. Z3: x + 0 == x ──────────────────────────────────────
    r = (
        Proof("x + 0 == x")
        .using(kernel)
        .given(x="int")
        .by_z3("x + 0 == x")
        .qed()
    )
    _show("E1  x + 0 = x  [Z3 arithmetic]", result=r)
    if r.success:
        passed += 1

    _runtime_check("sympy: simplify(x + 0) == x",
                    simplify(x + 0), x)

    # ── E2. Z3: distributive law ─────────────────────────────────
    r = (
        Proof("a * (b + c) == a*b + a*c")
        .using(kernel)
        .given(a="int", b="int", c="int")
        .by_z3("a * (b + c) == a*b + a*c")
        .qed()
    )
    _show("E2  a·(b+c) = a·b + a·c  [Z3 arithmetic]", result=r)
    if r.success:
        passed += 1

    a_s, b_s, c_s = symbols('a b c')
    _runtime_check("sympy: expand(a*(b+c)) == a*b + a*c",
                    expand(a_s * (b_s + c_s)),
                    a_s*b_s + a_s*c_s)

    # ── E3. Z3: commutativity of addition ────────────────────────
    r = (
        Proof("a + b == b + a")
        .using(kernel)
        .given(a="int", b="int")
        .by_z3("a + b == b + a")
        .qed()
    )
    _show("E3  a + b = b + a  [Z3 arithmetic]", result=r)
    if r.success:
        passed += 1

    _runtime_check("sympy: x + y == y + x",
                    x + y, y + x)

    # ── E4. Z3: (a - b) + b == a ─────────────────────────────────
    r = (
        Proof("(a - b) + b == a")
        .using(kernel)
        .given(a="int", b="int")
        .by_z3("(a - b) + b == a")
        .qed()
    )
    _show("E4  (a − b) + b = a  [Z3 arithmetic]", result=r)
    if r.success:
        passed += 1

    _runtime_check("sympy: simplify((x - y) + y) == x",
                    simplify((x - y) + y), x)

    # ── E5. Z3: squaring is non-negative ─────────────────────────
    r = (
        Proof("x * x >= 0")
        .using(kernel)
        .given(x="int")
        .by_z3("x * x >= 0")
        .qed()
    )
    _show("E5  x² ≥ 0  [Z3 arithmetic]", result=r)
    if r.success:
        passed += 1

    import random
    random.seed(42)
    for _ in range(5):
        v = random.randint(-100, 100)
        _runtime_check(f"({v})² = {v*v} ≥ 0",
                        v * v >= 0, True)

    _record_category("Runtime Validation", passed, total, "Z3_VERIFIED")
    return passed, total


# ═════════════════════════════════════════════════════════════════
# Report
# ═════════════════════════════════════════════════════════════════

def _print_report() -> None:
    """Print the final verification report."""
    sympy_version = sympy.__version__

    sep = "═" * 62
    thin = "─" * 62

    print(f"\n{sep}")
    print("  SynHoPy — SymPy Sidecar Verification Report")
    print(sep)
    print()
    print(f"  Module: sympy (version {sympy_version})")
    print(f"  Proof mode: SIDECAR (no sympy modification)")
    print()
    print(f"  {'Category':<24s} {'Proved':>6s}  {'Total':>5s}  {'Trust Level'}")
    print(f"  {thin}")

    total_proved = 0
    total_all = 0
    for cat in ["Algebra", "Calculus", "Linear Algebra",
                "Number Theory", "Runtime Validation"]:
        proved, tot = _CATEGORY_STATS.get(cat, (0, 0))
        trust = _CATEGORY_TRUST.get(cat, "N/A")
        total_proved += proved
        total_all += tot
        print(f"  {cat:<24s} {proved:>6d}  {tot:>5d}  {trust}")

    print(f"  {thin}")

    if total_all > 0:
        pct = total_proved * 100 // total_all
    else:
        pct = 0
    print(f"  {'TOTAL':<24s} {total_proved:>6d}  {total_all:>5d}  {pct}% verified")
    print(f"  Runtime checks: {_RUNTIME_PASS}/{_RUNTIME_TOTAL} passed")
    print()
    print("  Key insight: sympy source was NEVER modified. All proofs")
    print("  are external sidecar proofs that can be stripped away,")
    print("  leaving the original sympy library completely untouched.")
    print(sep)
    print()


# ═════════════════════════════════════════════════════════════════
# Main
# ═════════════════════════════════════════════════════════════════

def run_sidecar_verification(*, verbose: bool = False) -> tuple[int, int]:
    """Run the full sidecar verification suite.

    Returns ``(passed, total)`` proof count.
    """
    global _PASS, _FAIL, _RUNTIME_PASS, _RUNTIME_TOTAL
    _PASS = 0
    _FAIL = 0
    _RUNTIME_PASS = 0
    _RUNTIME_TOTAL = 0
    _CATEGORY_STATS.clear()
    _CATEGORY_TRUST.clear()

    sep = "═" * 62

    print()
    print(sep)
    print("  SynHoPy — SymPy Sidecar Verification Demo")
    print(f"  sympy {sympy.__version__} • proof mode: SIDECAR")
    print(sep)

    # Build a fresh kernel and install sidecar axioms
    kernel = ProofKernel()

    # Install the default library axioms for broader coverage
    from synhopy.axioms.library_axioms import default_registry
    registry = default_registry()
    registry.install_into_kernel(kernel)

    # Layer formal axiom schemas on top
    try:
        from synhopy.axioms.formal_axiom_library import install_formal_axioms
        install_formal_axioms(kernel)
    except (ImportError, AttributeError):
        pass

    n_sidecar = _install_sympy_sidecar_axioms(kernel)
    if verbose:
        print(f"\n  Installed {n_sidecar} sidecar formal axioms")

    t0 = time.perf_counter()

    # Run all proof categories
    results = [
        prove_algebra(kernel),
        prove_calculus(kernel),
        prove_linear_algebra(kernel),
        prove_number_theory(kernel),
        prove_runtime_validation(kernel),
    ]

    elapsed_ms = (time.perf_counter() - t0) * 1000

    # Report
    _print_report()

    total_proved = sum(p for p, _ in results)
    total_all = sum(t for _, t in results)

    print(f"  Elapsed: {elapsed_ms:.1f} ms")
    print()

    return total_proved, total_all


if __name__ == "__main__":
    verbose = "--verbose" in sys.argv or "-v" in sys.argv
    passed, total = run_sidecar_verification(verbose=verbose)
    raise SystemExit(total - passed)
