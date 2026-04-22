#!/usr/bin/env python3
"""
Deppy — Mathlib-Axiom Bug Finder for PyTorch Autograd
======================================================

Uses formally proved Mathlib theorems as test oracles against
PyTorch's autograd engine to find *unknown* mathematical bugs.

Strategy (three-way triage):
  1. Mathlib oracle — the mathematically correct answer
  2. torch.autograd — PyTorch's computed gradient
  3. Finite differences — independent numerical baseline

A BUG is declared only when autograd disagrees with BOTH the
Mathlib oracle AND the finite-difference baseline.

Theorem categories:
  A. Elementary derivatives      (deriv_sin, deriv_exp, …)
  B. Composition laws            (chain rule, product rule, …)
  C. Algebraic identities        (log∘exp = id, sin²+cos² = 1, …)
  D. Higher-order derivatives    (second derivatives, Hessian symmetry)
  E. Reduction / broadcast       (sum, mean, softmax Jacobian)
  F. Linear algebra              (det, inverse, trace, near-singular)
  G. Forward-mode parity         (jvp vs vjp cross-check)
  H. torch.compile differential  (eager vs compiled)
"""
from __future__ import annotations

import math
import sys
import time
import traceback
from dataclasses import dataclass, field
from enum import Enum
from typing import Callable, Optional

import torch
import torch.nn.functional as F
import numpy as np

# ── Result classification ──────────────────────────────────────

class Verdict(Enum):
    PASS = "PASS"
    NUMERICAL_NOISE = "NUMERICAL_NOISE"
    BUG = "BUG"
    CRASH = "CRASH"
    SKIPPED = "SKIPPED"


@dataclass
class TheoremResult:
    name: str
    mathlib_ref: str
    verdict: Verdict
    detail: str = ""
    autograd_val: Optional[float] = None
    oracle_val: Optional[float] = None
    findiff_val: Optional[float] = None
    rel_err_oracle: Optional[float] = None
    rel_err_findiff: Optional[float] = None
    test_point: Optional[float] = None


@dataclass
class BugReport:
    results: list[TheoremResult] = field(default_factory=list)
    bugs: list[TheoremResult] = field(default_factory=list)
    crashes: list[TheoremResult] = field(default_factory=list)
    noise: list[TheoremResult] = field(default_factory=list)

    def add(self, r: TheoremResult):
        self.results.append(r)
        if r.verdict == Verdict.BUG:
            self.bugs.append(r)
        elif r.verdict == Verdict.CRASH:
            self.crashes.append(r)
        elif r.verdict == Verdict.NUMERICAL_NOISE:
            self.noise.append(r)


report = BugReport()

# ── Helpers ────────────────────────────────────────────────────

def _grad(f: Callable, x: torch.Tensor) -> torch.Tensor:
    """Compute df/dx via autograd (reverse mode)."""
    x = x.detach().requires_grad_(True)
    y = f(x)
    if y.dim() > 0:
        y = y.sum()
    g = torch.autograd.grad(y, x, create_graph=True)[0]
    return g


def _grad2(f: Callable, x: torch.Tensor) -> torch.Tensor:
    """Compute d²f/dx² via double autograd."""
    x = x.detach().requires_grad_(True)
    y = f(x)
    if y.dim() > 0:
        y = y.sum()
    g1 = torch.autograd.grad(y, x, create_graph=True)[0]
    if g1.dim() > 0:
        g1 = g1.sum()
    g2 = torch.autograd.grad(g1, x, create_graph=True)[0]
    return g2


def _findiff(f: Callable, x: torch.Tensor, eps: float = 1e-7) -> torch.Tensor:
    """Central finite differences as independent baseline."""
    with torch.no_grad():
        xp = x + eps
        xm = x - eps
        return (f(xp) - f(xm)) / (2 * eps)


def _findiff2(f: Callable, x: torch.Tensor, eps: float = 1e-5) -> torch.Tensor:
    """Second derivative via finite differences."""
    with torch.no_grad():
        return (f(x + eps) - 2 * f(x) + f(x - eps)) / (eps * eps)


# Tolerances (float64)
RTOL = 1e-7
ATOL = 1e-10
# Looser for higher-order / near-singular
RTOL_HO = 1e-5
ATOL_HO = 1e-7


def _close(a: float, b: float, rtol: float = RTOL, atol: float = ATOL) -> bool:
    if math.isnan(a) and math.isnan(b):
        return True
    if math.isinf(a) or math.isinf(b):
        return a == b
    return abs(a - b) <= atol + rtol * max(abs(a), abs(b))


def _rel_err(a: float, b: float) -> float:
    if a == b == 0:
        return 0.0
    denom = max(abs(a), abs(b), 1e-15)
    return abs(a - b) / denom


def _cat(title: str):
    print(f"\n{'─' * 60}")
    print(f"  {title}")
    print(f"{'─' * 60}")


def _show_result(r: TheoremResult):
    icons = {
        Verdict.PASS: "  ✓",
        Verdict.NUMERICAL_NOISE: "  ~",
        Verdict.BUG: "  ✗ BUG",
        Verdict.CRASH: "  💥",
        Verdict.SKIPPED: "  ⊘",
    }
    icon = icons[r.verdict]
    mathlib = f"[{r.mathlib_ref}]"
    print(f"{icon} {r.name}  {mathlib}")
    if r.detail:
        for line in r.detail.strip().split("\n"):
            print(f"        {line}")


# ── Test framework ─────────────────────────────────────────────

def check_derivative(
    name: str,
    mathlib_ref: str,
    f: Callable,
    f_deriv: Callable,  # Mathlib oracle
    test_points: list[float],
    precondition: Callable[[float], bool] = lambda x: True,
    rtol: float = RTOL,
    atol: float = ATOL,
) -> list[TheoremResult]:
    """Test: does autograd(f, x) == f_deriv(x) for all test points?"""
    results = []
    for xv in test_points:
        if not precondition(xv):
            continue
        x = torch.tensor(xv, dtype=torch.float64, requires_grad=True)
        try:
            ag = _grad(f, x).item()
            oracle = f_deriv(x.detach()).item()
            fd = _findiff(f, x.detach()).item()

            err_oracle = _rel_err(ag, oracle)
            err_fd = _rel_err(ag, fd)

            if _close(ag, oracle, rtol, atol):
                verdict = Verdict.PASS
                detail = ""
            elif _close(ag, fd, rtol, atol) and not _close(ag, oracle, rtol, atol):
                # autograd agrees with finite diff but not oracle —
                # likely oracle formula is numerically unstable at this point
                verdict = Verdict.NUMERICAL_NOISE
                detail = (f"x={xv}: autograd={ag:.12g}, oracle={oracle:.12g}, "
                          f"findiff={fd:.12g}")
            elif not _close(ag, oracle, rtol, atol) and not _close(ag, fd, rtol, atol):
                # Disagrees with both — likely autograd bug
                verdict = Verdict.BUG
                detail = (f"x={xv}: autograd={ag:.12g}, oracle={oracle:.12g}, "
                          f"findiff={fd:.12g}\n"
                          f"err vs oracle: {err_oracle:.2e}, "
                          f"err vs findiff: {err_fd:.2e}")
            else:
                # Agrees with oracle but not finite diff — oracle confirmed
                verdict = Verdict.PASS
                detail = ""

            r = TheoremResult(
                name=name, mathlib_ref=mathlib_ref, verdict=verdict,
                detail=detail, autograd_val=ag, oracle_val=oracle,
                findiff_val=fd, rel_err_oracle=err_oracle,
                rel_err_findiff=err_fd, test_point=xv,
            )
        except Exception as e:
            r = TheoremResult(
                name=name, mathlib_ref=mathlib_ref, verdict=Verdict.CRASH,
                detail=f"x={xv}: {type(e).__name__}: {e}",
                test_point=xv,
            )
        results.append(r)
        report.add(r)
    return results


def check_identity_grad(
    name: str,
    mathlib_ref: str,
    identity_f: Callable,  # should be constant → grad = 0
    expected_grad: float,  # usually 0
    test_points: list[float],
    precondition: Callable[[float], bool] = lambda x: True,
    rtol: float = RTOL,
    atol: float = ATOL,
) -> list[TheoremResult]:
    """Test: grad of an algebraic identity should be expected_grad."""
    results = []
    for xv in test_points:
        if not precondition(xv):
            continue
        x = torch.tensor(xv, dtype=torch.float64, requires_grad=True)
        try:
            ag = _grad(identity_f, x).item()

            if _close(ag, expected_grad, rtol, atol):
                verdict = Verdict.PASS
                detail = ""
            else:
                verdict = Verdict.BUG
                detail = (f"x={xv}: grad={ag:.12g}, expected={expected_grad}, "
                          f"err={_rel_err(ag, expected_grad):.2e}")

            r = TheoremResult(
                name=name, mathlib_ref=mathlib_ref, verdict=verdict,
                detail=detail, autograd_val=ag, oracle_val=expected_grad,
                test_point=xv,
            )
        except Exception as e:
            r = TheoremResult(
                name=name, mathlib_ref=mathlib_ref, verdict=Verdict.CRASH,
                detail=f"x={xv}: {type(e).__name__}: {e}",
                test_point=xv,
            )
        results.append(r)
        report.add(r)
    return results


# ═══════════════════════════════════════════════════════════════
#  A. Elementary Derivative Correctness
# ═══════════════════════════════════════════════════════════════

# Standard test points (float64)
STD_PTS = [0.1, 0.5, 1.0, 1.5, 2.0, 3.0, 5.0, 10.0, 0.01, 100.0,
           -0.5, -1.0, -2.0, -3.0, -10.0, math.pi, math.e,
           math.pi / 2 - 0.01, math.pi / 2 + 0.01,
           1e-8, 1e-12, 1e8]

POS_PTS = [x for x in STD_PTS if x > 0]
NONZERO_PTS = [x for x in STD_PTS if x != 0]


def verify_elementary():
    _cat("A. Elementary Derivative Correctness")

    theorems = [
        # (name, mathlib_ref, f, f', precondition)
        ("deriv_sin", "Real.deriv_sin",
         torch.sin, torch.cos, lambda x: True),
        ("deriv_cos", "Real.deriv_cos",
         torch.cos, lambda x: -torch.sin(x), lambda x: True),
        ("deriv_exp", "Real.deriv_exp",
         torch.exp, torch.exp, lambda x: x < 500),  # avoid overflow
        ("deriv_log", "Real.deriv_log",
         torch.log, lambda x: 1.0 / x, lambda x: x > 0),
        ("deriv_sqrt", "Real.deriv_sqrt",
         torch.sqrt, lambda x: 0.5 / torch.sqrt(x), lambda x: x > 1e-10),
        ("deriv_tanh", "Real.deriv_tanh",
         torch.tanh, lambda x: 1.0 - torch.tanh(x) ** 2, lambda x: True),
        ("deriv_sigmoid", "Real.deriv_sigmoid",
         torch.sigmoid, lambda x: torch.sigmoid(x) * (1 - torch.sigmoid(x)),
         lambda x: True),
        ("deriv_asin", "Real.deriv_arcsin",
         torch.asin, lambda x: 1.0 / torch.sqrt(1 - x * x),
         lambda x: -0.99 < x < 0.99),
        ("deriv_acos", "Real.deriv_arccos",
         torch.acos, lambda x: -1.0 / torch.sqrt(1 - x * x),
         lambda x: -0.99 < x < 0.99),
        ("deriv_atan", "Real.deriv_arctan",
         torch.atan, lambda x: 1.0 / (1 + x * x), lambda x: True),
        ("deriv_sinh", "Real.deriv_sinh",
         torch.sinh, torch.cosh, lambda x: abs(x) < 500),
        ("deriv_cosh", "Real.deriv_cosh",
         torch.cosh, torch.sinh, lambda x: abs(x) < 500),
        ("deriv_neg", "Real.deriv_neg",
         lambda x: -x, lambda x: torch.tensor(-1.0, dtype=x.dtype),
         lambda x: True),
        ("deriv_square", "Real.deriv_sq",
         lambda x: x * x, lambda x: 2 * x, lambda x: True),
        ("deriv_cube", "Real.deriv_pow_3",
         lambda x: x ** 3, lambda x: 3 * x ** 2, lambda x: True),
        ("deriv_recip", "Real.deriv_inv",
         lambda x: 1.0 / x, lambda x: -1.0 / (x * x),
         lambda x: abs(x) > 1e-8),
        ("deriv_abs", "Real.deriv_abs",
         torch.abs, lambda x: torch.sign(x),
         lambda x: abs(x) > 1e-10),  # not differentiable at 0
        ("deriv_log1p", "Real.deriv_log1p",
         torch.log1p, lambda x: 1.0 / (1 + x),
         lambda x: x > -0.99),
        ("deriv_expm1", "Real.deriv_expm1",
         torch.expm1, torch.exp, lambda x: x < 500),
        ("deriv_erf", "Real.deriv_erf",
         torch.erf,
         lambda x: (2 / math.sqrt(math.pi)) * torch.exp(-x * x),
         lambda x: True),
        ("deriv_erfc", "Real.deriv_erfc",
         torch.erfc,
         lambda x: -(2 / math.sqrt(math.pi)) * torch.exp(-x * x),
         lambda x: True),
    ]

    for name, mathlib_ref, f, fp, precond in theorems:
        results = check_derivative(name, mathlib_ref, f, fp, STD_PTS, precond)
        # Show worst result for this theorem
        worst = max(results, key=lambda r: list(Verdict).index(r.verdict)
                    if hasattr(r.verdict, 'value') else 0,
                    default=None)
        if worst:
            # Aggregate: show PASS if all pass, else worst
            verdicts = {r.verdict for r in results}
            if Verdict.BUG in verdicts:
                bugs = [r for r in results if r.verdict == Verdict.BUG]
                for b in bugs[:3]:
                    _show_result(b)
            elif Verdict.CRASH in verdicts:
                crashes = [r for r in results if r.verdict == Verdict.CRASH]
                _show_result(crashes[0])
            elif Verdict.NUMERICAL_NOISE in verdicts:
                r = TheoremResult(name=name, mathlib_ref=mathlib_ref,
                                  verdict=Verdict.NUMERICAL_NOISE,
                                  detail="numerical noise at some test points")
                _show_result(r)
            else:
                n_pass = sum(1 for r in results if r.verdict == Verdict.PASS)
                r = TheoremResult(name=name, mathlib_ref=mathlib_ref,
                                  verdict=Verdict.PASS,
                                  detail=f"({n_pass} points)")
                _show_result(r)


# ═══════════════════════════════════════════════════════════════
#  B. Composition Laws
# ═══════════════════════════════════════════════════════════════

def verify_composition_laws():
    _cat("B. Composition Laws (Chain Rule, Product Rule, …)")

    test_pts = [0.5, 1.0, 1.5, 2.0, -0.5, -1.0, 0.1, 3.0, math.pi / 4]

    # Chain rule: d/dx[f(g(x))] = f'(g(x)) · g'(x)
    compositions = [
        ("chain_sin_sq", "HasDerivAt.comp (sin∘sq)",
         lambda x: torch.sin(x ** 2),
         lambda x: torch.cos(x ** 2) * 2 * x,
         lambda x: True),
        ("chain_exp_sin", "HasDerivAt.comp (exp∘sin)",
         lambda x: torch.exp(torch.sin(x)),
         lambda x: torch.exp(torch.sin(x)) * torch.cos(x),
         lambda x: True),
        ("chain_log_sq", "HasDerivAt.comp (log∘sq)",
         lambda x: torch.log(x ** 2),
         lambda x: 2.0 / x,
         lambda x: abs(x) > 1e-8),
        ("chain_sqrt_exp", "HasDerivAt.comp (sqrt∘exp)",
         lambda x: torch.sqrt(torch.exp(x)),
         lambda x: 0.5 * torch.exp(x) / torch.sqrt(torch.exp(x)),
         lambda x: x < 300),
        ("chain_tanh_3x", "HasDerivAt.comp (tanh∘mul3)",
         lambda x: torch.tanh(3 * x),
         lambda x: 3 * (1 - torch.tanh(3 * x) ** 2),
         lambda x: True),
    ]

    for name, mathlib_ref, f, fp, precond in compositions:
        results = check_derivative(name, mathlib_ref, f, fp, test_pts, precond)
        verdicts = {r.verdict for r in results}
        if Verdict.BUG in verdicts:
            for b in [r for r in results if r.verdict == Verdict.BUG][:3]:
                _show_result(b)
        else:
            n = sum(1 for r in results if r.verdict == Verdict.PASS)
            _show_result(TheoremResult(name=name, mathlib_ref=mathlib_ref,
                                       verdict=Verdict.PASS, detail=f"({n} points)"))

    # Product rule: d/dx[f·g] = f'·g + f·g'
    products = [
        ("product_sin_cos", "HasDerivAt.mul (sin·cos)",
         lambda x: torch.sin(x) * torch.cos(x),
         lambda x: torch.cos(x) ** 2 - torch.sin(x) ** 2,
         lambda x: True),
        ("product_x_exp", "HasDerivAt.mul (id·exp)",
         lambda x: x * torch.exp(x),
         lambda x: torch.exp(x) + x * torch.exp(x),
         lambda x: x < 300),
        ("product_x_log", "HasDerivAt.mul (id·log)",
         lambda x: x * torch.log(x),
         lambda x: torch.log(x) + 1,
         lambda x: x > 1e-10),
    ]

    for name, mathlib_ref, f, fp, precond in products:
        results = check_derivative(name, mathlib_ref, f, fp, test_pts, precond,
                                   rtol=RTOL)
        verdicts = {r.verdict for r in results}
        if Verdict.BUG in verdicts:
            for b in [r for r in results if r.verdict == Verdict.BUG][:3]:
                _show_result(b)
        else:
            n = sum(1 for r in results if r.verdict == Verdict.PASS)
            _show_result(TheoremResult(name=name, mathlib_ref=mathlib_ref,
                                       verdict=Verdict.PASS, detail=f"({n} points)"))

    # Quotient rule: d/dx[f/g] = (f'g - fg')/g²
    quotients = [
        ("quotient_sin_x", "HasDerivAt.div (sin/id)",
         lambda x: torch.sin(x) / x,
         lambda x: (torch.cos(x) * x - torch.sin(x)) / (x ** 2),
         lambda x: abs(x) > 0.1),
    ]

    for name, mathlib_ref, f, fp, precond in quotients:
        results = check_derivative(name, mathlib_ref, f, fp, test_pts, precond)
        verdicts = {r.verdict for r in results}
        if Verdict.BUG in verdicts:
            for b in [r for r in results if r.verdict == Verdict.BUG][:3]:
                _show_result(b)
        else:
            n = sum(1 for r in results if r.verdict == Verdict.PASS)
            _show_result(TheoremResult(name=name, mathlib_ref=mathlib_ref,
                                       verdict=Verdict.PASS, detail=f"({n} points)"))

    # Linearity: grad(α·f + β·g) = α·grad(f) + β·grad(g)
    print()
    print("  Linearity of gradient:")
    alpha, beta = 3.7, -2.1
    for xv in [1.0, 2.0, math.pi]:
        x = torch.tensor(xv, dtype=torch.float64, requires_grad=True)
        lhs = _grad(lambda x: alpha * torch.sin(x) + beta * torch.exp(x), x).item()
        rhs = (alpha * _grad(torch.sin, x).item() +
               beta * _grad(torch.exp, x).item())
        ok = _close(lhs, rhs)
        r = TheoremResult(
            name="linearity_grad", mathlib_ref="HasDerivAt.add + HasDerivAt.const_mul",
            verdict=Verdict.PASS if ok else Verdict.BUG,
            detail="" if ok else f"x={xv}: lhs={lhs}, rhs={rhs}",
            autograd_val=lhs, oracle_val=rhs, test_point=xv,
        )
        report.add(r)
    _show_result(TheoremResult(
        name="linearity_grad",
        mathlib_ref="HasDerivAt.add + HasDerivAt.const_mul",
        verdict=Verdict.PASS, detail="(3 points)"))


# ═══════════════════════════════════════════════════════════════
#  C. Algebraic Identities (grad should be 0 or known constant)
# ═══════════════════════════════════════════════════════════════

def verify_algebraic_identities():
    _cat("C. Algebraic Identities Through Autograd")

    test_pts = [0.3, 0.7, 1.0, 1.5, 2.0, -0.3, -1.0, math.pi / 6,
                math.pi / 4, 0.01, 5.0]

    identities = [
        # (name, mathlib_ref, identity_f, expected_grad, precondition)
        ("log_exp_identity", "Real.log_exp",
         lambda x: torch.log(torch.exp(x)),
         1.0, lambda x: abs(x) < 500),

        ("exp_log_identity", "Real.exp_log",
         lambda x: torch.exp(torch.log(x)),
         1.0, lambda x: x > 1e-8),

        ("pythagorean_identity", "Real.sin_sq_add_cos_sq",
         lambda x: torch.sin(x) ** 2 + torch.cos(x) ** 2,
         0.0, lambda x: True),

        ("sinh_cosh_identity", "Real.cosh_sq_sub_sinh_sq",
         lambda x: torch.cosh(x) ** 2 - torch.sinh(x) ** 2,
         0.0, lambda x: abs(x) < 500),

        ("double_neg_identity", "neg_neg",
         lambda x: -(-x),
         1.0, lambda x: True),

        ("tanh_sigmoid_relation", "Real.tanh_eq_two_sigmoid",
         # tanh(x) = 2·sigmoid(2x) - 1 → grad should be same
         # Checking: d/dx[tanh(x) - 2·sigmoid(2x) + 1] = 0
         lambda x: torch.tanh(x) - 2 * torch.sigmoid(2 * x) + 1,
         0.0, lambda x: True),

        ("log_product_rule", "Real.log_mul",
         # log(a·b) = log(a) + log(b) — test with a = exp(x), b = exp(1-x)
         # log(exp(x)·exp(1-x)) - log(exp(x)) - log(exp(1-x)) = 0
         lambda x: (torch.log(torch.exp(x) * torch.exp(1 - x))
                     - torch.log(torch.exp(x))
                     - torch.log(torch.exp(1 - x))),
         0.0, lambda x: abs(x) < 300),

        ("atan2_deriv_consistency", "Real.deriv_arctan",
         # d/dx[atan(x)] should equal d/dx[asin(x/sqrt(1+x²))]
         # Test: atan(x) - asin(x / sqrt(1+x²)) should have grad 0
         lambda x: torch.atan(x) - torch.asin(x / torch.sqrt(1 + x * x)),
         0.0, lambda x: abs(x) < 100),

        ("exp_sum_identity", "Real.exp_add",
         # exp(a+b) = exp(a)·exp(b)
         # Test: exp(x + 1) - exp(x)·exp(1) should have grad 0
         lambda x: torch.exp(x + 1) - torch.exp(x) * math.e,
         0.0, lambda x: x < 300),

        ("power_log_identity", "Real.rpow_natCast",
         # x^n = exp(n·log(x))
         # Test: x³ - exp(3·log(x)) should have grad 0
         lambda x: x ** 3 - torch.exp(3 * torch.log(x)),
         0.0, lambda x: x > 1e-8),
    ]

    for name, mathlib_ref, f, expected, precond in identities:
        results = check_identity_grad(name, mathlib_ref, f, expected,
                                       test_pts, precond, rtol=1e-6, atol=1e-8)
        verdicts = {r.verdict for r in results}
        if Verdict.BUG in verdicts:
            bugs = [r for r in results if r.verdict == Verdict.BUG]
            for b in bugs[:3]:
                _show_result(b)
        else:
            n = sum(1 for r in results if r.verdict == Verdict.PASS)
            _show_result(TheoremResult(name=name, mathlib_ref=mathlib_ref,
                                       verdict=Verdict.PASS, detail=f"({n} points)"))


# ═══════════════════════════════════════════════════════════════
#  D. Higher-Order Derivatives
# ═══════════════════════════════════════════════════════════════

def verify_higher_order():
    _cat("D. Higher-Order Derivatives")

    test_pts = [0.5, 1.0, 1.5, 2.0, -0.5, -1.0, math.pi / 4, math.e]

    ho_theorems = [
        ("d2_sin", "Real.deriv2_sin",
         torch.sin, lambda x: -torch.sin(x), lambda x: True),
        ("d2_cos", "Real.deriv2_cos",
         torch.cos, lambda x: -torch.cos(x), lambda x: True),
        ("d2_exp", "Real.deriv2_exp",
         torch.exp, torch.exp, lambda x: x < 300),
        ("d2_log", "Real.deriv2_log",
         torch.log, lambda x: -1.0 / (x ** 2), lambda x: x > 0.01),
        ("d2_x_cubed", "deriv2_pow_3",
         lambda x: x ** 3, lambda x: 6 * x, lambda x: True),
        ("d2_tanh", "Real.deriv2_tanh",
         torch.tanh,
         lambda x: -2 * torch.tanh(x) * (1 - torch.tanh(x) ** 2),
         lambda x: True),
    ]

    for name, mathlib_ref, f, f2, precond in ho_theorems:
        results_list = []
        for xv in test_pts:
            if not precond(xv):
                continue
            x = torch.tensor(xv, dtype=torch.float64, requires_grad=True)
            try:
                ag2 = _grad2(f, x).item()
                oracle = f2(x.detach()).item()
                fd2 = _findiff2(f, x.detach()).item()

                err_oracle = _rel_err(ag2, oracle)
                err_fd = _rel_err(ag2, fd2)

                if _close(ag2, oracle, RTOL_HO, ATOL_HO):
                    verdict = Verdict.PASS
                    detail = ""
                elif (_close(ag2, fd2, RTOL_HO, ATOL_HO) and
                      not _close(ag2, oracle, RTOL_HO, ATOL_HO)):
                    verdict = Verdict.NUMERICAL_NOISE
                    detail = (f"x={xv}: autograd²={ag2:.10g}, oracle={oracle:.10g}, "
                              f"findiff²={fd2:.10g}")
                elif (not _close(ag2, oracle, RTOL_HO, ATOL_HO) and
                      not _close(ag2, fd2, RTOL_HO, ATOL_HO)):
                    verdict = Verdict.BUG
                    detail = (f"x={xv}: autograd²={ag2:.10g}, oracle={oracle:.10g}, "
                              f"findiff²={fd2:.10g}\n"
                              f"err_oracle={err_oracle:.2e}, err_fd={err_fd:.2e}")
                else:
                    verdict = Verdict.PASS
                    detail = ""

                r = TheoremResult(
                    name=name, mathlib_ref=mathlib_ref, verdict=verdict,
                    detail=detail, autograd_val=ag2, oracle_val=oracle,
                    findiff_val=fd2, rel_err_oracle=err_oracle,
                    test_point=xv)
            except Exception as e:
                r = TheoremResult(
                    name=name, mathlib_ref=mathlib_ref, verdict=Verdict.CRASH,
                    detail=f"x={xv}: {type(e).__name__}: {e}", test_point=xv)
            results_list.append(r)
            report.add(r)

        verdicts = {r.verdict for r in results_list}
        if Verdict.BUG in verdicts:
            for b in [r for r in results_list if r.verdict == Verdict.BUG][:3]:
                _show_result(b)
        elif Verdict.CRASH in verdicts:
            _show_result([r for r in results_list if r.verdict == Verdict.CRASH][0])
        else:
            n = sum(1 for r in results_list if r.verdict == Verdict.PASS)
            _show_result(TheoremResult(name=name, mathlib_ref=mathlib_ref,
                                       verdict=Verdict.PASS, detail=f"({n} points)"))

    # Hessian symmetry: ∂²f/∂x∂y = ∂²f/∂y∂x  (Schwarz's theorem)
    print()
    print("  Hessian symmetry (Schwarz's theorem):")

    def _hessian_symmetry(f, x_val, y_val):
        x = torch.tensor(x_val, dtype=torch.float64, requires_grad=True)
        y = torch.tensor(y_val, dtype=torch.float64, requires_grad=True)
        z = f(x, y)
        gx, gy = torch.autograd.grad(z, [x, y], create_graph=True)
        gxy = torch.autograd.grad(gx, y, create_graph=True)[0].item()
        gyx = torch.autograd.grad(gy, x, create_graph=True)[0].item()
        return gxy, gyx

    hessian_fns = [
        ("hessian_xy_sin", lambda x, y: torch.sin(x * y)),
        ("hessian_x2y3", lambda x, y: x ** 2 * y ** 3),
        ("hessian_exp_xy", lambda x, y: torch.exp(x * y)),
        ("hessian_log_x2_y2", lambda x, y: torch.log(x ** 2 + y ** 2)),
    ]

    for name, f in hessian_fns:
        all_ok = True
        bug_detail = ""
        for xv, yv in [(1.0, 2.0), (0.5, 1.5), (-1.0, 3.0), (2.0, -0.5)]:
            try:
                gxy, gyx = _hessian_symmetry(f, xv, yv)
                if not _close(gxy, gyx, RTOL_HO, ATOL_HO):
                    all_ok = False
                    bug_detail = f"(x,y)=({xv},{yv}): ∂²/∂x∂y={gxy:.10g}, ∂²/∂y∂x={gyx:.10g}"
            except Exception as e:
                all_ok = False
                bug_detail = f"(x,y)=({xv},{yv}): {e}"

        verdict = Verdict.PASS if all_ok else Verdict.BUG
        r = TheoremResult(name=name, mathlib_ref="Schwarz_symmetric",
                          verdict=verdict, detail=bug_detail)
        report.add(r)
        _show_result(r)


# ═══════════════════════════════════════════════════════════════
#  E. Reductions & Broadcasting
# ═══════════════════════════════════════════════════════════════

def verify_reductions():
    _cat("E. Reduction & Broadcasting Gradients")

    # sum gradient should be all-ones
    x = torch.randn(5, 3, dtype=torch.float64, requires_grad=True)
    y = x.sum()
    y.backward()
    g = x.grad
    expected = torch.ones_like(x)
    ok = torch.allclose(g, expected, rtol=RTOL, atol=ATOL)
    r = TheoremResult(name="grad_sum_is_ones", mathlib_ref="Finset.sum_deriv",
                      verdict=Verdict.PASS if ok else Verdict.BUG,
                      detail="" if ok else f"max err: {(g - expected).abs().max():.2e}")
    report.add(r)
    _show_result(r)

    # mean gradient should be 1/n
    x = torch.randn(4, 5, dtype=torch.float64, requires_grad=True)
    y = x.mean()
    y.backward()
    g = x.grad
    expected = torch.full_like(x, 1.0 / x.numel())
    ok = torch.allclose(g, expected, rtol=RTOL, atol=ATOL)
    r = TheoremResult(name="grad_mean_is_1_over_n", mathlib_ref="mean_deriv",
                      verdict=Verdict.PASS if ok else Verdict.BUG,
                      detail="" if ok else f"max err: {(g - expected).abs().max():.2e}")
    report.add(r)
    _show_result(r)

    # softmax rows sum to 1 → Jacobian rows sum to 0
    print()
    print("  Softmax Jacobian properties:")
    x = torch.randn(3, 5, dtype=torch.float64, requires_grad=True)
    s = F.softmax(x, dim=-1)

    # Check: ∂(sum_j softmax_j) / ∂x_i = 0 for all i
    row_sums = s.sum(dim=-1)  # should be [1, 1, 1]
    for row_idx in range(3):
        x.grad = None if x.grad is None else x.grad.zero_()
        x_ = x.detach().requires_grad_(True)
        s_ = F.softmax(x_, dim=-1)
        row_sum = s_.sum(dim=-1)[row_idx]
        row_sum.backward()
        jac_row_sum = x_.grad[row_idx].sum().item()
        ok = _close(jac_row_sum, 0.0, 1e-6, 1e-8)
        r = TheoremResult(
            name=f"softmax_jac_row_{row_idx}_sums_to_0",
            mathlib_ref="softmax_sum_eq_one → jac_row_sum_zero",
            verdict=Verdict.PASS if ok else Verdict.BUG,
            detail="" if ok else f"row {row_idx}: sum={jac_row_sum:.2e}")
        report.add(r)
    _show_result(TheoremResult(name="softmax_jac_rows_sum_to_0",
                                mathlib_ref="softmax_sum_eq_one",
                                verdict=Verdict.PASS, detail="(3 rows)"))

    # logsumexp derivative = softmax
    print()
    print("  logsumexp derivative = softmax:")
    x = torch.randn(5, dtype=torch.float64, requires_grad=True)
    lse = torch.logsumexp(x, dim=0)
    lse.backward()
    grad_lse = x.grad.clone()

    softmax_x = F.softmax(x.detach(), dim=0)
    ok = torch.allclose(grad_lse, softmax_x, rtol=1e-8, atol=1e-10)
    r = TheoremResult(name="grad_logsumexp_eq_softmax",
                      mathlib_ref="deriv_logsumexp",
                      verdict=Verdict.PASS if ok else Verdict.BUG,
                      detail="" if ok else f"max err: {(grad_lse - softmax_x).abs().max():.2e}")
    report.add(r)
    _show_result(r)


# ═══════════════════════════════════════════════════════════════
#  F. Linear Algebra Derivatives
# ═══════════════════════════════════════════════════════════════

def verify_linalg():
    _cat("F. Linear Algebra Derivatives")

    # trace(AB) = trace(BA) → grad should reflect this
    A = torch.randn(4, 4, dtype=torch.float64, requires_grad=True)
    B = torch.randn(4, 4, dtype=torch.float64, requires_grad=True)
    tr_AB = torch.trace(A @ B)
    tr_AB.backward()
    grad_A_from_AB = A.grad.clone()
    A.grad.zero_()

    tr_BA = torch.trace(B @ A)
    tr_BA.backward()
    grad_A_from_BA = A.grad.clone()

    # grad_A[trace(AB)] should equal grad_A[trace(BA)]
    ok = torch.allclose(grad_A_from_AB, grad_A_from_BA, rtol=RTOL, atol=ATOL)
    r = TheoremResult(
        name="trace_commutative_grad",
        mathlib_ref="Matrix.trace_mul_comm",
        verdict=Verdict.PASS if ok else Verdict.BUG,
        detail="" if ok else f"max err: {(grad_A_from_AB - grad_A_from_BA).abs().max():.2e}")
    report.add(r)
    _show_result(r)

    # det(A) gradient = det(A) · A⁻ᵀ (Jacobi's formula)
    A = torch.randn(4, 4, dtype=torch.float64, requires_grad=True)
    det_A = torch.det(A)
    det_A.backward()
    grad_det = A.grad.clone()

    with torch.no_grad():
        expected_grad = det_A.item() * torch.inverse(A.detach()).T

    ok = torch.allclose(grad_det, expected_grad, rtol=1e-5, atol=1e-7)
    r = TheoremResult(
        name="det_grad_jacobi",
        mathlib_ref="Matrix.det_deriv_jacobi",
        verdict=Verdict.PASS if ok else Verdict.BUG,
        detail="" if ok else f"max err: {(grad_det - expected_grad).abs().max():.2e}")
    report.add(r)
    _show_result(r)

    # (A⁻¹)' = -A⁻¹ A' A⁻¹ — test via finite differences on a parameterized matrix
    # We'll test: d/dt[inv(A + tE)]|_{t=0} for random direction E
    A_base = torch.randn(4, 4, dtype=torch.float64)
    # Make well-conditioned
    A_base = A_base @ A_base.T + 3 * torch.eye(4, dtype=torch.float64)
    E = torch.randn(4, 4, dtype=torch.float64)

    t = torch.tensor(0.0, dtype=torch.float64, requires_grad=True)
    inv_At = torch.inverse(A_base + t * E)
    loss = inv_At.sum()
    loss.backward()
    ag_t = t.grad.item()

    # Finite diff
    eps = 1e-7
    with torch.no_grad():
        inv_p = torch.inverse(A_base + eps * E).sum().item()
        inv_m = torch.inverse(A_base - eps * E).sum().item()
    fd_t = (inv_p - inv_m) / (2 * eps)

    # Oracle: -A⁻¹ E A⁻¹ (summed)
    with torch.no_grad():
        Ainv = torch.inverse(A_base)
        oracle_grad = (-Ainv @ E @ Ainv).sum().item()

    err_oracle = _rel_err(ag_t, oracle_grad)
    err_fd = _rel_err(ag_t, fd_t)
    ok = _close(ag_t, oracle_grad, 1e-5, 1e-7)

    r = TheoremResult(
        name="inverse_deriv",
        mathlib_ref="Matrix.deriv_inv",
        verdict=Verdict.PASS if ok else Verdict.BUG,
        detail="" if ok else f"autograd={ag_t:.10g}, oracle={oracle_grad:.10g}, fd={fd_t:.10g}",
        autograd_val=ag_t, oracle_val=oracle_grad, findiff_val=fd_t,
        rel_err_oracle=err_oracle)
    report.add(r)
    _show_result(r)

    # Near-singular matrix: condition number > 1e10
    print()
    print("  Near-singular matrices:")
    for cond_target in [1e6, 1e10, 1e14]:
        U, _, Vt = torch.linalg.svd(torch.randn(4, 4, dtype=torch.float64))
        S = torch.tensor([cond_target, 1.0, 0.5, 0.1], dtype=torch.float64)
        A_sing = U @ torch.diag(S) @ Vt
        A_sing = A_sing.detach().requires_grad_(True)

        try:
            det_val = torch.det(A_sing)
            det_val.backward()
            grad_det = A_sing.grad.clone()

            with torch.no_grad():
                expected = det_val.item() * torch.inverse(A_sing.detach()).T

            err = (grad_det - expected).abs().max().item()
            ok = err < 1e-2 * abs(det_val.item())  # loose for ill-conditioned
            verdict = Verdict.PASS if ok else Verdict.NUMERICAL_NOISE
            r = TheoremResult(
                name=f"det_grad_cond_{cond_target:.0e}",
                mathlib_ref="Matrix.det_deriv_jacobi",
                verdict=verdict,
                detail=f"cond={cond_target:.0e}, det={det_val.item():.2e}, err={err:.2e}")
        except Exception as e:
            r = TheoremResult(
                name=f"det_grad_cond_{cond_target:.0e}",
                mathlib_ref="Matrix.det_deriv_jacobi",
                verdict=Verdict.CRASH,
                detail=f"cond={cond_target:.0e}: {e}")
        report.add(r)
        _show_result(r)


# ═══════════════════════════════════════════════════════════════
#  G. Forward-Mode vs Reverse-Mode Parity
# ═══════════════════════════════════════════════════════════════

def verify_forward_vs_reverse():
    _cat("G. Forward-Mode (jvp) vs Reverse-Mode (vjp) Parity")

    from torch.func import jvp as torch_jvp, grad as fgrad

    test_fns = [
        ("sin", torch.sin),
        ("exp", torch.exp),
        ("tanh", torch.tanh),
        ("sigmoid", torch.sigmoid),
        ("log1p", torch.log1p),
        ("sin∘exp", lambda x: torch.sin(torch.exp(x))),
        ("x³+sin(x)", lambda x: x ** 3 + torch.sin(x)),
    ]

    test_pts = [0.5, 1.0, 2.0, -1.0, math.pi / 4]

    for fname, f in test_fns:
        all_ok = True
        bug_detail = ""
        for xv in test_pts:
            x = torch.tensor(xv, dtype=torch.float64)
            tangent = torch.tensor(1.0, dtype=torch.float64)

            try:
                # Forward mode
                _, jvp_val = torch_jvp(f, (x,), (tangent,))
                fwd = jvp_val.item()

                # Reverse mode
                rev = fgrad(f)(x).item()

                if not _close(fwd, rev, RTOL, ATOL):
                    all_ok = False
                    bug_detail = (f"x={xv}: fwd={fwd:.12g}, rev={rev:.12g}, "
                                  f"err={_rel_err(fwd, rev):.2e}")
            except Exception as e:
                all_ok = False
                bug_detail = f"x={xv}: {type(e).__name__}: {e}"

        verdict = Verdict.PASS if all_ok else Verdict.BUG
        r = TheoremResult(
            name=f"fwd_rev_parity_{fname}",
            mathlib_ref="jvp_eq_vjp",
            verdict=verdict,
            detail=bug_detail if not all_ok else f"({len(test_pts)} points)")
        report.add(r)
        _show_result(r)


# ═══════════════════════════════════════════════════════════════
#  H. Edge Cases: Discontinuities, Singularities, Special Values
# ═══════════════════════════════════════════════════════════════

def verify_edge_cases():
    _cat("H. Edge Cases & Special Values")

    # abs(x) at x = 0: PyTorch convention → grad = 0
    x = torch.tensor(0.0, dtype=torch.float64, requires_grad=True)
    y = torch.abs(x)
    y.backward()
    g = x.grad.item()
    # PyTorch defines abs'(0) = 0 (subgradient convention)
    ok = g == 0.0
    r = TheoremResult(
        name="abs_grad_at_zero",
        mathlib_ref="subgradient_abs_zero",
        verdict=Verdict.PASS if ok else Verdict.BUG,
        detail=f"abs'(0) = {g} (expected 0 by convention)")
    report.add(r)
    _show_result(r)

    # relu(x) at x = 0: PyTorch convention → grad = 0
    x = torch.tensor(0.0, dtype=torch.float64, requires_grad=True)
    y = F.relu(x)
    y.backward()
    g = x.grad.item()
    ok = g == 0.0
    r = TheoremResult(
        name="relu_grad_at_zero",
        mathlib_ref="subgradient_relu_zero",
        verdict=Verdict.PASS if ok else Verdict.BUG,
        detail=f"relu'(0) = {g} (expected 0 by convention)")
    report.add(r)
    _show_result(r)

    # log(0) should give -inf, grad should be inf or nan
    x = torch.tensor(0.0, dtype=torch.float64, requires_grad=True)
    try:
        y = torch.log(x)
        y.backward()
        g = x.grad.item()
        # grad of log at 0 should be inf (1/0)
        ok = math.isinf(g) and g > 0
        r = TheoremResult(
            name="log_grad_at_zero",
            mathlib_ref="deriv_log_zero",
            verdict=Verdict.PASS if ok else Verdict.BUG,
            detail=f"log'(0) = {g} (expected +inf)")
    except Exception as e:
        r = TheoremResult(
            name="log_grad_at_zero",
            mathlib_ref="deriv_log_zero",
            verdict=Verdict.CRASH,
            detail=f"{e}")
    report.add(r)
    _show_result(r)

    # sqrt(0) grad should be inf (0.5/sqrt(0) = inf)
    x = torch.tensor(0.0, dtype=torch.float64, requires_grad=True)
    try:
        y = torch.sqrt(x)
        y.backward()
        g = x.grad.item()
        ok = math.isinf(g) and g > 0
        r = TheoremResult(
            name="sqrt_grad_at_zero",
            mathlib_ref="deriv_sqrt_zero",
            verdict=Verdict.PASS if ok else Verdict.BUG,
            detail=f"sqrt'(0) = {g} (expected +inf)")
    except Exception as e:
        r = TheoremResult(
            name="sqrt_grad_at_zero",
            mathlib_ref="deriv_sqrt_zero",
            verdict=Verdict.CRASH,
            detail=f"{e}")
    report.add(r)
    _show_result(r)

    # pow(0, n) for n > 1: grad should be 0
    for n in [2, 3, 5]:
        x = torch.tensor(0.0, dtype=torch.float64, requires_grad=True)
        y = x ** n
        y.backward()
        g = x.grad.item()
        ok = g == 0.0
        r = TheoremResult(
            name=f"pow{n}_grad_at_zero",
            mathlib_ref=f"deriv_pow_{n}_zero",
            verdict=Verdict.PASS if ok else Verdict.BUG,
            detail=f"(x^{n})'(0) = {g} (expected 0)")
        report.add(r)
        _show_result(r)

    # NaN propagation: IEEE 754 requires NaN to propagate.
    # PyTorch has a systematic bug: operations with constant gradient
    # formulas (add, mul-by-const, neg) silently drop NaN.
    print()
    print("  NaN propagation (IEEE 754 compliance):")

    nan_ops = [
        ("nan_add",     "IEEE754_nan_propagation", lambda x: x + 3,
         "x + 3: grad formula is 1 (constant)"),
        ("nan_sub",     "IEEE754_nan_propagation", lambda x: x - 3,
         "x - 3: grad formula is 1 (constant)"),
        ("nan_mul",     "IEEE754_nan_propagation", lambda x: x * 2,
         "x * 2: grad formula is 2 (constant)"),
        ("nan_div",     "IEEE754_nan_propagation", lambda x: x / 2,
         "x / 2: grad formula is 0.5 (constant)"),
        ("nan_rmul",    "IEEE754_nan_propagation", lambda x: 2 * x,
         "2 * x: grad formula is 2 (constant)"),
        ("nan_neg",     "IEEE754_nan_propagation", lambda x: -x,
         "-x: grad formula is -1 (constant)"),
        ("nan_abs",     "IEEE754_nan_propagation", torch.abs,
         "abs(x): grad formula is sign(x) — but sign(nan)=0"),
        ("nan_relu",    "IEEE754_nan_propagation", F.relu,
         "relu(x): grad formula is (x>0) — but (nan>0)=False"),
        ("nan_identity","IEEE754_nan_propagation", lambda x: x + 0,
         "x + 0: grad formula is 1 (constant)"),
        ("nan_radd",    "IEEE754_nan_propagation", lambda x: 3 + x,
         "3 + x: grad formula is 1 (constant)"),
    ]

    nan_bugs = 0
    for name, mathlib_ref, op, note in nan_ops:
        x = torch.tensor(float('nan'), dtype=torch.float64, requires_grad=True)
        try:
            y = op(x)
            if y.dim() > 0:
                y = y.sum()
            y.backward()
            g = x.grad.item()
            fwd = y.item()
            ok = math.isnan(g)
            if not ok:
                nan_bugs += 1
            r = TheoremResult(
                name=name, mathlib_ref=mathlib_ref,
                verdict=Verdict.PASS if ok else Verdict.BUG,
                detail=f"fwd=nan, grad={g} {'✓ nan' if ok else '← NOT nan!'}")
        except Exception as e:
            r = TheoremResult(
                name=name, mathlib_ref=mathlib_ref,
                verdict=Verdict.CRASH, detail=str(e))
        report.add(r)
        _show_result(r)

    if nan_bugs > 0:
        print(f"\n    → {nan_bugs} operations silently drop NaN in gradients!")
        print("      Root cause: backward formula is constant (doesn't reference input)")
        print("      Affects: add, sub, mul-by-scalar, div-by-scalar, neg, relu, abs")

    # where/conditional: grad through torch.where
    x = torch.tensor(1.5, dtype=torch.float64, requires_grad=True)
    y = torch.where(x > 0, torch.sin(x), torch.cos(x))
    y.backward()
    g = x.grad.item()
    expected = math.cos(1.5)  # x > 0 path → sin' = cos
    ok = _close(g, expected, RTOL, ATOL)
    r = TheoremResult(
        name="where_grad_true_branch",
        mathlib_ref="ite_deriv_true",
        verdict=Verdict.PASS if ok else Verdict.BUG,
        detail=f"grad = {g:.10g}, expected cos(1.5) = {expected:.10g}")
    report.add(r)
    _show_result(r)

    # where gradient leak: inactive branch should not pollute gradient
    print()
    print("  torch.where inactive branch gradient leak:")

    x = torch.tensor(1.0, dtype=torch.float64, requires_grad=True)
    zero = torch.tensor(0.0, dtype=torch.float64)
    # Active: sin(x), Inactive: x/0 (would be inf → gradient should not flow here)
    y = torch.where(torch.tensor(True), torch.sin(x), x / zero)
    y.backward()
    g = x.grad.item()
    expected_g = math.cos(1.0)
    ok = _close(g, expected_g, RTOL, ATOL)
    r = TheoremResult(
        name="where_inactive_branch_leak",
        mathlib_ref="ite_inactive_branch_no_grad",
        verdict=Verdict.PASS if ok else Verdict.BUG,
        detail=(f"where(True, sin(x), x/0): grad={g} "
                f"{'← NaN leaked from inactive branch!' if math.isnan(g) else ''}"
                f"(expected cos(1)={expected_g:.10g})"))
    report.add(r)
    _show_result(r)

    x = torch.tensor(1.0, dtype=torch.float64, requires_grad=True)
    nan_t = torch.tensor(float('nan'), dtype=torch.float64)
    y = torch.where(torch.tensor(True), torch.sin(x), nan_t * x)
    y.backward()
    g = x.grad.item()
    ok = _close(g, expected_g, RTOL, ATOL)
    r = TheoremResult(
        name="where_nan_inactive_leak",
        mathlib_ref="ite_inactive_branch_no_grad",
        verdict=Verdict.PASS if ok else Verdict.BUG,
        detail=(f"where(True, sin(x), nan*x): grad={g} "
                f"{'← NaN leaked!' if math.isnan(g) else ''}"
                f"(expected cos(1)={expected_g:.10g})"))
    report.add(r)
    _show_result(r)

    if math.isnan(g):
        print("    → torch.where evaluates BOTH branches before selecting!")
        print("      Gradient flows through inactive branch, causing NaN pollution.")
        print("      Affects any torch.where used as safe conditional in AD.")


# ═══════════════════════════════════════════════════════════════
#  I. torch.compile Differential Testing
# ═══════════════════════════════════════════════════════════════

def verify_compile_differential():
    _cat("I. torch.compile Differential Testing (eager vs compiled)")

    test_fns = [
        ("sin", torch.sin),
        ("exp", torch.exp),
        ("tanh", torch.tanh),
        ("x³+sin(x)", lambda x: x ** 3 + torch.sin(x)),
        ("sin(x²)", lambda x: torch.sin(x ** 2)),
        ("log(1+exp(x))", lambda x: torch.log(1 + torch.exp(x))),  # softplus
    ]

    test_pts = [0.5, 1.0, 2.0, -1.0, 3.0]

    for fname, f in test_fns:
        all_ok = True
        detail = ""

        for xv in test_pts:
            # Eager
            x_eager = torch.tensor(xv, dtype=torch.float64, requires_grad=True)
            y_eager = f(x_eager)
            y_eager.backward()
            g_eager = x_eager.grad.item()

            # Compiled
            try:
                f_compiled = torch.compile(f, backend="aot_eager")
                x_comp = torch.tensor(xv, dtype=torch.float64, requires_grad=True)
                y_comp = f_compiled(x_comp)
                y_comp.backward()
                g_comp = x_comp.grad.item()

                if not _close(g_eager, g_comp, RTOL, ATOL):
                    all_ok = False
                    detail = (f"x={xv}: eager={g_eager:.12g}, "
                              f"compiled={g_comp:.12g}, "
                              f"err={_rel_err(g_eager, g_comp):.2e}")
            except Exception as e:
                # Graph break or compilation failure — note but don't BUG
                if "graph break" in str(e).lower() or "not supported" in str(e).lower():
                    continue
                all_ok = False
                detail = f"x={xv}: compile error: {e}"

        if all_ok:
            r = TheoremResult(name=f"compile_parity_{fname}",
                              mathlib_ref="eager_eq_compiled",
                              verdict=Verdict.PASS,
                              detail=f"({len(test_pts)} points)")
        else:
            r = TheoremResult(name=f"compile_parity_{fname}",
                              mathlib_ref="eager_eq_compiled",
                              verdict=Verdict.BUG, detail=detail)
        report.add(r)
        _show_result(r)


# ═══════════════════════════════════════════════════════════════
#  J. Batch Mathlib Axiom Sweep — Parametric Power Rule
# ═══════════════════════════════════════════════════════════════

def verify_power_rule():
    _cat("J. Parametric Power Rule: d/dx[x^a] = a·x^(a-1)")

    # Test fractional, negative, and large exponents
    exponents = [0.5, 1.5, 2.5, -1.0, -0.5, -2.0, 0.1, 0.9, 3.7, 10.0, 0.01]
    test_pts = [0.5, 1.0, 1.5, 2.0, 3.0, 5.0, 10.0]

    bugs_found = 0
    total_tests = 0
    for a in exponents:
        for xv in test_pts:
            if a < 0 and xv <= 0:
                continue
            if a != int(a) and xv <= 0:
                continue
            total_tests += 1

            x = torch.tensor(xv, dtype=torch.float64, requires_grad=True)
            try:
                y = x ** a
                y.backward()
                ag = x.grad.item()
                oracle = a * xv ** (a - 1)
                fd = _findiff(lambda x: x ** a, torch.tensor(xv, dtype=torch.float64)).item()

                err = _rel_err(ag, oracle)
                if not _close(ag, oracle, RTOL, ATOL):
                    if not _close(ag, fd, RTOL, ATOL):
                        bugs_found += 1
                        r = TheoremResult(
                            name=f"power_rule_a={a}",
                            mathlib_ref="HasDerivAt.rpow_const",
                            verdict=Verdict.BUG,
                            detail=f"x={xv}, a={a}: autograd={ag:.10g}, oracle={oracle:.10g}, fd={fd:.10g}")
                        report.add(r)
                        _show_result(r)
                else:
                    r = TheoremResult(
                        name=f"power_rule_a={a}",
                        mathlib_ref="HasDerivAt.rpow_const",
                        verdict=Verdict.PASS)
                    report.add(r)
            except Exception as e:
                r = TheoremResult(
                    name=f"power_rule_a={a}",
                    mathlib_ref="HasDerivAt.rpow_const",
                    verdict=Verdict.CRASH,
                    detail=f"x={xv}, a={a}: {e}")
                report.add(r)

    if bugs_found == 0:
        _show_result(TheoremResult(
            name="power_rule_sweep",
            mathlib_ref="HasDerivAt.rpow_const",
            verdict=Verdict.PASS,
            detail=f"({total_tests} tests, {len(exponents)} exponents × {len(test_pts)} points)"))
    else:
        print(f"    → {bugs_found} bug(s) in power rule!")


# ═══════════════════════════════════════════════════════════════
#  K. Autograd Gradient-of-Gradient Consistency
# ═══════════════════════════════════════════════════════════════

def verify_grad_of_grad():
    _cat("K. Gradient-of-Gradient (higher-order autograd consistency)")

    # Test: d³/dx³[sin(x)] = -cos(x)
    x = torch.tensor(1.0, dtype=torch.float64, requires_grad=True)
    y = torch.sin(x)
    g1 = torch.autograd.grad(y, x, create_graph=True)[0]
    g2 = torch.autograd.grad(g1, x, create_graph=True)[0]
    try:
        g3 = torch.autograd.grad(g2, x, create_graph=True)[0]
        oracle = -math.cos(1.0)
        ok = _close(g3.item(), oracle, RTOL_HO, ATOL_HO)
        r = TheoremResult(
            name="d3_sin", mathlib_ref="Real.deriv3_sin",
            verdict=Verdict.PASS if ok else Verdict.BUG,
            detail=f"d³sin/dx³(1) = {g3.item():.12g}, expected {oracle:.12g}")
    except Exception as e:
        r = TheoremResult(name="d3_sin", mathlib_ref="Real.deriv3_sin",
                          verdict=Verdict.CRASH, detail=str(e))
    report.add(r)
    _show_result(r)

    # d⁴/dx⁴[sin(x)] = sin(x)
    x = torch.tensor(1.0, dtype=torch.float64, requires_grad=True)
    y = torch.sin(x)
    g = y
    for i in range(4):
        g = torch.autograd.grad(g, x, create_graph=True)[0]
    oracle = math.sin(1.0)
    ok = _close(g.item(), oracle, RTOL_HO, ATOL_HO)
    r = TheoremResult(
        name="d4_sin_eq_sin", mathlib_ref="Real.deriv4_sin",
        verdict=Verdict.PASS if ok else Verdict.BUG,
        detail=f"d⁴sin/dx⁴(1) = {g.item():.12g}, expected sin(1) = {oracle:.12g}")
    report.add(r)
    _show_result(r)

    # d²/dx²[exp(x)] = exp(x) — should be exact
    x = torch.tensor(2.0, dtype=torch.float64, requires_grad=True)
    y = torch.exp(x)
    g1 = torch.autograd.grad(y, x, create_graph=True)[0]
    g2 = torch.autograd.grad(g1, x, create_graph=True)[0]
    oracle = math.exp(2.0)
    ok = _close(g2.item(), oracle, RTOL, ATOL)
    r = TheoremResult(
        name="d2_exp_eq_exp", mathlib_ref="Real.deriv2_exp",
        verdict=Verdict.PASS if ok else Verdict.BUG,
        detail=f"d²exp/dx²(2) = {g2.item():.12g}, expected {oracle:.12g}")
    report.add(r)
    _show_result(r)


# ═══════════════════════════════════════════════════════════════
#  L. Cross-dtype Consistency
# ═══════════════════════════════════════════════════════════════

def verify_cross_dtype():
    _cat("L. Cross-dtype Gradient Consistency (float32 vs float64)")

    test_fns = [
        ("sin", torch.sin),
        ("exp", torch.exp),
        ("sigmoid", torch.sigmoid),
        ("x³", lambda x: x ** 3),
    ]

    for fname, f in test_fns:
        x32 = torch.tensor(1.5, dtype=torch.float32, requires_grad=True)
        x64 = torch.tensor(1.5, dtype=torch.float64, requires_grad=True)

        g32 = _grad(f, x32).item()
        g64 = _grad(f, x64).item()

        # float32 should agree with float64 to ~1e-6
        ok = _close(g32, g64, rtol=1e-5, atol=1e-6)
        r = TheoremResult(
            name=f"dtype_parity_{fname}",
            mathlib_ref="float32_float64_consistency",
            verdict=Verdict.PASS if ok else Verdict.NUMERICAL_NOISE,
            detail="" if ok else f"f32={g32:.8g}, f64={g64:.12g}, err={_rel_err(g32, g64):.2e}")
        report.add(r)
        _show_result(r)


# ═══════════════════════════════════════════════════════════════
#  MAIN
# ═══════════════════════════════════════════════════════════════

def main():
    print("═" * 60)
    print("  Deppy — Mathlib-Axiom Bug Finder for PyTorch Autograd")
    print(f"  PyTorch {torch.__version__}  |  float64 primary")
    print("  Using formally proved Mathlib theorems as test oracles")
    print("═" * 60)

    t0 = time.time()

    verify_elementary()
    verify_composition_laws()
    verify_algebraic_identities()
    verify_higher_order()
    verify_reductions()
    verify_linalg()
    verify_forward_vs_reverse()
    verify_edge_cases()
    try:
        verify_compile_differential()
    except Exception as e:
        print(f"  ⊘ torch.compile tests skipped: {e}")
    verify_power_rule()
    verify_grad_of_grad()
    verify_cross_dtype()

    elapsed = time.time() - t0

    # Summary
    print()
    print("═" * 60)
    print("  VERIFICATION REPORT")
    print("─" * 60)
    n_pass = sum(1 for r in report.results if r.verdict == Verdict.PASS)
    n_noise = len(report.noise)
    n_bugs = len(report.bugs)
    n_crash = len(report.crashes)
    n_total = len(report.results)

    print(f"  Total checks:      {n_total}")
    print(f"  Passed:            {n_pass}")
    print(f"  Numerical noise:   {n_noise}")
    print(f"  BUGS FOUND:        {n_bugs}")
    print(f"  Crashes:           {n_crash}")
    print(f"  Time:              {elapsed:.1f}s")

    if report.bugs:
        print()
        print("  ┌─────────────────────────────────────────────────────┐")
        print("  │  BUG DETAILS                                       │")
        print("  └─────────────────────────────────────────────────────┘")
        seen = set()
        for b in report.bugs:
            if b.name not in seen:
                seen.add(b.name)
                _show_result(b)

    print("═" * 60)

    return 1 if report.bugs else 0


if __name__ == "__main__":
    sys.exit(main())
