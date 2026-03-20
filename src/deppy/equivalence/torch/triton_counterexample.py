"""
Triton kernel counterexample synthesis via algebraic axiom theory.

Sheaf-theoretic formulation
───────────────────────
The floating-point input space  F  has a natural **stratification**
induced by IEEE 754:

    F  =  F_regular  ⊔  F_subnormal  ⊔  F_zero  ⊔  F_inf  ⊔  F_nan

Two kernels that agree on the open dense stratum F_regular may
**disagree on boundary strata** — the presheaf isomorphism η : Sem_f ⇒ Sem_g
fails to extend from the interior to the compactification.

Architecture
────────────
The synthesizer is built on three algebraic layers:

1. **Expression algebra** (§3): An immutable AST for kernel computations
   — Var, Num, BinOp, Neg, FnCall, Cond — with MetaVar-based unification.

2. **Axiom catalog** (§4): Each axiom of real-number algebra is declared
   as a (LHS pattern, RHS pattern) pair.  The IEEE 754 failure spec for
   each axiom maps it to the strata and category where it breaks.

3. **Comparison engine** (§5): A depth-bounded, memoised rewrite search
   that identifies which axioms are needed to equate two expressions.
   Counterexamples are derived mechanically from axiom failure specs.

A **counterexample** is a section  σ ∈ Γ(U, Sem_f)  on a boundary fiber
U ⊂ F_boundary  witnessing  η|_U  is NOT an isomorphism.
"""

from __future__ import annotations

import ast
import enum
import math
import re
import textwrap
from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple, Union


# ═══════════════════════════════════════════════════════════════════════════════
# §1  Input space stratification & data types
# ═══════════════════════════════════════════════════════════════════════════════


class InputStratum(enum.Enum):
    """Strata of the floating-point input space.

    The IEEE 754 number line has a natural stratification:
        F_regular  ⊃  F_subnormal  ⊃  F_zero  ⊃  F_inf  ⊃  F_nan

    with closure relations (e.g. Inf is in the closure of the regulars).
    Algebraic identities that hold on F_regular may fail on boundary strata.
    """
    REGULAR = "regular"
    SUBNORMAL = "subnormal"
    ZERO = "zero"
    INFINITY = "infinity"
    NAN = "nan"
    LARGE_MAGNITUDE = "large_magnitude"
    PRECISION_BOUNDARY = "precision_boundary"
    TILING_BOUNDARY = "tiling_boundary"
    NEGATIVE = "negative"


class EdgeCaseCategory(enum.Enum):
    """Categories of edge-case counterexamples."""
    FP_IDENTITY = "fp_identity"
    FP_ASSOCIATIVITY = "fp_associativity"
    FP_DISTRIBUTIVITY = "fp_distributivity"
    DIVISION_HAZARD = "division_hazard"
    CANCELLATION = "cancellation"
    OVERFLOW = "overflow"
    MASK_BOUNDARY = "mask_boundary"
    NAN_PROPAGATION = "nan_propagation"
    SIGN_LOSS = "sign_loss"
    CONDITIONAL_EDGE = "conditional_edge"
    REDUCTION_ORDER = "reduction_order"


@dataclass(frozen=True)
class EdgeCaseCounterexample:
    """A witness to non-equivalence on a boundary stratum."""
    category: EdgeCaseCategory
    input_stratum: InputStratum
    description: str
    trigger_values: Dict[str, str] = field(default_factory=dict)
    kernel_a_output: str = ""
    kernel_b_output: str = ""
    confidence: float = 1.0

    def __str__(self) -> str:
        vals = ", ".join(f"{k}={v}" for k, v in self.trigger_values.items())
        return (
            f"[{self.category.value}] {self.description}\n"
            f"  Stratum: {self.input_stratum.value}\n"
            f"  Trigger: {vals}\n"
            f"  Kernel A \u2192 {self.kernel_a_output}\n"
            f"  Kernel B \u2192 {self.kernel_b_output}"
        )


@dataclass
class CounterexampleReport:
    """Full report from counterexample synthesis on a kernel pair."""
    counterexamples: List[EdgeCaseCounterexample] = field(default_factory=list)
    kernel_a_expr: str = ""
    kernel_b_expr: str = ""
    structurally_identical: bool = False
    n_stores_a: int = 0
    n_stores_b: int = 0

    @property
    def found_counterexample(self) -> bool:
        return len(self.counterexamples) > 0

    @property
    def strata_affected(self) -> FrozenSet[InputStratum]:
        return frozenset(c.input_stratum for c in self.counterexamples)

    @property
    def categories(self) -> FrozenSet[EdgeCaseCategory]:
        return frozenset(c.category for c in self.counterexamples)


# ═══════════════════════════════════════════════════════════════════════════════
# §2  Expression algebra — immutable AST for kernel computations
# ═══════════════════════════════════════════════════════════════════════════════

Expr = Union["Var", "Num", "BinOp", "Neg", "FnCall", "Cond"]


@dataclass(frozen=True)
class Var:
    """Leaf: a loaded tensor variable or unresolved parameter."""
    name: str


@dataclass(frozen=True)
class Num:
    """Leaf: a floating-point constant."""
    value: float

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Num):
            return NotImplemented
        if math.isnan(self.value) and math.isnan(other.value):
            return True
        return self.value == other.value

    def __hash__(self) -> int:
        return hash(("Num", self.value if not math.isnan(self.value) else "nan"))


@dataclass(frozen=True)
class BinOp:
    """Binary arithmetic: +, -, *, /, **, and comparisons."""
    op: str
    left: Expr
    right: Expr


@dataclass(frozen=True)
class Neg:
    """Unary negation."""
    arg: Expr


@dataclass(frozen=True)
class FnCall:
    """Function call: tl.exp, tl.abs, tl.sum, etc."""
    func: str
    args: tuple
    kwargs: tuple = ()


@dataclass(frozen=True)
class Cond:
    """Conditional: tl.where(test, if_true, if_false)."""
    test: Expr
    if_true: Expr
    if_false: Expr


@dataclass(frozen=True)
class MetaVar:
    """Pattern variable that binds to any sub-expression during unification."""
    name: str


Pattern = Union[Var, Num, BinOp, Neg, FnCall, Cond, MetaVar]


def unify(
    pattern: Pattern, expr: Expr, bindings: Optional[Dict[str, Expr]] = None,
) -> Optional[Dict[str, Expr]]:
    """Structural unification of *pattern* against *expr*.

    MetaVar nodes in *pattern* bind to sub-expressions.  A MetaVar that
    appears more than once must bind to structurally equal sub-trees.
    """
    if bindings is None:
        bindings = {}
    if isinstance(pattern, MetaVar):
        if pattern.name in bindings:
            return bindings if bindings[pattern.name] == expr else None
        b = dict(bindings)
        b[pattern.name] = expr
        return b
    if type(pattern) is not type(expr):
        return None
    if isinstance(pattern, Var):
        return bindings if pattern.name == expr.name else None  # type: ignore[union-attr]
    if isinstance(pattern, Num):
        return bindings if pattern == expr else None
    if isinstance(pattern, BinOp):
        assert isinstance(expr, BinOp)
        if pattern.op != expr.op:
            return None
        b = unify(pattern.left, expr.left, bindings)
        return unify(pattern.right, expr.right, b) if b is not None else None
    if isinstance(pattern, Neg):
        assert isinstance(expr, Neg)
        return unify(pattern.arg, expr.arg, bindings)
    if isinstance(pattern, FnCall):
        assert isinstance(expr, FnCall)
        if pattern.func != expr.func or len(pattern.args) != len(expr.args):
            return None
        b = bindings
        for pa, ea in zip(pattern.args, expr.args):
            b = unify(pa, ea, b)
            if b is None:
                return None
        return b
    if isinstance(pattern, Cond):
        assert isinstance(expr, Cond)
        b = unify(pattern.test, expr.test, bindings)
        if b is None:
            return None
        b = unify(pattern.if_true, expr.if_true, b)
        return unify(pattern.if_false, expr.if_false, b) if b is not None else None
    return None


def instantiate(pattern: Pattern, bindings: Dict[str, Expr]) -> Expr:
    """Substitute MetaVars in *pattern* with their bound expressions."""
    if isinstance(pattern, MetaVar):
        return bindings[pattern.name]
    if isinstance(pattern, (Var, Num)):
        return pattern  # type: ignore[return-value]
    if isinstance(pattern, BinOp):
        return BinOp(pattern.op, instantiate(pattern.left, bindings),
                     instantiate(pattern.right, bindings))
    if isinstance(pattern, Neg):
        return Neg(instantiate(pattern.arg, bindings))
    if isinstance(pattern, FnCall):
        return FnCall(pattern.func,
                      tuple(instantiate(a, bindings) for a in pattern.args),
                      pattern.kwargs)
    if isinstance(pattern, Cond):
        return Cond(instantiate(pattern.test, bindings),
                    instantiate(pattern.if_true, bindings),
                    instantiate(pattern.if_false, bindings))
    return pattern  # type: ignore[return-value]


def _expr_to_str(e: Expr) -> str:
    """Human-readable string for an expression tree."""
    if isinstance(e, Var):
        return e.name
    if isinstance(e, Num):
        return repr(e.value)
    if isinstance(e, BinOp):
        return f"({_expr_to_str(e.left)} {e.op} {_expr_to_str(e.right)})"
    if isinstance(e, Neg):
        return f"(-{_expr_to_str(e.arg)})"
    if isinstance(e, FnCall):
        a = ", ".join(_expr_to_str(x) for x in e.args)
        return f"{e.func}({a})"
    if isinstance(e, Cond):
        return f"where({_expr_to_str(e.test)}, {_expr_to_str(e.if_true)}, {_expr_to_str(e.if_false)})"
    return "?"


# ═══════════════════════════════════════════════════════════════════════════════
# §3  Axioms of R-algebra and their IEEE 754 failure specifications
# ═══════════════════════════════════════════════════════════════════════════════


class RealAxiom(enum.Enum):
    """Each value names an axiom of the real-number field that *fails*
    on at least one IEEE 754 boundary stratum."""
    SUB_SELF = "x - x = 0"
    DIV_SELF = "x / x = 1"
    MUL_ZERO = "x * 0 = 0"
    ADD_ZERO = "x + 0 = x"
    ADD_ASSOC = "(a+b)+c = a+(b+c)"
    MUL_ASSOC = "(a*b)*c = a*(b*c)"
    DISTRIBUTE = "a*(b+c) = a*b+a*c"
    MUL_DIV_CANCEL = "(x*y)/y = x"
    ADD_SUB_CANCEL = "(x+y)-y = x"
    SUB_ADD_CANCEL = "(x-y)+y = x"
    DIV_MUL_CANCEL = "(x/y)*y = x"
    SQ_SELF_DIV = "(x*x)/x = x"
    DIV_MUL_RECIP = "a/b = a*(1/b)"
    RECIP_INVOL = "1/(1/x) = x"
    DIV_CHAIN = "(a/b)/c = a/(b*c)"
    COMPLEX_FRACTION = "a/(b/c) = (a*c)/b"
    FRACTION_ADD = "1/a+1/b = (a+b)/(a*b)"
    POW_EXPAND = "x^n = x*...*x"
    SQ_DIFF = "a^2-b^2 = (a+b)(a-b)"
    SQ_EXPAND = "(a+b)^2 = a^2+2ab+b^2"
    LINEARITY = "a+a+a = 3*a"
    EXP_ADD = "exp(a)*exp(b) = exp(a+b)"
    MAX_ALG = "max(a,b) = (a+b+|a-b|)/2"
    ABS_MAX_MIN = "max-min = |a-b|"
    PROD_EXP_LOG = "prod = exp.sum.log"
    WHERE_AS_MUL = "where(c,x,0) = x*c"
    MAX_AS_WHERE = "max(x,0) = where(x>0,x,0)"
    CLAMP_ORDER = "clamp order"
    SUM_ABS = "sum|x| >= |sum x|"
    SOFTPLUS_GUARD = "log(1+exp(x)) approx x"
    SIGN_DIV = "x/|x| = sign(x)"
    SAFE_DIV = "a/(b+eps) approx guarded"
    MEAN_EXPAND = "sum(x)/N = sum(x/N)"


@dataclass(frozen=True)
class AxiomRule:
    """Declarative rewrite: lhs -> rhs modulo an axiom."""
    axiom: RealAxiom
    lhs: Pattern
    rhs: Pattern


@dataclass(frozen=True)
class AxiomFailureSpec:
    """How an axiom fails under IEEE 754."""
    strata: Tuple[InputStratum, ...]
    category: EdgeCaseCategory
    description: str
    trigger: Dict[str, str]
    output_a: str
    output_b: str


# shorthand MetaVars
_A, _B, _C = MetaVar("A"), MetaVar("B"), MetaVar("C")
_X, _Y, _Z = MetaVar("X"), MetaVar("Y"), MetaVar("Z")

AXIOM_RULES: List[AxiomRule] = [
    # identity / cancellation
    AxiomRule(RealAxiom.SUB_SELF, BinOp("-", _X, _X), Num(0.0)),
    AxiomRule(RealAxiom.DIV_SELF, BinOp("/", _X, _X), Num(1.0)),
    AxiomRule(RealAxiom.MUL_ZERO, BinOp("*", _X, Num(0.0)), Num(0.0)),
    AxiomRule(RealAxiom.ADD_ZERO, BinOp("+", _X, Num(0.0)), _X),
    # structure
    AxiomRule(RealAxiom.ADD_ASSOC,
             BinOp("+", BinOp("+", _A, _B), _C),
             BinOp("+", _A, BinOp("+", _B, _C))),
    AxiomRule(RealAxiom.MUL_ASSOC,
             BinOp("*", BinOp("*", _A, _B), _C),
             BinOp("*", _A, BinOp("*", _B, _C))),
    AxiomRule(RealAxiom.DISTRIBUTE,
             BinOp("*", _A, BinOp("+", _B, _C)),
             BinOp("+", BinOp("*", _A, _B), BinOp("*", _A, _C))),
    AxiomRule(RealAxiom.DISTRIBUTE,
             BinOp("*", BinOp("+", _A, _B), _C),
             BinOp("+", BinOp("*", _A, _C), BinOp("*", _B, _C))),
    # cancellation through two ops
    AxiomRule(RealAxiom.MUL_DIV_CANCEL,
             BinOp("/", BinOp("*", _X, _Y), _Y), _X),
    AxiomRule(RealAxiom.ADD_SUB_CANCEL,
             BinOp("-", BinOp("+", _X, _Y), _Y), _X),
    AxiomRule(RealAxiom.SUB_ADD_CANCEL,
             BinOp("+", BinOp("-", _X, _Y), _Y), _X),
    AxiomRule(RealAxiom.DIV_MUL_CANCEL,
             BinOp("*", BinOp("/", _X, _Y), _Y), _X),
    AxiomRule(RealAxiom.SQ_SELF_DIV,
             BinOp("/", BinOp("*", _X, _X), _X), _X),
    # division algebra
    AxiomRule(RealAxiom.DIV_MUL_RECIP,
             BinOp("/", _A, _B),
             BinOp("*", _A, BinOp("/", Num(1.0), _B))),
    AxiomRule(RealAxiom.RECIP_INVOL,
             BinOp("/", Num(1.0), BinOp("/", Num(1.0), _X)), _X),
    AxiomRule(RealAxiom.DIV_CHAIN,
             BinOp("/", BinOp("/", _A, _B), _C),
             BinOp("/", _A, BinOp("*", _B, _C))),
    AxiomRule(RealAxiom.COMPLEX_FRACTION,
             BinOp("/", _A, BinOp("/", _B, _C)),
             BinOp("/", BinOp("*", _A, _C), _B)),
    AxiomRule(RealAxiom.FRACTION_ADD,
             BinOp("+", BinOp("/", Num(1.0), _A), BinOp("/", Num(1.0), _B)),
             BinOp("/", BinOp("+", _A, _B), BinOp("*", _A, _B))),
    # powers
    AxiomRule(RealAxiom.POW_EXPAND,
             BinOp("*", BinOp("*", _X, _X), _X),
             BinOp("**", _X, Num(3.0))),
    AxiomRule(RealAxiom.SQ_DIFF,
             BinOp("-", BinOp("*", _A, _A), BinOp("*", _B, _B)),
             BinOp("*", BinOp("+", _A, _B), BinOp("-", _A, _B))),
    AxiomRule(RealAxiom.SQ_EXPAND,
             BinOp("*", BinOp("+", _X, _Y), BinOp("+", _X, _Y)),
             BinOp("+", BinOp("+", BinOp("*", _X, _X),
                               BinOp("*", Num(2.0), BinOp("*", _X, _Y))),
                    BinOp("*", _Y, _Y))),
    AxiomRule(RealAxiom.LINEARITY,
             BinOp("+", BinOp("+", _X, _X), _X),
             BinOp("*", Num(3.0), _X)),
    # transcendental
    AxiomRule(RealAxiom.EXP_ADD,
             BinOp("*", FnCall("tl.exp", (_A,)), FnCall("tl.exp", (_B,))),
             FnCall("tl.exp", (BinOp("+", _A, _B),))),
    AxiomRule(RealAxiom.MAX_ALG,
             FnCall("tl.maximum", (_X, _Y)),
             BinOp("/", BinOp("+", BinOp("+", _X, _Y),
                               FnCall("tl.abs", (BinOp("-", _X, _Y),))),
                    Num(2.0))),
    # conditional
    AxiomRule(RealAxiom.MAX_AS_WHERE,
             FnCall("tl.maximum", (_X, Num(0.0))),
             Cond(BinOp(">", _X, Num(0.0)), _X, Num(0.0))),
]

AXIOM_FAILURES: Dict[RealAxiom, AxiomFailureSpec] = {
    RealAxiom.SUB_SELF: AxiomFailureSpec(
        (InputStratum.NAN, InputStratum.INFINITY), EdgeCaseCategory.FP_IDENTITY,
        "x - x != 0 for NaN/Inf", {"x": "float('nan')"}, "NaN", "0.0"),
    RealAxiom.DIV_SELF: AxiomFailureSpec(
        (InputStratum.ZERO, InputStratum.NAN), EdgeCaseCategory.DIVISION_HAZARD,
        "x / x != 1 for 0/NaN", {"x": "0.0"}, "NaN", "1.0"),
    RealAxiom.MUL_ZERO: AxiomFailureSpec(
        (InputStratum.INFINITY, InputStratum.NAN), EdgeCaseCategory.FP_IDENTITY,
        "Inf * 0 = NaN", {"x": "float('inf')"}, "NaN", "0.0"),
    RealAxiom.ADD_ZERO: AxiomFailureSpec(
        (InputStratum.ZERO,), EdgeCaseCategory.SIGN_LOSS,
        "-0 + 0 = +0 != -0", {"x": "-0.0"}, "+0.0", "-0.0"),
    RealAxiom.ADD_ASSOC: AxiomFailureSpec(
        (InputStratum.LARGE_MAGNITUDE, InputStratum.PRECISION_BOUNDARY),
        EdgeCaseCategory.FP_ASSOCIATIVITY,
        "FP addition not associative", {"a": "1e16", "b": "1.0", "c": "-1e16"},
        "0.0", "1.0"),
    RealAxiom.MUL_ASSOC: AxiomFailureSpec(
        (InputStratum.LARGE_MAGNITUDE,), EdgeCaseCategory.FP_ASSOCIATIVITY,
        "FP multiplication not associative near overflow",
        {"a": "1e200", "b": "1e200", "c": "1e-200"}, "Inf", "1e200"),
    RealAxiom.DISTRIBUTE: AxiomFailureSpec(
        (InputStratum.LARGE_MAGNITUDE, InputStratum.PRECISION_BOUNDARY),
        EdgeCaseCategory.FP_DISTRIBUTIVITY,
        "a*(b+c) != a*b+a*c", {"a": "1e15", "b": "1.0000001", "c": "-1.0"},
        "differs by ULP(s)", "differs by ULP(s)"),
    RealAxiom.MUL_DIV_CANCEL: AxiomFailureSpec(
        (InputStratum.ZERO, InputStratum.NAN), EdgeCaseCategory.DIVISION_HAZARD,
        "(x*y)/y != x when y=0", {"y": "0.0", "x": "1.0"}, "NaN", "1.0"),
    RealAxiom.ADD_SUB_CANCEL: AxiomFailureSpec(
        (InputStratum.PRECISION_BOUNDARY, InputStratum.LARGE_MAGNITUDE),
        EdgeCaseCategory.CANCELLATION,
        "(x+y)-y != x: catastrophic cancellation",
        {"x": "1e-16", "y": "1e16"}, "0.0", "1e-16"),
    RealAxiom.SUB_ADD_CANCEL: AxiomFailureSpec(
        (InputStratum.PRECISION_BOUNDARY, InputStratum.LARGE_MAGNITUDE),
        EdgeCaseCategory.CANCELLATION,
        "(x-y)+y != x: catastrophic cancellation",
        {"x": "1e-16", "y": "1e16"}, "0.0", "1e-16"),
    RealAxiom.DIV_MUL_CANCEL: AxiomFailureSpec(
        (InputStratum.ZERO, InputStratum.PRECISION_BOUNDARY),
        EdgeCaseCategory.DIVISION_HAZARD,
        "(x/y)*y != x when y=0", {"x": "1.0", "y": "0.0"}, "NaN", "1.0"),
    RealAxiom.SQ_SELF_DIV: AxiomFailureSpec(
        (InputStratum.ZERO,), EdgeCaseCategory.DIVISION_HAZARD,
        "(x*x)/x != x when x=0", {"x": "0.0"}, "NaN", "0.0"),
    RealAxiom.DIV_MUL_RECIP: AxiomFailureSpec(
        (InputStratum.PRECISION_BOUNDARY,), EdgeCaseCategory.DIVISION_HAZARD,
        "a/b != a*(1/b): double rounding", {"a": "1.0", "b": "3.0"},
        "correctly rounded", "double rounded"),
    RealAxiom.RECIP_INVOL: AxiomFailureSpec(
        (InputStratum.SUBNORMAL,), EdgeCaseCategory.OVERFLOW,
        "1/(1/x) != x for subnormal x", {"x": "5e-324"},
        "0.0 (round-trip via Inf)", "5e-324"),
    RealAxiom.DIV_CHAIN: AxiomFailureSpec(
        (InputStratum.PRECISION_BOUNDARY,), EdgeCaseCategory.DIVISION_HAZARD,
        "a/b/c != a/(b*c): intermediate precision",
        {"a": "1.0", "b": "3.0", "c": "7.0"},
        "differs at ULP", "differs at ULP"),
    RealAxiom.COMPLEX_FRACTION: AxiomFailureSpec(
        (InputStratum.LARGE_MAGNITUDE,), EdgeCaseCategory.OVERFLOW,
        "a/(b/c) != (a*c)/b: overflow path differs",
        {"a": "1.0", "b": "1e-300", "c": "1e-300"},
        "Inf (b/c underflow)", "different overflow"),
    RealAxiom.FRACTION_ADD: AxiomFailureSpec(
        (InputStratum.ZERO,), EdgeCaseCategory.DIVISION_HAZARD,
        "1/a+1/b != (a+b)/(a*b) when a=0",
        {"a": "0.0", "b": "1.0"}, "Inf", "NaN"),
    RealAxiom.POW_EXPAND: AxiomFailureSpec(
        (InputStratum.LARGE_MAGNITUDE,), EdgeCaseCategory.OVERFLOW,
        "x*x*x != x**3: intermediate overflow",
        {"x": "1e200"}, "Inf (x*x overflow)", "pow() path"),
    RealAxiom.SQ_DIFF: AxiomFailureSpec(
        (InputStratum.LARGE_MAGNITUDE,), EdgeCaseCategory.CANCELLATION,
        "a^2-b^2 != (a+b)(a-b): catastrophic cancellation",
        {"a": "1e8+1", "b": "1e8"}, "different rounding", "different rounding"),
    RealAxiom.SQ_EXPAND: AxiomFailureSpec(
        (InputStratum.LARGE_MAGNITUDE, InputStratum.PRECISION_BOUNDARY),
        EdgeCaseCategory.FP_DISTRIBUTIVITY,
        "(a+b)^2 != a^2+2ab+b^2: expansion rounding",
        {"a": "1e15", "b": "1.0"}, "differs", "differs"),
    RealAxiom.LINEARITY: AxiomFailureSpec(
        (InputStratum.PRECISION_BOUNDARY,), EdgeCaseCategory.FP_ASSOCIATIVITY,
        "a+a+a != 3*a: intermediate rounding",
        {"a": "large odd near 2^53"}, "rounded differently", "rounded differently"),
    RealAxiom.EXP_ADD: AxiomFailureSpec(
        (InputStratum.LARGE_MAGNITUDE,), EdgeCaseCategory.OVERFLOW,
        "exp(a)*exp(b) overflows individually",
        {"a": "500.0", "b": "-499.0"}, "Inf", "exp(1) approx 2.718"),
    RealAxiom.MAX_ALG: AxiomFailureSpec(
        (InputStratum.NAN,), EdgeCaseCategory.NAN_PROPAGATION,
        "max(a,b) via arithmetic propagates NaN differently",
        {"x": "float('nan')"}, "NaN", "NaN (arithmetic)"),
    RealAxiom.MAX_AS_WHERE: AxiomFailureSpec(
        (InputStratum.NAN,), EdgeCaseCategory.NAN_PROPAGATION,
        "tl.maximum propagates NaN; tl.where may not",
        {"x": "float('nan')"}, "NaN", "0.0"),
    RealAxiom.ABS_MAX_MIN: AxiomFailureSpec(
        (InputStratum.NAN,), EdgeCaseCategory.NAN_PROPAGATION,
        "max-min != |a-b| for NaN", {"a": "float('nan')"}, "NaN", "NaN"),
    RealAxiom.WHERE_AS_MUL: AxiomFailureSpec(
        (InputStratum.INFINITY,), EdgeCaseCategory.CONDITIONAL_EDGE,
        "where(c,x,0)!=x*c: Inf*0=NaN",
        {"x": "float('inf')", "c": "False"}, "0.0", "NaN"),
    RealAxiom.CLAMP_ORDER: AxiomFailureSpec(
        (InputStratum.NAN,), EdgeCaseCategory.NAN_PROPAGATION,
        "Clamp order differs for NaN",
        {"x": "float('nan')"}, "NaN path A", "NaN path B"),
    RealAxiom.SUM_ABS: AxiomFailureSpec(
        (InputStratum.NEGATIVE,), EdgeCaseCategory.FP_IDENTITY,
        "sum|x| > |sum x| for mixed signs",
        {"x": "[1,-1,1,-1]"}, "4.0", "0.0"),
    RealAxiom.SOFTPLUS_GUARD: AxiomFailureSpec(
        (InputStratum.LARGE_MAGNITUDE,), EdgeCaseCategory.OVERFLOW,
        "log(1+exp(x)) overflows for large x",
        {"x": "1000.0"}, "Inf", "1000.0"),
    RealAxiom.SIGN_DIV: AxiomFailureSpec(
        (InputStratum.ZERO,), EdgeCaseCategory.DIVISION_HAZARD,
        "x/|x| != sign(x) when x=0", {"x": "0.0"}, "NaN", "0.0"),
    RealAxiom.SAFE_DIV: AxiomFailureSpec(
        (InputStratum.NEGATIVE,), EdgeCaseCategory.DIVISION_HAZARD,
        "a/(b+eps)!=safe when b=-eps", {"b": "-eps"}, "NaN/Inf", "0.0"),
    RealAxiom.MEAN_EXPAND: AxiomFailureSpec(
        (InputStratum.PRECISION_BOUNDARY,), EdgeCaseCategory.REDUCTION_ORDER,
        "sum(x)/N != sum(x/N): precision",
        {"x_i": "large spread"}, "sum-then-div", "div-then-sum"),
    RealAxiom.PROD_EXP_LOG: AxiomFailureSpec(
        (InputStratum.NEGATIVE,), EdgeCaseCategory.OVERFLOW,
        "prod(x)!=exp(sum(log(x))) for x<0",
        {"x": "[-1,2,3]"}, "-6.0", "NaN"),
}


# ═══════════════════════════════════════════════════════════════════════════════
# §4  Expression extraction from Triton kernel AST
# ═══════════════════════════════════════════════════════════════════════════════


def _binop_str(op: ast.operator) -> str:
    _MAP = {
        ast.Add: "+", ast.Sub: "-", ast.Mult: "*", ast.Div: "/",
        ast.FloorDiv: "//", ast.Mod: "%", ast.Pow: "**",
        ast.BitAnd: "&", ast.BitOr: "|", ast.BitXor: "^",
        ast.LShift: "<<", ast.RShift: ">>",
    }
    return _MAP.get(type(op), "?")


def _cmpop_str(op: ast.cmpop) -> str:
    _MAP = {
        ast.Eq: "==", ast.NotEq: "!=", ast.Lt: "<", ast.LtE: "<=",
        ast.Gt: ">", ast.GtE: ">=",
    }
    return _MAP.get(type(op), "??")


class _ExprExtractor(ast.NodeVisitor):
    """Extracts computation expressions from a Triton kernel as Expr trees."""

    def __init__(self) -> None:
        self.env: Dict[str, ast.expr] = {}
        self.loads: Dict[str, ast.Call] = {}
        self.stores: List[Tuple[str, ast.expr]] = []
        self.store_masks: List[Optional[str]] = []
        self.load_others: Dict[str, Optional[str]] = {}
        self.load_masks: Dict[str, Optional[str]] = {}
        self.reductions: Dict[str, ast.Call] = {}

    def extract(self, source: str) -> None:
        tree = ast.parse(textwrap.dedent(source))
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                self._walk_body(node.body)
                break

    def _walk_body(self, body: List[ast.stmt]) -> None:
        for stmt in body:
            if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1:
                tgt = stmt.targets[0]
                if isinstance(tgt, ast.Name):
                    name = tgt.id
                    self.env[name] = stmt.value
                    if self._is_tl_call(stmt.value, "load"):
                        self.loads[name] = stmt.value
                        self._extract_load_info(name, stmt.value)
                    elif self._is_tl_reduction(stmt.value):
                        self.reductions[name] = stmt.value
            elif isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
                if self._is_tl_call(stmt.value, "store"):
                    self._extract_store(stmt.value)
            elif isinstance(stmt, ast.AugAssign) and isinstance(stmt.target, ast.Name):
                name = stmt.target.id
                self.env[name] = ast.BinOp(
                    left=ast.Name(id=name, ctx=ast.Load()),
                    op=stmt.op, right=stmt.value)
            elif isinstance(stmt, ast.If):
                self._walk_body(stmt.body)
                if stmt.orelse:
                    self._walk_body(stmt.orelse)
            elif isinstance(stmt, ast.For):
                self._walk_body(stmt.body)

    @staticmethod
    def _call_name(node: ast.Call) -> str:
        if isinstance(node.func, ast.Attribute):
            if isinstance(node.func.value, ast.Name):
                return f"{node.func.value.id}.{node.func.attr}"
            return node.func.attr
        if isinstance(node.func, ast.Name):
            return node.func.id
        return ""

    def _is_tl_call(self, node: ast.expr, method: str) -> bool:
        return isinstance(node, ast.Call) and self._call_name(node) in (f"tl.{method}", method)

    def _is_tl_reduction(self, node: ast.expr) -> bool:
        return isinstance(node, ast.Call) and self._call_name(node) in (
            "tl.sum", "tl.max", "tl.min", "tl.reduce", "sum", "max", "min")

    def _extract_load_info(self, var: str, call: ast.Call) -> None:
        mask = other = None
        for kw in call.keywords:
            if kw.arg == "mask":
                mask = self._quick_str(kw.value)
            elif kw.arg == "other":
                other = self._quick_str(kw.value)
        if mask is None and len(call.args) > 1:
            mask = self._quick_str(call.args[1])
        if other is None and len(call.args) > 2:
            other = self._quick_str(call.args[2])
        self.load_masks[var] = mask
        self.load_others[var] = other

    def _extract_store(self, call: ast.Call) -> None:
        if len(call.args) < 2:
            return
        self.stores.append((self._quick_str(call.args[0]), call.args[1]))
        mask = None
        for kw in call.keywords:
            if kw.arg == "mask":
                mask = self._quick_str(kw.value)
        if mask is None and len(call.args) > 2:
            mask = self._quick_str(call.args[2])
        self.store_masks.append(mask)

    @staticmethod
    def _quick_str(node: ast.expr) -> str:
        if isinstance(node, ast.Constant):
            return repr(node.value)
        if isinstance(node, ast.Name):
            return node.id
        return ast.dump(node)

    def resolve_expr(self, node: ast.expr, depth: int = 0) -> Expr:
        """Resolve an AST node into an Expr tree through the environment."""
        if depth > 50:
            return Var("deep")
        if isinstance(node, ast.Name):
            name = node.id
            if name in self.loads:
                return Var(name)
            if name in self.reductions:
                return self._resolve_reduction_expr(name, depth)
            if name in self.env:
                return self.resolve_expr(self.env[name], depth + 1)
            return Var(name)
        if isinstance(node, ast.Constant):
            v = node.value
            if isinstance(v, (int, float)):
                return Num(float(v))
            return Var(repr(v))
        if isinstance(node, ast.BinOp):
            return BinOp(_binop_str(node.op),
                         self.resolve_expr(node.left, depth + 1),
                         self.resolve_expr(node.right, depth + 1))
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return Neg(self.resolve_expr(node.operand, depth + 1))
        if isinstance(node, ast.Call):
            cname = self._call_name(node)
            args = tuple(self.resolve_expr(a, depth + 1) for a in node.args)
            if cname in ("tl.where", "where") and len(args) >= 3:
                return Cond(args[0], args[1], args[2])
            kw = tuple((k.arg, self.resolve_expr(k.value, depth + 1))
                       for k in node.keywords if k.arg is not None)
            return FnCall(cname, args, kw)
        if isinstance(node, ast.Compare) and len(node.ops) == 1:
            return BinOp(_cmpop_str(node.ops[0]),
                         self.resolve_expr(node.left, depth + 1),
                         self.resolve_expr(node.comparators[0], depth + 1))
        if isinstance(node, ast.IfExp):
            return Cond(self.resolve_expr(node.test, depth + 1),
                        self.resolve_expr(node.body, depth + 1),
                        self.resolve_expr(node.orelse, depth + 1))
        if isinstance(node, ast.Attribute):
            val = self.resolve_expr(node.value, depth + 1)
            return Var(f"{_expr_to_str(val)}.{node.attr}")
        return Var(ast.dump(node))

    def _resolve_reduction_expr(self, name: str, depth: int) -> Expr:
        call = self.reductions[name]
        cname = self._call_name(call)
        args = tuple(self.resolve_expr(a, depth + 1) for a in call.args)
        kw = tuple((k.arg, self.resolve_expr(k.value, depth + 1))
                   for k in call.keywords if k.arg is not None)
        return FnCall(cname, args, kw)

    def resolved_store_exprs(self) -> List[Expr]:
        return [self.resolve_expr(val) for _, val in self.stores]

    def resolved_stores_str(self) -> List[str]:
        return [_expr_to_str(e) for e in self.resolved_store_exprs()]


# ═══════════════════════════════════════════════════════════════════════════════
# §5  Algebraic comparison engine
# ═══════════════════════════════════════════════════════════════════════════════


_COMPARE_BUDGET_KEY = "__budget__"
_MAX_COMPARE_CALLS = 5000


def _compare(
    a: Expr, b: Expr, depth: int = 12,
    _cache: Optional[Dict] = None,
) -> Optional[FrozenSet[RealAxiom]]:
    """Check whether a and b are R-equivalent modulo axioms.

    Returns the set of axioms needed, or None if not unifiable.
    Uses a call budget to bound exponential search.
    """
    if _cache is None:
        _cache = {_COMPARE_BUDGET_KEY: _MAX_COMPARE_CALLS}
    # Check budget
    budget = _cache.get(_COMPARE_BUDGET_KEY, 0)
    if budget <= 0:
        return None
    _cache[_COMPARE_BUDGET_KEY] = budget - 1

    key = (a, b)
    if key in _cache:
        return _cache[key]
    if a == b:
        _cache[key] = frozenset()
        return frozenset()
    if depth <= 0:
        _cache[key] = None
        return None
    _cache[key] = None  # prevent infinite recursion

    try:
        return _compare_inner(a, b, depth, _cache, key)
    except RecursionError:
        _cache[key] = None
        return None


def _compare_inner(
    a: Expr, b: Expr, depth: int, _cache: Dict, key: tuple,
) -> Optional[FrozenSet[RealAxiom]]:
    # Phase 1: Direct (non-recursive) rule match — one rewrite step away
    for rule in AXIOM_RULES:
        result = _try_rule_direct(rule, a, b)
        if result is not None:
            _cache[key] = result
            return result

    # Phase 2: SOP normalization (fast, handles polynomial identities)
    result = _try_sop(a, b)
    if result is not None:
        _cache[key] = result
        return result

    # Phase 3: Commutativity — decrement depth to bound recursion
    result = _try_commutative(a, b, depth - 1, _cache)
    if result is not None:
        _cache[key] = result
        return result

    # Phase 4: Same top-level op (recursive into sub-expressions)
    result = _try_same_op(a, b, depth, _cache)
    if result is not None:
        _cache[key] = result
        return result

    # Phase 5: Full recursive rule match
    for rule in AXIOM_RULES:
        result = _try_rule(rule, a, b, depth, _cache)
        if result is not None:
            _cache[key] = result
            return result

    _cache[key] = None
    return None


def _try_commutative(a: Expr, b: Expr, depth: int, _cache: Dict) -> Optional[FrozenSet[RealAxiom]]:
    if isinstance(a, BinOp) and a.op in ("+", "*"):
        swapped = BinOp(a.op, a.right, a.left)
        r = _compare(swapped, b, depth, _cache)
        if r is not None:
            return r
    if isinstance(b, BinOp) and b.op in ("+", "*"):
        swapped = BinOp(b.op, b.right, b.left)
        r = _compare(a, swapped, depth, _cache)
        if r is not None:
            return r
    return None


def _try_same_op(a: Expr, b: Expr, depth: int, _cache: Dict) -> Optional[FrozenSet[RealAxiom]]:
    if isinstance(a, BinOp) and isinstance(b, BinOp) and a.op == b.op:
        rl = _compare(a.left, b.left, depth - 1, _cache)
        if rl is not None:
            rr = _compare(a.right, b.right, depth - 1, _cache)
            if rr is not None:
                return rl | rr
    if isinstance(a, Neg) and isinstance(b, Neg):
        return _compare(a.arg, b.arg, depth - 1, _cache)
    if isinstance(a, FnCall) and isinstance(b, FnCall):
        if a.func == b.func and len(a.args) == len(b.args):
            axioms: FrozenSet[RealAxiom] = frozenset()
            for xa, xb in zip(a.args, b.args):
                r = _compare(xa, xb, depth - 1, _cache)
                if r is None:
                    return None
                axioms = axioms | r
            return axioms
    if isinstance(a, Cond) and isinstance(b, Cond):
        rt = _compare(a.test, b.test, depth - 1, _cache)
        if rt is not None:
            ry = _compare(a.if_true, b.if_true, depth - 1, _cache)
            if ry is not None:
                rn = _compare(a.if_false, b.if_false, depth - 1, _cache)
                if rn is not None:
                    return rt | ry | rn
    return None


def _has_division(e: Expr) -> bool:
    """Check if an expression contains a division operator."""
    if isinstance(e, BinOp):
        if e.op == "/":
            return True
        return _has_division(e.left) or _has_division(e.right)
    if isinstance(e, Neg):
        return _has_division(e.arg)
    if isinstance(e, FnCall):
        return any(_has_division(a) for a in e.args)
    if isinstance(e, Cond):
        return _has_division(e.test) or _has_division(e.if_true) or _has_division(e.if_false)
    return False


def _collect_metavars(p: Pattern) -> Set[str]:
    """Collect all MetaVar names in a pattern."""
    if isinstance(p, MetaVar):
        return {p.name}
    if isinstance(p, (Var, Num)):
        return set()
    if isinstance(p, BinOp):
        return _collect_metavars(p.left) | _collect_metavars(p.right)
    if isinstance(p, Neg):
        return _collect_metavars(p.arg)
    if isinstance(p, FnCall):
        s: Set[str] = set()
        for a in p.args:
            s |= _collect_metavars(a)
        return s
    if isinstance(p, Cond):
        return _collect_metavars(p.test) | _collect_metavars(p.if_true) | _collect_metavars(p.if_false)
    return set()


def _try_rule_direct(rule: AxiomRule, a: Expr, b: Expr) -> Optional[FrozenSet[RealAxiom]]:
    """Non-recursive rule match: one rewrite step directly yields the target."""
    lhs_vars = _collect_metavars(rule.lhs)
    rhs_vars = _collect_metavars(rule.rhs)

    for src, tgt in [(a, b), (b, a)]:
        bindings = unify(rule.lhs, src)
        if bindings is not None and rhs_vars <= set(bindings):
            rhs = instantiate(rule.rhs, bindings)
            if rhs == tgt:
                return frozenset({rule.axiom})
        bindings = unify(rule.rhs, src)
        if bindings is not None and lhs_vars <= set(bindings):
            lhs = instantiate(rule.lhs, bindings)
            if lhs == tgt:
                return frozenset({rule.axiom})
    return None


def _try_rule(rule: AxiomRule, a: Expr, b: Expr, depth: int, _cache: Dict) -> Optional[FrozenSet[RealAxiom]]:
    # DIV_MUL_RECIP is very general (matches any a/b) — only try it
    # when both sides involve division to avoid runaway rewriting.
    if rule.axiom == RealAxiom.DIV_MUL_RECIP:
        if not (_has_division(a) and _has_division(b)):
            return None

    lhs_vars = _collect_metavars(rule.lhs)
    rhs_vars = _collect_metavars(rule.rhs)

    # If RHS has strictly fewer MetaVars than LHS, the reverse direction
    # (matching RHS against any expression, then expanding to LHS) always
    # succeeds and creates unhelpful new expressions → skip reverse.
    allow_reverse = not (rhs_vars < lhs_vars)

    for src, tgt in [(a, b), (b, a)]:
        # Forward: match LHS, instantiate RHS
        bindings = unify(rule.lhs, src)
        if bindings is not None and rhs_vars <= set(bindings):
            rhs = instantiate(rule.rhs, bindings)
            sub = _compare(rhs, tgt, depth - 1, _cache)
            if sub is not None:
                return frozenset({rule.axiom}) | sub
        # Reverse: match RHS, instantiate LHS (only if safe)
        if allow_reverse:
            bindings = unify(rule.rhs, src)
            if bindings is not None and lhs_vars <= set(bindings):
                lhs = instantiate(rule.lhs, bindings)
                sub = _compare(lhs, tgt, depth - 1, _cache)
                if sub is not None:
                    return frozenset({rule.axiom}) | sub
    return None


# sum-of-products normalization

@dataclass(frozen=True, order=True)
class _Factor:
    key: str
    power: int = 1


@dataclass(frozen=True)
class _Mono:
    coeff: float
    factors: Tuple[_Factor, ...]


def _canonical_key(e: Expr) -> str:
    if isinstance(e, Var):
        return e.name
    if isinstance(e, Num):
        return repr(e.value)
    if isinstance(e, BinOp) and e.op in ("+", "*"):
        parts = sorted([_canonical_key(e.left), _canonical_key(e.right)])
        return f"({parts[0]}{e.op}{parts[1]})"
    if isinstance(e, BinOp):
        return f"({_canonical_key(e.left)}{e.op}{_canonical_key(e.right)})"
    if isinstance(e, Neg):
        return f"(-{_canonical_key(e.arg)})"
    if isinstance(e, FnCall):
        a = ",".join(_canonical_key(x) for x in e.args)
        return f"{e.func}({a})"
    if isinstance(e, Cond):
        return f"where({_canonical_key(e.test)},{_canonical_key(e.if_true)},{_canonical_key(e.if_false)})"
    return "?"


def _mul_mono(a: _Mono, b: _Mono) -> _Mono:
    fmap: Dict[str, int] = {}
    for f in a.factors:
        fmap[f.key] = fmap.get(f.key, 0) + f.power
    for f in b.factors:
        fmap[f.key] = fmap.get(f.key, 0) + f.power
    factors = tuple(sorted(_Factor(k, p) for k, p in fmap.items() if p != 0))
    return _Mono(a.coeff * b.coeff, factors)


def _expand_to_sop(e: Expr, axioms: Set[RealAxiom]) -> List[_Mono]:
    if isinstance(e, Num):
        return [_Mono(e.value, ())]
    if isinstance(e, Var):
        return [_Mono(1.0, (_Factor(e.name),))]
    if isinstance(e, Neg):
        return [_Mono(-m.coeff, m.factors) for m in _expand_to_sop(e.arg, axioms)]
    if isinstance(e, BinOp):
        if e.op == "+":
            axioms.add(RealAxiom.ADD_ASSOC)
            return _expand_to_sop(e.left, axioms) + _expand_to_sop(e.right, axioms)
        if e.op == "-":
            axioms.add(RealAxiom.ADD_ASSOC)
            lm = _expand_to_sop(e.left, axioms)
            rm = _expand_to_sop(e.right, axioms)
            return lm + [_Mono(-m.coeff, m.factors) for m in rm]
        if e.op == "*":
            axioms.add(RealAxiom.DISTRIBUTE)
            axioms.add(RealAxiom.MUL_ASSOC)
            lm = _expand_to_sop(e.left, axioms)
            rm = _expand_to_sop(e.right, axioms)
            return [_mul_mono(a, b) for a in lm for b in rm]
        if e.op == "/":
            axioms.add(RealAxiom.DIV_MUL_RECIP)
            lm = _expand_to_sop(e.left, axioms)
            rm = _expand_to_sop(e.right, axioms)
            if len(rm) == 1 and rm[0].coeff != 0.0:
                inv = _Mono(1.0 / rm[0].coeff,
                            tuple(_Factor(f.key, -f.power) for f in rm[0].factors))
                return [_mul_mono(l, inv) for l in lm]
            rkey = _canonical_key(e.right)
            inv_f = _Factor(rkey, -1)
            return [_Mono(m.coeff, m.factors + (inv_f,)) for m in lm]
        if e.op == "**":
            if isinstance(e.right, Num) and e.right.value == int(e.right.value) and 1 < e.right.value <= 4:
                axioms.add(RealAxiom.POW_EXPAND)
                n = int(e.right.value)
                bm = _expand_to_sop(e.left, axioms)
                result = [_Mono(1.0, ())]
                for _ in range(n):
                    result = [_mul_mono(a, b) for a in result for b in bm]
                return result
    key = _canonical_key(e)
    return [_Mono(1.0, (_Factor(key),))]


def _combine_sop(monos: List[_Mono]) -> List[_Mono]:
    by_factors: Dict[Tuple[_Factor, ...], float] = {}
    for m in monos:
        fs = tuple(sorted(m.factors))
        by_factors[fs] = by_factors.get(fs, 0.0) + m.coeff
    return sorted(
        (_Mono(c, fs) for fs, c in by_factors.items() if abs(c) > 1e-15),
        key=lambda m: (m.factors, m.coeff),
    )


def _try_sop(a: Expr, b: Expr) -> Optional[FrozenSet[RealAxiom]]:
    try:
        ax_a: Set[RealAxiom] = set()
        ax_b: Set[RealAxiom] = set()
        sop_a = _combine_sop(_expand_to_sop(a, ax_a))
        sop_b = _combine_sop(_expand_to_sop(b, ax_b))
        if sop_a == sop_b:
            all_ax = ax_a | ax_b
            all_ax.discard(RealAxiom.ADD_ASSOC)
            if not all_ax:
                all_ax = {RealAxiom.DISTRIBUTE}
            return frozenset(all_ax)
    except Exception:
        pass
    return None


def _derive_counterexamples(axioms: FrozenSet[RealAxiom]) -> List[EdgeCaseCounterexample]:
    cexs: List[EdgeCaseCounterexample] = []
    for ax in axioms:
        spec = AXIOM_FAILURES.get(ax)
        if spec is None:
            continue
        for stratum in spec.strata:
            cexs.append(EdgeCaseCounterexample(
                category=spec.category,
                input_stratum=stratum,
                description=f"[{ax.value}] {spec.description}",
                trigger_values=dict(spec.trigger),
                kernel_a_output=spec.output_a,
                kernel_b_output=spec.output_b,
            ))
    return cexs


# ═══════════════════════════════════════════════════════════════════════════════
# §6  Load / mask parameter analysis
# ═══════════════════════════════════════════════════════════════════════════════


def _check_load_other_diff(ext_a: _ExprExtractor, ext_b: _ExprExtractor) -> List[EdgeCaseCounterexample]:
    results: List[EdgeCaseCounterexample] = []
    for i, (la, lb) in enumerate(zip(ext_a.loads, ext_b.loads)):
        oa, ob = ext_a.load_others.get(la), ext_b.load_others.get(lb)
        if oa != ob:
            results.append(EdgeCaseCounterexample(
                EdgeCaseCategory.MASK_BOUNDARY, InputStratum.TILING_BOUNDARY,
                f"Load {i}: different other= ({oa!r} vs {ob!r})",
                {"N": "not multiple of BLOCK_SIZE"},
                f"boundary = {oa}", f"boundary = {ob}"))
    return results


def _check_mask_presence_diff(ext_a: _ExprExtractor, ext_b: _ExprExtractor) -> List[EdgeCaseCounterexample]:
    results: List[EdgeCaseCounterexample] = []
    for i, (la, lb) in enumerate(zip(ext_a.loads, ext_b.loads)):
        ma, mb = ext_a.load_masks.get(la), ext_b.load_masks.get(lb)
        if bool(ma) != bool(mb):
            who = "A" if ma else "B"
            results.append(EdgeCaseCounterexample(
                EdgeCaseCategory.MASK_BOUNDARY, InputStratum.TILING_BOUNDARY,
                f"Load {i}: kernel {who} masked, other not",
                {"N": "N % BLOCK_SIZE != 0"},
                "masked: safe" if ma else "unmasked: OOB",
                "masked: safe" if mb else "unmasked: OOB"))
    for i in range(min(len(ext_a.store_masks), len(ext_b.store_masks))):
        ma, mb = ext_a.store_masks[i], ext_b.store_masks[i]
        if bool(ma) != bool(mb):
            who = "A" if ma else "B"
            results.append(EdgeCaseCounterexample(
                EdgeCaseCategory.MASK_BOUNDARY, InputStratum.TILING_BOUNDARY,
                f"Store {i}: kernel {who} masked, other not",
                {"N": "N % BLOCK_SIZE != 0"},
                "masked: safe" if ma else "unmasked: OOB",
                "masked: safe" if mb else "unmasked: OOB"))
    return results


# ═══════════════════════════════════════════════════════════════════════════════
# §7  Source-level pattern analysis
# ═══════════════════════════════════════════════════════════════════════════════


def _check_source_patterns(src_a: str, src_b: str) -> List[EdgeCaseCounterexample]:
    results: List[EdgeCaseCounterexample] = []
    sa, sb = textwrap.dedent(src_a), textwrap.dedent(src_b)

    # tl.where vs tl.maximum/minimum
    if ('tl.maximum' in sa or 'tl.minimum' in sa) and 'tl.where' in sb:
        results.append(EdgeCaseCounterexample(
            EdgeCaseCategory.NAN_PROPAGATION, InputStratum.NAN,
            "tl.maximum/minimum propagates NaN; tl.where may not",
            {"x": "float('nan')"}, "NaN", "condition-dependent"))
    elif ('tl.maximum' in sb or 'tl.minimum' in sb) and 'tl.where' in sa:
        results.append(EdgeCaseCounterexample(
            EdgeCaseCategory.NAN_PROPAGATION, InputStratum.NAN,
            "tl.maximum/minimum propagates NaN; tl.where may not",
            {"x": "float('nan')"}, "condition-dependent", "NaN"))

    # clamp order
    if (re.search(r'tl\.minimum\(tl\.maximum\(', sa) and re.search(r'tl\.maximum\(tl\.minimum\(', sb)) or \
       (re.search(r'tl\.maximum\(tl\.minimum\(', sa) and re.search(r'tl\.minimum\(tl\.maximum\(', sb)):
        results.append(EdgeCaseCounterexample(
            EdgeCaseCategory.NAN_PROPAGATION, InputStratum.NAN,
            "min(max(x,lo),hi) != max(min(x,hi),lo) for NaN",
            {"x": "float('nan')"}, "NaN path A", "NaN path B"))

    # softplus guard
    exp_log_a = 'tl.exp(' in sa and 'tl.log(' in sa
    exp_log_b = 'tl.exp(' in sb and 'tl.log(' in sb
    guard_a = 'tl.where' in sa and exp_log_a
    guard_b = 'tl.where' in sb and exp_log_b
    if exp_log_a and guard_b and not guard_a:
        results.append(EdgeCaseCounterexample(
            EdgeCaseCategory.OVERFLOW, InputStratum.LARGE_MAGNITUDE,
            "Unguarded exp(x) overflows; guarded version safe",
            {"x": "1000.0"}, "Inf", "1000.0"))
    elif exp_log_b and guard_a and not guard_b:
        results.append(EdgeCaseCounterexample(
            EdgeCaseCategory.OVERFLOW, InputStratum.LARGE_MAGNITUDE,
            "Unguarded exp(x) overflows; guarded version safe",
            {"x": "1000.0"}, "1000.0", "Inf"))

    # exp product
    ep_a = re.search(r'tl\.exp\(.+?\)\s*\*\s*tl\.exp\(', sa)
    ep_b = re.search(r'tl\.exp\(.+?\)\s*\*\s*tl\.exp\(', sb)
    if ep_a and not ep_b and 'tl.exp(' in sb:
        results.append(EdgeCaseCounterexample(
            EdgeCaseCategory.OVERFLOW, InputStratum.LARGE_MAGNITUDE,
            "exp(a)*exp(b) overflows individually",
            {"a": "500.0", "b": "-499.0"}, "Inf", "exp(1)"))
    elif ep_b and not ep_a and 'tl.exp(' in sa:
        results.append(EdgeCaseCounterexample(
            EdgeCaseCategory.OVERFLOW, InputStratum.LARGE_MAGNITUDE,
            "exp(a)*exp(b) overflows individually",
            {"a": "500.0", "b": "-499.0"}, "exp(1)", "Inf"))

    # where vs multiply mask
    if 'tl.where' in sa and '*' in sb and 'tl.where' not in sb:
        results.append(EdgeCaseCounterexample(
            EdgeCaseCategory.CONDITIONAL_EDGE, InputStratum.INFINITY,
            "where(c,x,0)!=x*c: Inf*0=NaN",
            {"x": "float('inf')", "c": "False"}, "0.0", "NaN"))
    elif 'tl.where' in sb and '*' in sa and 'tl.where' not in sa:
        results.append(EdgeCaseCounterexample(
            EdgeCaseCategory.CONDITIONAL_EDGE, InputStratum.INFINITY,
            "where(c,x,0)!=x*c: Inf*0=NaN",
            {"x": "float('inf')", "c": "False"}, "NaN", "0.0"))

    # abs vs manual abs
    abs_a = 'tl.abs(' in sa or 'tl.math.fabs(' in sa
    abs_b = 'tl.abs(' in sb or 'tl.math.fabs(' in sb
    manual_a = re.search(r'tl\.where\(.+?>=?\s*0', sa) and '-' in sa
    manual_b = re.search(r'tl\.where\(.+?>=?\s*0', sb) and '-' in sb
    if abs_a and manual_b and not abs_b:
        results.append(EdgeCaseCounterexample(
            EdgeCaseCategory.SIGN_LOSS, InputStratum.ZERO,
            "tl.abs(-0)->+0; manual abs may differ",
            {"x": "-0.0"}, "+0.0", "depends on condition"))
    elif abs_b and manual_a and not abs_a:
        results.append(EdgeCaseCounterexample(
            EdgeCaseCategory.SIGN_LOSS, InputStratum.ZERO,
            "tl.abs(-0)->+0; manual abs may differ",
            {"x": "-0.0"}, "depends on condition", "+0.0"))

    # sign function
    div_abs = re.search(r'/\s*tl\.(abs|math\.fabs)\(', sa) or re.search(r'/\s*tl\.(abs|math\.fabs)\(', sb)
    if div_abs and ('tl.where' in sa or 'tl.where' in sb):
        results.append(EdgeCaseCounterexample(
            EdgeCaseCategory.DIVISION_HAZARD, InputStratum.ZERO,
            "x/|x|!=sign(x) when x=0", {"x": "0.0"}, "NaN", "0.0"))

    # safe division
    eps_div = re.search(r'/\s*\(.+?\+.+?\)', sa) or re.search(r'/\s*\(.+?\+.+?\)', sb)
    if eps_div and ('tl.where' in sa or 'tl.where' in sb):
        results.append(EdgeCaseCounterexample(
            EdgeCaseCategory.DIVISION_HAZARD, InputStratum.NEGATIVE,
            "a/(b+eps)!=safe when b=-eps", {"b": "-eps"}, "NaN/Inf", "0.0"))

    # sum|x| vs |sum x|
    sum_abs = re.search(r'tl\.sum\(tl\.abs\(', sa) or re.search(r'tl\.sum\(tl\.abs\(', sb)
    abs_sum = re.search(r'tl\.abs\(tl\.sum\(', sa) or re.search(r'tl\.abs\(tl\.sum\(', sb)
    if sum_abs and abs_sum:
        results.append(EdgeCaseCounterexample(
            EdgeCaseCategory.FP_IDENTITY, InputStratum.NEGATIVE,
            "sum|x|!=|sum x| for mixed signs",
            {"x": "[1,-1,1,-1]"}, "4.0", "0.0"))

    # prod vs exp(sum(log))
    has_reduce = 'tl.reduce(' in sa or 'tl.reduce(' in sb
    has_esl = re.search(r'tl\.exp\(tl\.sum\(tl\.log\(', sa) or re.search(r'tl\.exp\(tl\.sum\(tl\.log\(', sb)
    if has_reduce and has_esl:
        results.append(EdgeCaseCounterexample(
            EdgeCaseCategory.OVERFLOW, InputStratum.NEGATIVE,
            "prod(x)!=exp(sum(log(x))) for x<0",
            {"x": "[-1,2,3]"}, "-6.0", "NaN"))

    # max-min vs |a-b|
    has_mm = ('tl.maximum' in sa and 'tl.minimum' in sa and '-' in sa) or \
             ('tl.maximum' in sb and 'tl.minimum' in sb and '-' in sb)
    has_ad = ('tl.abs(' in sa and '-' in sa) or ('tl.abs(' in sb and '-' in sb)
    if has_mm and has_ad:
        results.append(EdgeCaseCounterexample(
            EdgeCaseCategory.NAN_PROPAGATION, InputStratum.NAN,
            "max(a,b)-min(a,b)!=|a-b| for NaN",
            {"a": "float('nan')"}, "NaN", "NaN"))

    # sum/divide order — detect sum-then-divide vs divide-then-sum in either order
    sum_then_div_a = re.search(r'tl\.sum\(.*\).*/', sa)
    sum_then_div_b = re.search(r'tl\.sum\(.*\).*/', sb)
    div_in_sum_a = re.search(r'tl\.sum\(.*[*/]', sa)
    div_in_sum_b = re.search(r'tl\.sum\(.*[*/]', sb)
    if (sum_then_div_a and div_in_sum_b) or (sum_then_div_b and div_in_sum_a):
        results.append(EdgeCaseCounterexample(
            EdgeCaseCategory.REDUCTION_ORDER, InputStratum.PRECISION_BOUNDARY,
            "sum(x)/N != sum(x/N)", {"x_i": "large spread"},
            "sum-then-divide", "divide-then-sum"))

    return results


# ═══════════════════════════════════════════════════════════════════════════════
# §8  Main synthesizer
# ═══════════════════════════════════════════════════════════════════════════════


class CounterexampleSynthesizer:
    """Synthesises edge-case counterexamples for Triton kernel pairs.

    Architecture: Extract Expr trees -> axiom-modulo comparison ->
    derive counterexamples from IEEE 754 failure catalog.
    """

    def synthesize(self, source_a: str, source_b: str) -> CounterexampleReport:
        ext_a, ext_b = _ExprExtractor(), _ExprExtractor()
        ext_a.extract(source_a)
        ext_b.extract(source_b)

        exprs_a = ext_a.resolved_store_exprs()
        exprs_b = ext_b.resolved_store_exprs()
        strs_a = [_expr_to_str(e) for e in exprs_a]
        strs_b = [_expr_to_str(e) for e in exprs_b]

        report = CounterexampleReport(
            kernel_a_expr="; ".join(strs_a),
            kernel_b_expr="; ".join(strs_b),
            n_stores_a=len(exprs_a),
            n_stores_b=len(exprs_b),
            structurally_identical=(exprs_a == exprs_b),
        )

        if exprs_a == exprs_b:
            report.counterexamples.extend(_check_load_other_diff(ext_a, ext_b))
            report.counterexamples.extend(_check_mask_presence_diff(ext_a, ext_b))
            return report

        all_cex: List[EdgeCaseCounterexample] = []

        # algebraic comparison
        for ea, eb in zip(exprs_a, exprs_b):
            axioms = _compare(ea, eb)
            if axioms is not None and len(axioms) > 0:
                all_cex.extend(_derive_counterexamples(axioms))

        # infrastructure checks
        all_cex.extend(_check_load_other_diff(ext_a, ext_b))
        all_cex.extend(_check_mask_presence_diff(ext_a, ext_b))

        # source-level fallback
        all_cex.extend(_check_source_patterns(source_a, source_b))

        # deduplicate
        seen: Dict[Tuple[EdgeCaseCategory, InputStratum], EdgeCaseCounterexample] = {}
        for cex in all_cex:
            k = (cex.category, cex.input_stratum)
            if k not in seen or cex.confidence > seen[k].confidence:
                seen[k] = cex
        report.counterexamples = list(seen.values())
        return report
