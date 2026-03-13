"""
Triton kernel edge-case counterexample synthesis — boundary stratum analysis.

Sheaf-theoretic formulation
───────────────────────────
The floating-point input space  F  has a natural **stratification**
induced by IEEE 754:

    F  =  F_regular  ⊔  F_subnormal  ⊔  F_zero  ⊔  F_inf  ⊔  F_nan

Two kernels that agree on the open dense stratum F_regular may
**disagree on boundary strata** — the presheaf isomorphism η : Sem_f ⇒ Sem_g
fails to extend from the interior to the compactification.

A **counterexample** is a section  σ ∈ Γ(U, Sem_f)  on a boundary fiber
U ⊂ F_boundary  witnessing  η|_U  is NOT an isomorphism.  This is a
*cohomological obstruction*: the first Čech cohomology class
H¹(F_boundary, Iso(Sem_f, Sem_g))  is non-trivial.

The synthesizer works by:
1. Extracting the **store expression** from each kernel (the section functor)
2. Comparing expressions via AST structural analysis
3. Classifying differences against known FP-hazard patterns
4. Generating specific input values on boundary strata that witness
   the non-isomorphism

For Triton kernels, there is an additional **tiling boundary** stratum:
when N is not a multiple of BLOCK_SIZE, the last tile has a partial
mask.  Two kernels with different ``other=`` defaults in masked loads
disagree on this tiling boundary.
"""

from __future__ import annotations

import ast
import enum
import math
import re
import textwrap
from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple


# ═══════════════════════════════════════════════════════════════════════════════
# Input space stratification
# ═══════════════════════════════════════════════════════════════════════════════


class InputStratum(enum.Enum):
    """Strata of the floating-point input space.

    The IEEE 754 number line has a natural stratification:
        F_regular  ⊃  F_subnormal  ⊃  F_zero  ⊃  F_inf  ⊃  F_nan

    with closure relations (e.g. Inf is in the closure of the regulars).
    Algebraic identities that hold on F_regular may fail on boundary strata.
    """

    REGULAR = "regular"
    """Normal floating-point numbers — the open dense stratum."""

    SUBNORMAL = "subnormal"
    """Denormalized numbers — boundary near zero."""

    ZERO = "zero"
    """±0 — distinguished boundary point (negative zero ≠ positive zero)."""

    INFINITY = "infinity"
    """±Inf — boundary at infinity (compactification)."""

    NAN = "nan"
    """NaN — singular stratum (absorbing element)."""

    LARGE_MAGNITUDE = "large_magnitude"
    """Values near ±MAX_FLOAT — overflow boundary."""

    PRECISION_BOUNDARY = "precision_boundary"
    """Values where FP rounding causes information loss (e.g. 1e16 + 1)."""

    TILING_BOUNDARY = "tiling_boundary"
    """Tile boundary: N not a multiple of BLOCK_SIZE."""

    NEGATIVE = "negative"
    """Negative values — sign boundary."""


class EdgeCaseCategory(enum.Enum):
    """Categories of edge-case counterexamples."""

    FP_IDENTITY = "fp_identity"
    """Algebraic identity that fails for special FP values."""

    FP_ASSOCIATIVITY = "fp_associativity"
    """Non-associativity of FP addition/multiplication."""

    FP_DISTRIBUTIVITY = "fp_distributivity"
    """Failure of distributive law in FP arithmetic."""

    DIVISION_HAZARD = "division_hazard"
    """Division by zero or near-zero causing divergence."""

    CANCELLATION = "cancellation"
    """Catastrophic cancellation in subtraction."""

    OVERFLOW = "overflow"
    """Intermediate overflow producing Inf/NaN."""

    MASK_BOUNDARY = "mask_boundary"
    """Tiling boundary with different mask defaults."""

    NAN_PROPAGATION = "nan_propagation"
    """NaN propagation differs between equivalent expressions."""

    SIGN_LOSS = "sign_loss"
    """Sign information lost (e.g. -0 → +0)."""

    CONDITIONAL_EDGE = "conditional_edge"
    """Conditional expression with NaN/Inf in comparison."""

    REDUCTION_ORDER = "reduction_order"
    """Reduction order sensitivity for FP sums."""


# ═══════════════════════════════════════════════════════════════════════════════
# Counterexample data types
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class EdgeCaseCounterexample:
    """A witness to non-equivalence on a boundary stratum.

    Sheaf-theoretically, this is a section on a closed substratum
    of the input fiber where the presheaf restriction map diverges:
    the natural transformation η fails on this fiber.
    """

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
            f"  Kernel A → {self.kernel_a_output}\n"
            f"  Kernel B → {self.kernel_b_output}"
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
# Expression extraction from Triton kernel AST
# ═══════════════════════════════════════════════════════════════════════════════


# Sentinel for load variables in resolved expressions
_LOAD_PREFIX = "«LOAD:"
_LOAD_SUFFIX = "»"


class _ExprExtractor(ast.NodeVisitor):
    """Extracts computation expressions from a Triton kernel.

    Walks the function body, building a variable→expression environment.
    For each ``tl.store``, resolves the stored value through the
    environment back to load variables, producing a canonical
    expression string.
    """

    def __init__(self) -> None:
        self.env: Dict[str, ast.expr] = {}
        self.loads: Dict[str, ast.Call] = {}
        self.stores: List[Tuple[str, ast.expr]] = []  # (ptr_expr, value_expr)
        self.store_masks: List[Optional[str]] = []
        self.load_others: Dict[str, Optional[str]] = {}
        self.load_masks: Dict[str, Optional[str]] = {}
        self.reductions: Dict[str, ast.Call] = {}
        self._call_args_cache: Dict[str, List[str]] = {}

    def extract(self, source: str) -> None:
        """Extract expressions from kernel source."""
        tree = ast.parse(textwrap.dedent(source))
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                self._walk_body(node.body)
                break

    def _walk_body(self, body: List[ast.stmt]) -> None:
        for stmt in body:
            if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1:
                target = stmt.targets[0]
                if isinstance(target, ast.Name):
                    name = target.id
                    self.env[name] = stmt.value
                    if self._is_tl_call(stmt.value, "load"):
                        self.loads[name] = stmt.value
                        self._extract_load_info(name, stmt.value)
                    elif self._is_tl_reduction(stmt.value):
                        self.reductions[name] = stmt.value
            elif isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
                if self._is_tl_call(stmt.value, "store"):
                    self._extract_store(stmt.value)
            elif isinstance(stmt, ast.AugAssign):
                if isinstance(stmt.target, ast.Name):
                    name = stmt.target.id
                    synth = ast.BinOp(
                        left=ast.Name(id=name, ctx=ast.Load()),
                        op=stmt.op,
                        right=stmt.value,
                    )
                    self.env[name] = synth
            elif isinstance(stmt, ast.If):
                self._walk_body(stmt.body)
                if stmt.orelse:
                    self._walk_body(stmt.orelse)
            elif isinstance(stmt, ast.For):
                self._walk_body(stmt.body)

    # ── helper: identify tl.X calls ──────────────────────────────────────

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
        if not isinstance(node, ast.Call):
            return False
        name = self._call_name(node)
        return name in (f"tl.{method}", method)

    def _is_tl_reduction(self, node: ast.expr) -> bool:
        if not isinstance(node, ast.Call):
            return False
        name = self._call_name(node)
        return name in (
            "tl.sum", "tl.max", "tl.min", "tl.reduce",
            "sum", "max", "min",
        )

    # ── load info extraction ─────────────────────────────────────────────

    def _extract_load_info(self, var: str, call: ast.Call) -> None:
        mask = None
        other = None
        for kw in call.keywords:
            if kw.arg == "mask":
                mask = self._expr_str(kw.value)
            elif kw.arg == "other":
                other = self._expr_str(kw.value)
        # Positional: tl.load(ptr, mask, other)
        if mask is None and len(call.args) > 1:
            mask = self._expr_str(call.args[1])
        if other is None and len(call.args) > 2:
            other = self._expr_str(call.args[2])
        self.load_masks[var] = mask
        self.load_others[var] = other

    # ── store extraction ─────────────────────────────────────────────────

    def _extract_store(self, call: ast.Call) -> None:
        if len(call.args) < 2:
            return
        ptr_str = self._expr_str(call.args[0])
        value = call.args[1]
        self.stores.append((ptr_str, value))
        # Mask
        mask = None
        for kw in call.keywords:
            if kw.arg == "mask":
                mask = self._expr_str(kw.value)
        if mask is None and len(call.args) > 2:
            mask = self._expr_str(call.args[2])
        self.store_masks.append(mask)

    # ── expression resolution ────────────────────────────────────────────

    def resolve(self, node: ast.expr, depth: int = 0) -> str:
        """Resolve an AST expression to a canonical string form.

        Load variables are wrapped as  «LOAD:varname»  so that
        pattern matchers can identify them.
        """
        if depth > 50:
            return "⟨deep⟩"

        if isinstance(node, ast.Name):
            name = node.id
            if name in self.loads:
                return f"{_LOAD_PREFIX}{name}{_LOAD_SUFFIX}"
            if name in self.reductions:
                return self._resolve_reduction(name, depth)
            if name in self.env:
                return self.resolve(self.env[name], depth + 1)
            return name

        if isinstance(node, ast.Constant):
            v = node.value
            if isinstance(v, float):
                if math.isnan(v):
                    return "nan"
                if math.isinf(v):
                    return "inf" if v > 0 else "-inf"
                if v == 0.0:
                    return "-0.0" if math.copysign(1.0, v) < 0 else "0.0"
            return repr(v)

        if isinstance(node, ast.BinOp):
            left = self.resolve(node.left, depth + 1)
            right = self.resolve(node.right, depth + 1)
            op = _binop_str(node.op)
            return f"({left} {op} {right})"

        if isinstance(node, ast.UnaryOp):
            operand = self.resolve(node.operand, depth + 1)
            op = _unaryop_str(node.op)
            return f"({op}{operand})"

        if isinstance(node, ast.Call):
            cname = self._call_name(node)
            args = [self.resolve(a, depth + 1) for a in node.args]
            # keyword args
            kw_parts = []
            for kw in node.keywords:
                kv = self.resolve(kw.value, depth + 1)
                kw_parts.append(f"{kw.arg}={kv}")
            all_args = args + kw_parts
            return f"{cname}({', '.join(all_args)})"

        if isinstance(node, ast.Compare):
            left = self.resolve(node.left, depth + 1)
            parts = [left]
            for op, comp in zip(node.ops, node.comparators):
                parts.append(_cmpop_str(op))
                parts.append(self.resolve(comp, depth + 1))
            return f"({' '.join(parts)})"

        if isinstance(node, ast.IfExp):
            test = self.resolve(node.test, depth + 1)
            body = self.resolve(node.body, depth + 1)
            orelse = self.resolve(node.orelse, depth + 1)
            return f"({body} if {test} else {orelse})"

        if isinstance(node, ast.Subscript):
            val = self.resolve(node.value, depth + 1)
            if isinstance(node.slice, ast.Constant):
                return f"{val}[{node.slice.value}]"
            return f"{val}[...]"

        if isinstance(node, ast.Attribute):
            val = self.resolve(node.value, depth + 1)
            return f"{val}.{node.attr}"

        return ast.dump(node)

    def _resolve_reduction(self, name: str, depth: int) -> str:
        call = self.reductions[name]
        cname = self._call_name(call)
        args = [self.resolve(a, depth + 1) for a in call.args]
        kw_parts = []
        for kw in call.keywords:
            kv = self.resolve(kw.value, depth + 1)
            kw_parts.append(f"{kw.arg}={kv}")
        all_args = args + kw_parts
        return f"{cname}({', '.join(all_args)})"

    @staticmethod
    def _expr_str(node: ast.expr) -> str:
        """Quick expression → string for mask/other params."""
        if isinstance(node, ast.Constant):
            return repr(node.value)
        if isinstance(node, ast.Name):
            return node.id
        return ast.dump(node)

    # ── public: resolved store expressions ───────────────────────────────

    def resolved_stores(self) -> List[str]:
        """Return resolved expression strings for each store."""
        return [self.resolve(val) for _, val in self.stores]


def _binop_str(op: ast.operator) -> str:
    _MAP = {
        ast.Add: "+", ast.Sub: "-", ast.Mult: "*", ast.Div: "/",
        ast.FloorDiv: "//", ast.Mod: "%", ast.Pow: "**",
        ast.BitAnd: "&", ast.BitOr: "|", ast.BitXor: "^",
        ast.LShift: "<<", ast.RShift: ">>",
    }
    return _MAP.get(type(op), "?")


def _unaryop_str(op: ast.unaryop) -> str:
    _MAP = {ast.USub: "-", ast.UAdd: "+", ast.Not: "not ", ast.Invert: "~"}
    return _MAP.get(type(op), "?")


def _cmpop_str(op: ast.cmpop) -> str:
    _MAP = {
        ast.Eq: "==", ast.NotEq: "!=", ast.Lt: "<", ast.LtE: "<=",
        ast.Gt: ">", ast.GtE: ">=", ast.Is: "is", ast.IsNot: "is not",
        ast.In: "in", ast.NotIn: "not in",
    }
    return _MAP.get(type(op), "??")


# ═══════════════════════════════════════════════════════════════════════════════
# Pattern-based edge-case classifiers
# ═══════════════════════════════════════════════════════════════════════════════


def _is_load(s: str) -> bool:
    return s.startswith(_LOAD_PREFIX) and s.endswith(_LOAD_SUFFIX)


def _load_name(s: str) -> str:
    if _is_load(s):
        return s[len(_LOAD_PREFIX):-len(_LOAD_SUFFIX)]
    return s


def _is_const(s: str, val: Optional[float] = None) -> bool:
    s = s.strip()
    try:
        v = float(s)
        if val is not None:
            return v == val
        return True
    except (ValueError, OverflowError):
        return False


def _const_val(s: str) -> Optional[float]:
    s = s.strip()
    try:
        return float(s)
    except (ValueError, OverflowError):
        return None


# ── Individual pattern matchers ──────────────────────────────────────────

def _check_self_cancellation(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """x - x  vs  0  (NaN/Inf → NaN vs 0)."""
    # Pattern: (LOAD - LOAD) where both refer to same variable vs const 0
    m = re.match(r'^\((.+) - (.+)\)$', a)
    if m and _is_load(m.group(1)) and m.group(1) == m.group(2) and _is_const(b, 0.0):
        var = _load_name(m.group(1))
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.FP_IDENTITY,
            input_stratum=InputStratum.NAN,
            description=f"{var} - {var} ≠ 0 when {var} is NaN or ±Inf",
            trigger_values={var: "float('nan')"},
            kernel_a_output="NaN",
            kernel_b_output="0.0",
        )
    # Reversed
    m = re.match(r'^\((.+) - (.+)\)$', b)
    if m and _is_load(m.group(1)) and m.group(1) == m.group(2) and _is_const(a, 0.0):
        var = _load_name(m.group(1))
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.FP_IDENTITY,
            input_stratum=InputStratum.NAN,
            description=f"{var} - {var} ≠ 0 when {var} is NaN or ±Inf",
            trigger_values={var: "float('nan')"},
            kernel_a_output="0.0",
            kernel_b_output="NaN",
        )
    return None


def _check_self_division(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """x / x  vs  1  (0 → NaN vs 1)."""
    m = re.match(r'^\((.+) / (.+)\)$', a)
    if m and _is_load(m.group(1)) and m.group(1) == m.group(2) and _is_const(b, 1.0):
        var = _load_name(m.group(1))
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.DIVISION_HAZARD,
            input_stratum=InputStratum.ZERO,
            description=f"{var} / {var} ≠ 1 when {var} = 0 (produces NaN)",
            trigger_values={var: "0.0"},
            kernel_a_output="NaN",
            kernel_b_output="1.0",
        )
    m = re.match(r'^\((.+) / (.+)\)$', b)
    if m and _is_load(m.group(1)) and m.group(1) == m.group(2) and _is_const(a, 1.0):
        var = _load_name(m.group(1))
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.DIVISION_HAZARD,
            input_stratum=InputStratum.ZERO,
            description=f"{var} / {var} ≠ 1 when {var} = 0 (produces NaN)",
            trigger_values={var: "0.0"},
            kernel_a_output="1.0",
            kernel_b_output="NaN",
        )
    return None


def _check_zero_multiply(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """x * 0  vs  0  (Inf → NaN vs 0)."""
    patterns = [
        (r'^\((.+) \* 0\.0\)$', r'0\.0$'),
        (r'^\(0\.0 \* (.+)\)$', r'0\.0$'),
    ]
    for pat, const_pat in patterns:
        m = re.match(pat, a)
        if m and _is_load(m.group(1)) and _is_const(b, 0.0):
            var = _load_name(m.group(1))
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.FP_IDENTITY,
                input_stratum=InputStratum.INFINITY,
                description=f"{var} * 0.0 ≠ 0 when {var} = Inf (produces NaN)",
                trigger_values={var: "float('inf')"},
                kernel_a_output="NaN",
                kernel_b_output="0.0",
            )
    # reversed
    for pat, const_pat in patterns:
        m = re.match(pat, b)
        if m and _is_load(m.group(1)) and _is_const(a, 0.0):
            var = _load_name(m.group(1))
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.FP_IDENTITY,
                input_stratum=InputStratum.INFINITY,
                description=f"{var} * 0.0 ≠ 0 when {var} = Inf (produces NaN)",
                trigger_values={var: "float('inf')"},
                kernel_a_output="0.0",
                kernel_b_output="NaN",
            )
    return None


def _check_zero_addition(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """x + 0.0  vs  x  (−0 + 0 = +0 ≠ −0)."""
    # (LOAD + 0.0) vs LOAD
    m = re.match(r'^\((.+) \+ 0\.0\)$', a)
    if m and _is_load(m.group(1)) and _is_load(b) and _load_name(m.group(1)) == _load_name(b):
        var = _load_name(m.group(1))
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.SIGN_LOSS,
            input_stratum=InputStratum.ZERO,
            description=f"{var} + 0.0 ≠ {var} when {var} = -0.0 (produces +0.0)",
            trigger_values={var: "-0.0"},
            kernel_a_output="+0.0",
            kernel_b_output="-0.0",
        )
    # reversed
    m = re.match(r'^\((.+) \+ 0\.0\)$', b)
    if m and _is_load(m.group(1)) and _is_load(a) and _load_name(m.group(1)) == _load_name(a):
        var = _load_name(m.group(1))
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.SIGN_LOSS,
            input_stratum=InputStratum.ZERO,
            description=f"{var} + 0.0 ≠ {var} when {var} = -0.0 (produces +0.0)",
            trigger_values={var: "-0.0"},
            kernel_a_output="-0.0",
            kernel_b_output="+0.0",
        )
    return None


def _check_multiply_divide_cancel(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """(x * y) / y  vs  x  (y=0 → NaN)."""
    m = re.match(r'^\(\((.+) \* (.+)\) / (.+)\)$', a)
    if m and m.group(2) == m.group(3) and _is_load(m.group(1)) and _is_load(b):
        if _load_name(m.group(1)) == _load_name(b):
            y_var = _load_name(m.group(2))
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.DIVISION_HAZARD,
                input_stratum=InputStratum.ZERO,
                description=f"(x * {y_var}) / {y_var} ≠ x when {y_var} = 0",
                trigger_values={y_var: "0.0", _load_name(m.group(1)): "1.0"},
                kernel_a_output="NaN",
                kernel_b_output="1.0",
            )
    # Reversed
    m = re.match(r'^\(\((.+) \* (.+)\) / (.+)\)$', b)
    if m and m.group(2) == m.group(3) and _is_load(m.group(1)) and _is_load(a):
        if _load_name(m.group(1)) == _load_name(a):
            y_var = _load_name(m.group(2))
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.DIVISION_HAZARD,
                input_stratum=InputStratum.ZERO,
                description=f"(x * {y_var}) / {y_var} ≠ x when {y_var} = 0",
                trigger_values={y_var: "0.0", _load_name(m.group(1)): "1.0"},
                kernel_a_output="1.0",
                kernel_b_output="NaN",
            )
    return None


def _check_add_subtract_cancel(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """(x + y) - y  vs  x  (catastrophic cancellation)."""
    m = re.match(r'^\(\((.+) \+ (.+)\) - (.+)\)$', a)
    if m and m.group(2) == m.group(3) and _is_load(m.group(1)) and _is_load(b):
        if _load_name(m.group(1)) == _load_name(b):
            y_var = _load_name(m.group(2))
            x_var = _load_name(m.group(1))
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.CANCELLATION,
                input_stratum=InputStratum.PRECISION_BOUNDARY,
                description=(
                    f"({x_var} + {y_var}) - {y_var} ≠ {x_var} due to "
                    f"catastrophic cancellation when |{y_var}| >> |{x_var}|"
                ),
                trigger_values={x_var: "1e-16", y_var: "1e16"},
                kernel_a_output="0.0 (precision lost)",
                kernel_b_output="1e-16",
            )
    # Reversed
    m = re.match(r'^\(\((.+) \+ (.+)\) - (.+)\)$', b)
    if m and m.group(2) == m.group(3) and _is_load(m.group(1)) and _is_load(a):
        if _load_name(m.group(1)) == _load_name(a):
            y_var = _load_name(m.group(2))
            x_var = _load_name(m.group(1))
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.CANCELLATION,
                input_stratum=InputStratum.PRECISION_BOUNDARY,
                description=(
                    f"({x_var} + {y_var}) - {y_var} ≠ {x_var} due to "
                    f"catastrophic cancellation when |{y_var}| >> |{x_var}|"
                ),
                trigger_values={x_var: "1e-16", y_var: "1e16"},
                kernel_a_output="1e-16",
                kernel_b_output="0.0 (precision lost)",
            )
    return None


def _check_reciprocal_roundtrip(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """1/(1/x)  vs  x  (denormals, precision loss)."""
    pat = r'^\(1\.0 / \(1\.0 / (.+)\)\)$'
    m = re.match(pat, a)
    if m and _is_load(m.group(1)) and _is_load(b) and _load_name(m.group(1)) == _load_name(b):
        var = _load_name(m.group(1))
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.OVERFLOW,
            input_stratum=InputStratum.SUBNORMAL,
            description=f"1/(1/{var}) ≠ {var} for subnormal {var} (1/{var} overflows to Inf)",
            trigger_values={var: "5e-324"},
            kernel_a_output="0.0 (Inf→0 round-trip)",
            kernel_b_output="5e-324",
        )
    m = re.match(pat, b)
    if m and _is_load(m.group(1)) and _is_load(a) and _load_name(m.group(1)) == _load_name(a):
        var = _load_name(m.group(1))
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.OVERFLOW,
            input_stratum=InputStratum.SUBNORMAL,
            description=f"1/(1/{var}) ≠ {var} for subnormal {var} (1/{var} overflows to Inf)",
            trigger_values={var: "5e-324"},
            kernel_a_output="5e-324",
            kernel_b_output="0.0 (Inf→0 round-trip)",
        )
    return None


def _check_associativity(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """(x + y) + z  vs  x + (y + z)  (FP associativity)."""
    # Pattern: ((A + B) + C) vs (A + (B + C))
    m_left = re.match(r'^\(\((.+?) \+ (.+?)\) \+ (.+)\)$', a)
    m_right = re.match(r'^\((.+?) \+ \((.+?) \+ (.+)\)\)$', b)
    if m_left and m_right:
        la, lb, lc = m_left.group(1), m_left.group(2), m_left.group(3)
        ra, rb, rc = m_right.group(1), m_right.group(2), m_right.group(3)
        if la == ra and lb == rb and lc == rc:
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.FP_ASSOCIATIVITY,
                input_stratum=InputStratum.LARGE_MAGNITUDE,
                description=(
                    "FP addition is not associative: "
                    "(a + b) + c ≠ a + (b + c) for values with large magnitude differences"
                ),
                trigger_values={"a": "1e16", "b": "1.0", "c": "-1e16"},
                kernel_a_output="0.0 ((1e16 + 1) rounds to 1e16, then - 1e16 = 0)",
                kernel_b_output="1.0 (1 + (-1e16 + 1e16) = 1 + 0 = 1)",
            )
    # Reversed
    m_left = re.match(r'^\(\((.+?) \+ (.+?)\) \+ (.+)\)$', b)
    m_right = re.match(r'^\((.+?) \+ \((.+?) \+ (.+)\)\)$', a)
    if m_left and m_right:
        la, lb, lc = m_left.group(1), m_left.group(2), m_left.group(3)
        ra, rb, rc = m_right.group(1), m_right.group(2), m_right.group(3)
        if la == ra and lb == rb and lc == rc:
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.FP_ASSOCIATIVITY,
                input_stratum=InputStratum.LARGE_MAGNITUDE,
                description=(
                    "FP addition is not associative: "
                    "(a + b) + c ≠ a + (b + c) for values with large magnitude differences"
                ),
                trigger_values={"a": "1e16", "b": "1.0", "c": "-1e16"},
                kernel_a_output="1.0",
                kernel_b_output="0.0",
            )
    return None


def _check_mult_associativity(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """(x * y) * z  vs  x * (y * z)  (FP mult associativity near overflow)."""
    m_left = re.match(r'^\(\((.+?) \* (.+?)\) \* (.+)\)$', a)
    m_right = re.match(r'^\((.+?) \* \((.+?) \* (.+)\)\)$', b)
    if m_left and m_right:
        la, lb, lc = m_left.group(1), m_left.group(2), m_left.group(3)
        ra, rb, rc = m_right.group(1), m_right.group(2), m_right.group(3)
        if la == ra and lb == rb and lc == rc:
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.FP_ASSOCIATIVITY,
                input_stratum=InputStratum.LARGE_MAGNITUDE,
                description=(
                    "FP multiplication is not associative near overflow: "
                    "(a*b)*c ≠ a*(b*c) when intermediate products overflow"
                ),
                trigger_values={"a": "1e200", "b": "1e200", "c": "1e-200"},
                kernel_a_output="Inf (1e200*1e200=Inf, Inf*1e-200=Inf)",
                kernel_b_output="1e200 (1e200*1e-200=1, 1e200*1=1e200)",
            )
    # Reversed
    m_left = re.match(r'^\(\((.+?) \* (.+?)\) \* (.+)\)$', b)
    m_right = re.match(r'^\((.+?) \* \((.+?) \* (.+)\)\)$', a)
    if m_left and m_right:
        la, lb, lc = m_left.group(1), m_left.group(2), m_left.group(3)
        ra, rb, rc = m_right.group(1), m_right.group(2), m_right.group(3)
        if la == ra and lb == rb and lc == rc:
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.FP_ASSOCIATIVITY,
                input_stratum=InputStratum.LARGE_MAGNITUDE,
                description="FP multiplication not associative near overflow boundary",
                trigger_values={"a": "1e200", "b": "1e200", "c": "1e-200"},
                kernel_a_output="1e200",
                kernel_b_output="Inf",
            )
    return None


def _check_distributivity(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """a*(b+c)  vs  a*b + a*c  (FP distributivity)."""
    # a * (b + c)
    m_dist = re.match(r'^\((.+?) \* \((.+?) \+ (.+?)\)\)$', a)
    # a*b + a*c
    m_expand = re.match(r'^\(\((.+?) \* (.+?)\) \+ \((.+?) \* (.+?)\)\)$', b)
    if m_dist and m_expand:
        da, db, dc = m_dist.group(1), m_dist.group(2), m_dist.group(3)
        ea1, eb, ea2, ec = (m_expand.group(1), m_expand.group(2),
                            m_expand.group(3), m_expand.group(4))
        if da == ea1 == ea2 and db == eb and dc == ec:
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.FP_DISTRIBUTIVITY,
                input_stratum=InputStratum.LARGE_MAGNITUDE,
                description=(
                    "FP distributivity fails: a*(b+c) ≠ a*b + a*c "
                    "when intermediate products have different magnitudes"
                ),
                trigger_values={"a": "1e15", "b": "1.0000001", "c": "-1.0"},
                kernel_a_output="differs by ULP(s)",
                kernel_b_output="differs by ULP(s)",
            )
    # Reversed
    m_dist = re.match(r'^\((.+?) \* \((.+?) \+ (.+?)\)\)$', b)
    m_expand = re.match(r'^\(\((.+?) \* (.+?)\) \+ \((.+?) \* (.+?)\)\)$', a)
    if m_dist and m_expand:
        da, db, dc = m_dist.group(1), m_dist.group(2), m_dist.group(3)
        ea1, eb, ea2, ec = (m_expand.group(1), m_expand.group(2),
                            m_expand.group(3), m_expand.group(4))
        if da == ea1 == ea2 and db == eb and dc == ec:
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.FP_DISTRIBUTIVITY,
                input_stratum=InputStratum.LARGE_MAGNITUDE,
                description="FP distributivity fails: a*(b+c) ≠ a*b + a*c",
                trigger_values={"a": "1e15", "b": "1.0000001", "c": "-1.0"},
                kernel_a_output="differs by ULP(s)",
                kernel_b_output="differs by ULP(s)",
            )
    return None


def _check_division_chain(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """a/b/c  vs  a/(b*c)  (intermediate division precision)."""
    m1 = re.match(r'^\(\((.+?) / (.+?)\) / (.+)\)$', a)
    m2 = re.match(r'^\((.+?) / \((.+?) \* (.+)\)\)$', b)
    if m1 and m2:
        a1, b1, c1 = m1.group(1), m1.group(2), m1.group(3)
        a2, b2, c2 = m2.group(1), m2.group(2), m2.group(3)
        if a1 == a2 and b1 == b2 and c1 == c2:
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.DIVISION_HAZARD,
                input_stratum=InputStratum.PRECISION_BOUNDARY,
                description="a/b/c ≠ a/(b*c): intermediate division loses precision",
                trigger_values={"a": "1.0", "b": "3.0", "c": "7.0"},
                kernel_a_output="differs at ULP level",
                kernel_b_output="differs at ULP level",
            )
    # Reversed
    m1 = re.match(r'^\(\((.+?) / (.+?)\) / (.+)\)$', b)
    m2 = re.match(r'^\((.+?) / \((.+?) \* (.+)\)\)$', a)
    if m1 and m2:
        a1, b1, c1 = m1.group(1), m1.group(2), m1.group(3)
        a2, b2, c2 = m2.group(1), m2.group(2), m2.group(3)
        if a1 == a2 and b1 == b2 and c1 == c2:
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.DIVISION_HAZARD,
                input_stratum=InputStratum.PRECISION_BOUNDARY,
                description="a/b/c ≠ a/(b*c): intermediate division loses precision",
                trigger_values={"a": "1.0", "b": "3.0", "c": "7.0"},
                kernel_a_output="differs at ULP level",
                kernel_b_output="differs at ULP level",
            )
    return None


def _check_divide_multiply_roundtrip(
    a: str, b: str,
) -> Optional[EdgeCaseCounterexample]:
    """(a/b)*b  vs  a  (round-trip fails for b=0, precision loss)."""
    m = re.match(r'^\(\((.+?) / (.+?)\) \* (.+)\)$', a)
    if m and m.group(2) == m.group(3) and _is_load(m.group(1)) and _is_load(b):
        if _load_name(m.group(1)) == _load_name(b):
            v = _load_name(m.group(2))
            x = _load_name(m.group(1))
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.DIVISION_HAZARD,
                input_stratum=InputStratum.ZERO,
                description=f"({x}/{v})*{v} ≠ {x} when {v}=0 (NaN) or precision loss",
                trigger_values={x: "1.0", v: "0.0"},
                kernel_a_output="NaN",
                kernel_b_output="1.0",
            )
    m = re.match(r'^\(\((.+?) / (.+?)\) \* (.+)\)$', b)
    if m and m.group(2) == m.group(3) and _is_load(m.group(1)) and _is_load(a):
        if _load_name(m.group(1)) == _load_name(a):
            v = _load_name(m.group(2))
            x = _load_name(m.group(1))
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.DIVISION_HAZARD,
                input_stratum=InputStratum.ZERO,
                description=f"({x}/{v})*{v} ≠ {x} when {v}=0 (NaN) or precision loss",
                trigger_values={x: "1.0", v: "0.0"},
                kernel_a_output="1.0",
                kernel_b_output="NaN",
            )
    return None


def _check_reciprocal_multiply(
    a: str, b: str,
) -> Optional[EdgeCaseCounterexample]:
    """a/b  vs  a*(1/b)  (reciprocal precision loss)."""
    m_div = re.match(r'^\((.+?) / (.+)\)$', a)
    m_recip = re.match(r'^\((.+?) \* \(1\.0 / (.+)\)\)$', b)
    if m_div and m_recip:
        if m_div.group(1) == m_recip.group(1) and m_div.group(2) == m_recip.group(2):
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.DIVISION_HAZARD,
                input_stratum=InputStratum.PRECISION_BOUNDARY,
                description="a/b ≠ a*(1/b): reciprocal approximation introduces error",
                trigger_values={"a": "1.0", "b": "3.0"},
                kernel_a_output="0.3333... (correctly rounded)",
                kernel_b_output="0.3333... (double rounding)",
            )
    m_div = re.match(r'^\((.+?) / (.+)\)$', b)
    m_recip = re.match(r'^\((.+?) \* \(1\.0 / (.+)\)\)$', a)
    if m_div and m_recip:
        if m_div.group(1) == m_recip.group(1) and m_div.group(2) == m_recip.group(2):
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.DIVISION_HAZARD,
                input_stratum=InputStratum.PRECISION_BOUNDARY,
                description="a/b ≠ a*(1/b): reciprocal approximation introduces error",
                trigger_values={"a": "1.0", "b": "3.0"},
                kernel_a_output="double-rounded",
                kernel_b_output="correctly rounded",
            )
    return None


def _check_square_diff_vs_product(
    a: str, b: str,
) -> Optional[EdgeCaseCounterexample]:
    """a²−b²  vs  (a+b)(a−b)  (algebraic identity, FP differs)."""
    m_sq = re.match(r'^\(\((.+?) \* \1\) - \((.+?) \* \2\)\)$', a)
    m_prod = re.match(r'^\(\((.+?) \+ (.+?)\) \* \((.+?) - (.+?)\)\)$', b)
    if m_sq and m_prod:
        a_var, b_var = m_sq.group(1), m_sq.group(2)
        pa, pb, pc, pd = (m_prod.group(1), m_prod.group(2),
                          m_prod.group(3), m_prod.group(4))
        if a_var == pa == pc and b_var == pb == pd:
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.CANCELLATION,
                input_stratum=InputStratum.LARGE_MAGNITUDE,
                description="a²−b² ≠ (a+b)(a−b) for large a,b (catastrophic cancellation in a²−b²)",
                trigger_values={"a": "1e8+1", "b": "1e8"},
                kernel_a_output="different rounding",
                kernel_b_output="different rounding",
            )
    # Reversed
    m_sq = re.match(r'^\(\((.+?) \* \1\) - \((.+?) \* \2\)\)$', b)
    m_prod = re.match(r'^\(\((.+?) \+ (.+?)\) \* \((.+?) - (.+?)\)\)$', a)
    if m_sq and m_prod:
        a_var, b_var = m_sq.group(1), m_sq.group(2)
        pa, pb, pc, pd = (m_prod.group(1), m_prod.group(2),
                          m_prod.group(3), m_prod.group(4))
        if a_var == pa == pc and b_var == pb == pd:
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.CANCELLATION,
                input_stratum=InputStratum.LARGE_MAGNITUDE,
                description="a²−b² ≠ (a+b)(a−b) for large values",
                trigger_values={"a": "1e8+1", "b": "1e8"},
                kernel_a_output="different rounding",
                kernel_b_output="different rounding",
            )
    return None


def _check_subtract_add_cancel(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """(x - y) + y  vs  x  (catastrophic cancellation, subtraction variant)."""
    m = re.match(r'^\(\((.+) - (.+)\) \+ (.+)\)$', a)
    if m and m.group(2) == m.group(3) and _is_load(m.group(1)) and _is_load(b):
        if _load_name(m.group(1)) == _load_name(b):
            x_var = _load_name(m.group(1))
            y_var = _load_name(m.group(2))
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.CANCELLATION,
                input_stratum=InputStratum.PRECISION_BOUNDARY,
                description=(
                    f"({x_var} - {y_var}) + {y_var} ≠ {x_var} due to "
                    f"catastrophic cancellation when |{y_var}| >> |{x_var}|"
                ),
                trigger_values={x_var: "1e-16", y_var: "1e16"},
                kernel_a_output="0.0 (precision lost)",
                kernel_b_output="1e-16",
            )
    m = re.match(r'^\(\((.+) - (.+)\) \+ (.+)\)$', b)
    if m and m.group(2) == m.group(3) and _is_load(m.group(1)) and _is_load(a):
        if _load_name(m.group(1)) == _load_name(a):
            x_var = _load_name(m.group(1))
            y_var = _load_name(m.group(2))
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.CANCELLATION,
                input_stratum=InputStratum.PRECISION_BOUNDARY,
                description=(
                    f"({x_var} - {y_var}) + {y_var} ≠ {x_var} due to "
                    f"catastrophic cancellation when |{y_var}| >> |{x_var}|"
                ),
                trigger_values={x_var: "1e-16", y_var: "1e16"},
                kernel_a_output="1e-16",
                kernel_b_output="0.0 (precision lost)",
            )
    return None


def _check_complex_fraction(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """a/(b/c) vs (a*c)/b  (complex fraction simplification)."""
    m1 = re.match(r'^\((.+?) / \((.+?) / (.+?)\)\)$', a)
    m2 = re.match(r'^\(\((.+?) \* (.+?)\) / (.+?)\)$', b)
    if m1 and m2:
        a1, b1, c1 = m1.group(1), m1.group(2), m1.group(3)
        a2, c2, b2 = m2.group(1), m2.group(2), m2.group(3)
        if a1 == a2 and b1 == b2 and c1 == c2:
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.OVERFLOW,
                input_stratum=InputStratum.LARGE_MAGNITUDE,
                description=(
                    "a/(b/c) ≠ (a*c)/b: when b is small, b/c underflows to 0 "
                    "(giving Inf/NaN), while a*c may overflow differently"
                ),
                trigger_values={"a": "1.0", "b": "1e-300", "c": "1e-300"},
                kernel_a_output="Inf or NaN (b/c underflow)",
                kernel_b_output="different overflow path",
            )
    m1 = re.match(r'^\((.+?) / \((.+?) / (.+?)\)\)$', b)
    m2 = re.match(r'^\(\((.+?) \* (.+?)\) / (.+?)\)$', a)
    if m1 and m2:
        a1, b1, c1 = m1.group(1), m1.group(2), m1.group(3)
        a2, c2, b2 = m2.group(1), m2.group(2), m2.group(3)
        if a1 == a2 and b1 == b2 and c1 == c2:
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.OVERFLOW,
                input_stratum=InputStratum.LARGE_MAGNITUDE,
                description="a/(b/c) ≠ (a*c)/b: different overflow/underflow paths",
                trigger_values={"a": "1.0", "b": "1e-300", "c": "1e-300"},
                kernel_a_output="different overflow path",
                kernel_b_output="Inf or NaN (b/c underflow)",
            )
    return None


def _check_fraction_addition(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """1/a + 1/b  vs  (a+b)/(a*b)  (fraction addition identity)."""
    m_sum = re.match(r'^\(\(1\.0 / (.+?)\) \+ \(1\.0 / (.+?)\)\)$', a)
    m_frac = re.match(r'^\(\((.+?) \+ (.+?)\) / \((.+?) \* (.+?)\)\)$', b)
    if m_sum and m_frac:
        sa, sb = m_sum.group(1), m_sum.group(2)
        fa, fb, fc, fd = m_frac.group(1), m_frac.group(2), m_frac.group(3), m_frac.group(4)
        if sa == fa == fc and sb == fb == fd:
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.DIVISION_HAZARD,
                input_stratum=InputStratum.ZERO,
                description=(
                    "1/a + 1/b ≠ (a+b)/(a*b): when a or b = 0, "
                    "1/0 = Inf vs 0/(0*b) = NaN"
                ),
                trigger_values={"a": "0.0", "b": "1.0"},
                kernel_a_output="Inf + 1.0 = Inf",
                kernel_b_output="NaN (0*1=0, 1/0=Inf... actually depends on eval order)",
            )
    m_sum = re.match(r'^\(\(1\.0 / (.+?)\) \+ \(1\.0 / (.+?)\)\)$', b)
    m_frac = re.match(r'^\(\((.+?) \+ (.+?)\) / \((.+?) \* (.+?)\)\)$', a)
    if m_sum and m_frac:
        sa, sb = m_sum.group(1), m_sum.group(2)
        fa, fb, fc, fd = m_frac.group(1), m_frac.group(2), m_frac.group(3), m_frac.group(4)
        if sa == fa == fc and sb == fb == fd:
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.DIVISION_HAZARD,
                input_stratum=InputStratum.ZERO,
                description="1/a + 1/b ≠ (a+b)/(a*b): different division-by-zero behavior",
                trigger_values={"a": "0.0", "b": "1.0"},
                kernel_a_output="NaN path",
                kernel_b_output="Inf path",
            )
    return None


def _check_power_vs_multiply(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """x*x*x vs x**3  (intermediate overflow for large x)."""
    # ((x * x) * x) vs (x ** 3)
    m_mul = re.match(r'^\(\((.+?) \* \1\) \* \1\)$', a)
    m_pow = re.match(r'^\((.+?) \*\* 3\)$', b)
    if m_mul and m_pow and m_mul.group(1) == m_pow.group(1):
        var = _load_name(m_mul.group(1)) if _is_load(m_mul.group(1)) else "x"
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.OVERFLOW,
            input_stratum=InputStratum.LARGE_MAGNITUDE,
            description=(
                f"{var}*{var}*{var} ≠ {var}**3: intermediate {var}*{var} may "
                f"overflow to Inf while pow({var},3) uses a different code path"
            ),
            trigger_values={var: "1e200"},
            kernel_a_output="Inf (x*x overflows)",
            kernel_b_output="Inf or different rounding via pow()",
        )
    m_mul = re.match(r'^\(\((.+?) \* \1\) \* \1\)$', b)
    m_pow = re.match(r'^\((.+?) \*\* 3\)$', a)
    if m_mul and m_pow and m_mul.group(1) == m_pow.group(1):
        var = _load_name(m_mul.group(1)) if _is_load(m_mul.group(1)) else "x"
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.OVERFLOW,
            input_stratum=InputStratum.LARGE_MAGNITUDE,
            description=f"{var}**3 vs {var}*{var}*{var}: different overflow behavior",
            trigger_values={var: "1e200"},
            kernel_a_output="Inf or different rounding via pow()",
            kernel_b_output="Inf (x*x overflows)",
        )
    return None


def _check_exp_product_vs_exp_sum(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """exp(a)*exp(b) vs exp(a+b) — one overflows, other doesn't."""
    m_prod = re.match(r'^\(tl\.exp\((.+?)\) \* tl\.exp\((.+?)\)\)$', a)
    m_sum = re.match(r'^tl\.exp\(\((.+?) \+ (.+?)\)\)$', b)
    if m_prod and m_sum:
        pa, pb = m_prod.group(1), m_prod.group(2)
        sa, sb = m_sum.group(1), m_sum.group(2)
        if pa == sa and pb == sb:
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.OVERFLOW,
                input_stratum=InputStratum.LARGE_MAGNITUDE,
                description=(
                    "exp(a)*exp(b) ≠ exp(a+b): exp(a) overflows for large a "
                    "even if a+b is moderate (e.g. a=500, b=-499)"
                ),
                trigger_values={"a": "500.0", "b": "-499.0"},
                kernel_a_output="Inf * exp(-499) (Inf)",
                kernel_b_output="exp(1) ≈ 2.718",
            )
    m_prod = re.match(r'^\(tl\.exp\((.+?)\) \* tl\.exp\((.+?)\)\)$', b)
    m_sum = re.match(r'^tl\.exp\(\((.+?) \+ (.+?)\)\)$', a)
    if m_prod and m_sum:
        pa, pb = m_prod.group(1), m_prod.group(2)
        sa, sb = m_sum.group(1), m_sum.group(2)
        if pa == sa and pb == sb:
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.OVERFLOW,
                input_stratum=InputStratum.LARGE_MAGNITUDE,
                description="exp(a)*exp(b) ≠ exp(a+b): individual exp() may overflow",
                trigger_values={"a": "500.0", "b": "-499.0"},
                kernel_a_output="exp(1) ≈ 2.718",
                kernel_b_output="Inf * exp(-499) (Inf)",
            )
    return None


def _check_function_composition_order(
    a: str, b: str,
) -> Optional[EdgeCaseCounterexample]:
    """Detect f(g(x)) vs g(f(x)) patterns — e.g. sum(|x|) vs |sum(x)|."""
    # tl.sum(tl.abs(x)) vs tl.abs(tl.sum(x))
    m1 = re.search(r'tl\.sum\(tl\.abs\(', a)
    m2 = re.search(r'tl\.abs\(tl\.sum\(', b)
    if m1 and m2:
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.FP_IDENTITY,
            input_stratum=InputStratum.NEGATIVE,
            description=(
                "sum(|x|) ≠ |sum(x)|: for mixed-sign inputs, "
                "sum of absolute values > absolute value of sum"
            ),
            trigger_values={"x": "[1.0, -1.0, 1.0, -1.0, ...]"},
            kernel_a_output="4.0 (sum of abs values)",
            kernel_b_output="0.0 (abs of cancellation)",
        )
    m1 = re.search(r'tl\.sum\(tl\.abs\(', b)
    m2 = re.search(r'tl\.abs\(tl\.sum\(', a)
    if m1 and m2:
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.FP_IDENTITY,
            input_stratum=InputStratum.NEGATIVE,
            description="sum(|x|) ≠ |sum(x)|: triangle inequality is strict for mixed signs",
            trigger_values={"x": "[1.0, -1.0, ...]"},
            kernel_a_output="0.0",
            kernel_b_output="4.0",
        )
    # tl.reduce(..., combine_fn=product) vs tl.exp(tl.sum(tl.log(x)))
    has_reduce = re.search(r'tl\.reduce\(', a) or re.search(r'tl\.reduce\(', b)
    has_exp_sum_log = (
        re.search(r'tl\.exp\(tl\.sum\(tl\.log\(', a)
        or re.search(r'tl\.exp\(tl\.sum\(tl\.log\(', b)
    )
    if has_reduce and has_exp_sum_log:
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.OVERFLOW,
            input_stratum=InputStratum.NEGATIVE,
            description=(
                "prod(x) ≠ exp(sum(log(x))): log(x) is NaN for x<0 and "
                "-Inf for x=0, so exp(sum(log(x))) fails for non-positive inputs"
            ),
            trigger_values={"x": "[-1.0, 2.0, 3.0]"},
            kernel_a_output="-6.0 (actual product)",
            kernel_b_output="NaN (log of negative)",
        )
    return None


# ── Heuristic / generic matchers ─────────────────────────────────────────


def _find_loads_in_expr(expr: str) -> Set[str]:
    """Extract all load variable names from a resolved expression."""
    return set(re.findall(r'«LOAD:(\w+)»', expr))


def _heuristic_arithmetic_diff(
    a: str, b: str,
) -> List[EdgeCaseCounterexample]:
    """Generic heuristic: if expressions share the same loads but differ
    in arithmetic structure, flag potential FP edge cases."""
    results: List[EdgeCaseCounterexample] = []
    loads_a = _find_loads_in_expr(a)
    loads_b = _find_loads_in_expr(b)

    if not loads_a or not loads_b:
        return results

    # Same variables, different computation → likely FP edge case
    if loads_a == loads_b and a != b:
        # Count operators
        ops_a = re.findall(r'[\+\-\*/]', a)
        ops_b = re.findall(r'[\+\-\*/]', b)

        # Check for division in one but not the other
        if '/' in a and '/' not in b:
            results.append(EdgeCaseCounterexample(
                category=EdgeCaseCategory.DIVISION_HAZARD,
                input_stratum=InputStratum.ZERO,
                description="Kernel A uses division, kernel B does not — diverges when divisor is 0",
                trigger_values={v: "0.0" for v in loads_a},
                kernel_a_output="possible NaN/Inf",
                kernel_b_output="finite",
                confidence=0.7,
            ))
        elif '/' in b and '/' not in a:
            results.append(EdgeCaseCounterexample(
                category=EdgeCaseCategory.DIVISION_HAZARD,
                input_stratum=InputStratum.ZERO,
                description="Kernel B uses division, kernel A does not — diverges when divisor is 0",
                trigger_values={v: "0.0" for v in loads_b},
                kernel_a_output="finite",
                kernel_b_output="possible NaN/Inf",
                confidence=0.7,
            ))

        # Different number of operations → different rounding behavior
        if len(ops_a) != len(ops_b):
            results.append(EdgeCaseCounterexample(
                category=EdgeCaseCategory.CANCELLATION,
                input_stratum=InputStratum.PRECISION_BOUNDARY,
                description=(
                    f"Different operation counts ({len(ops_a)} vs {len(ops_b)}): "
                    f"different intermediate roundings"
                ),
                trigger_values={v: "1e15" for v in loads_a},
                kernel_a_output="precision-dependent",
                kernel_b_output="precision-dependent",
                confidence=0.5,
            ))

        # Check for subtraction with same-magnitude operands
        if '-' in a or '-' in b:
            results.append(EdgeCaseCounterexample(
                category=EdgeCaseCategory.CANCELLATION,
                input_stratum=InputStratum.LARGE_MAGNITUDE,
                description="Subtraction present — potential catastrophic cancellation for large inputs",
                trigger_values={v: "1e15" for v in loads_a},
                kernel_a_output="precision-dependent",
                kernel_b_output="precision-dependent",
                confidence=0.4,
            ))

    return results


# ── Mask / load parameter diff analysis ──────────────────────────────────


def _check_load_other_diff(
    ext_a: _ExprExtractor,
    ext_b: _ExprExtractor,
) -> List[EdgeCaseCounterexample]:
    """Detect different ``other=`` defaults in masked loads."""
    results: List[EdgeCaseCounterexample] = []

    # Map loads by position (order of appearance)
    loads_a = list(ext_a.loads.keys())
    loads_b = list(ext_b.loads.keys())

    for i, (la, lb) in enumerate(zip(loads_a, loads_b)):
        other_a = ext_a.load_others.get(la)
        other_b = ext_b.load_others.get(lb)

        if other_a != other_b:
            # At least one has an other= value
            results.append(EdgeCaseCounterexample(
                category=EdgeCaseCategory.MASK_BOUNDARY,
                input_stratum=InputStratum.TILING_BOUNDARY,
                description=(
                    f"Load {i}: different other= defaults "
                    f"({other_a!r} vs {other_b!r}) — "
                    f"masked-out elements get different values at tile boundary"
                ),
                trigger_values={"N": "not a multiple of BLOCK_SIZE"},
                kernel_a_output=f"boundary elements = {other_a}",
                kernel_b_output=f"boundary elements = {other_b}",
            ))

    return results


def _check_mask_presence_diff(
    ext_a: _ExprExtractor,
    ext_b: _ExprExtractor,
) -> List[EdgeCaseCounterexample]:
    """Detect one kernel masking loads/stores while the other doesn't."""
    results: List[EdgeCaseCounterexample] = []

    loads_a = list(ext_a.loads.keys())
    loads_b = list(ext_b.loads.keys())
    for i, (la, lb) in enumerate(zip(loads_a, loads_b)):
        mask_a = ext_a.load_masks.get(la)
        mask_b = ext_b.load_masks.get(lb)
        if bool(mask_a) != bool(mask_b):
            masked = "A" if mask_a else "B"
            results.append(EdgeCaseCounterexample(
                category=EdgeCaseCategory.MASK_BOUNDARY,
                input_stratum=InputStratum.TILING_BOUNDARY,
                description=(
                    f"Load {i}: kernel {masked} is masked, other is not — "
                    f"unmasked load reads garbage at tile boundary"
                ),
                trigger_values={"N": "N % BLOCK_SIZE != 0"},
                kernel_a_output="masked: safe" if mask_a else "unmasked: OOB read",
                kernel_b_output="masked: safe" if mask_b else "unmasked: OOB read",
            ))

    for i in range(min(len(ext_a.store_masks), len(ext_b.store_masks))):
        mask_a = ext_a.store_masks[i]
        mask_b = ext_b.store_masks[i]
        if bool(mask_a) != bool(mask_b):
            masked = "A" if mask_a else "B"
            results.append(EdgeCaseCounterexample(
                category=EdgeCaseCategory.MASK_BOUNDARY,
                input_stratum=InputStratum.TILING_BOUNDARY,
                description=(
                    f"Store {i}: kernel {masked} is masked, other is not — "
                    f"unmasked store writes beyond boundary"
                ),
                trigger_values={"N": "N % BLOCK_SIZE != 0"},
                kernel_a_output="masked: safe" if mask_a else "unmasked: OOB write",
                kernel_b_output="masked: safe" if mask_b else "unmasked: OOB write",
            ))

    return results


# ── tl.where / conditional pattern analysis ──────────────────────────────


def _check_where_vs_arithmetic(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """tl.where(m, x, 0) vs x * m  (Inf * 0 = NaN)."""
    # tl.where(cond, val, 0.0) vs val * cond
    m_where = re.search(r'tl\.where\((.+?), (.+?), 0\.0\)', a)
    if m_where:
        cond, val = m_where.group(1), m_where.group(2)
        # Check if b is like val * cond or (val * cond_float)
        if '*' in b and _is_load(val.strip()):
            return EdgeCaseCounterexample(
                category=EdgeCaseCategory.CONDITIONAL_EDGE,
                input_stratum=InputStratum.INFINITY,
                description=(
                    "tl.where(c, x, 0) ≠ x * c.float(): "
                    "when x=Inf and c=False, first gives 0, second gives Inf*0=NaN"
                ),
                trigger_values={"x": "float('inf')", "c": "False"},
                kernel_a_output="0.0",
                kernel_b_output="NaN",
            )
    m_where = re.search(r'tl\.where\((.+?), (.+?), 0\.0\)', b)
    if m_where and '*' in a:
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.CONDITIONAL_EDGE,
            input_stratum=InputStratum.INFINITY,
            description=(
                "tl.where(c, x, 0) ≠ x * c.float(): "
                "when x=Inf and c=False, where gives 0, multiply gives NaN"
            ),
            trigger_values={"x": "float('inf')", "c": "False"},
            kernel_a_output="NaN",
            kernel_b_output="0.0",
        )
    return None


def _check_max_vs_where(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """tl.maximum(x, 0) vs tl.where(x > 0, x, 0.0) — NaN behavior."""
    has_max_a = re.search(r'tl\.(maximum|math\.max)\(', a)
    has_where_b = re.search(r'tl\.where\(', b)
    if has_max_a and has_where_b:
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.NAN_PROPAGATION,
            input_stratum=InputStratum.NAN,
            description=(
                "tl.maximum(x, 0) propagates NaN, but "
                "tl.where(x > 0, x, 0.0) returns 0.0 for NaN (NaN > 0 is False)"
            ),
            trigger_values={"x": "float('nan')"},
            kernel_a_output="NaN",
            kernel_b_output="0.0",
        )
    has_max_b = re.search(r'tl\.(maximum|math\.max)\(', b)
    has_where_a = re.search(r'tl\.where\(', a)
    if has_max_b and has_where_a:
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.NAN_PROPAGATION,
            input_stratum=InputStratum.NAN,
            description=(
                "tl.maximum propagates NaN; tl.where returns 0 for NaN input"
            ),
            trigger_values={"x": "float('nan')"},
            kernel_a_output="0.0",
            kernel_b_output="NaN",
        )
    return None


def _check_sign_function(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """x / abs(x)  vs  where(x>0, 1, where(x<0, -1, 0))  — x=0 diverges."""
    has_div_abs = re.search(r'/ tl\.(abs|math\.fabs)\(', a) or re.search(r'/ tl\.(abs|math\.fabs)\(', b)
    has_where = 'tl.where' in a or 'tl.where' in b
    if has_div_abs and has_where:
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.DIVISION_HAZARD,
            input_stratum=InputStratum.ZERO,
            description="x/|x| ≠ sign(x) when x=0: division gives NaN, sign gives 0",
            trigger_values={"x": "0.0"},
            kernel_a_output="NaN (if division)",
            kernel_b_output="0.0 (if conditional)",
        )
    return None


def _check_safe_division(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """a/(b+eps)  vs  where(|b|>eps, a/b, 0)  — b=-eps makes first blow up."""
    has_eps_div = re.search(r'/ \(.+? \+ .+?\)', a) or re.search(r'/ \(.+? \+ .+?\)', b)
    has_where = 'tl.where' in a or 'tl.where' in b
    if has_eps_div and has_where:
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.DIVISION_HAZARD,
            input_stratum=InputStratum.NEGATIVE,
            description="a/(b+eps) ≠ safe_div: when b = -eps, denominator is 0",
            trigger_values={"b": "-eps"},
            kernel_a_output="NaN or ±Inf",
            kernel_b_output="0.0 (guarded)",
        )
    return None


def _check_triple_sum_vs_multiply(
    a: str, b: str,
) -> Optional[EdgeCaseCounterexample]:
    """a + a + a  vs  3.0 * a  (triple addition vs multiplication)."""
    # ((LOAD + LOAD) + LOAD) same var vs (3.0 * LOAD)
    m_add = re.match(r'^\(\((.+?) \+ \1\) \+ \1\)$', a)
    m_mul = re.match(r'^\(3\.0 \* (.+)\)$', b)
    if m_add and m_mul and m_add.group(1) == m_mul.group(1):
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.FP_ASSOCIATIVITY,
            input_stratum=InputStratum.PRECISION_BOUNDARY,
            description="a + a + a ≠ 3*a due to different intermediate rounding",
            trigger_values={"a": "large odd value near 2^53"},
            kernel_a_output="different ULP rounding",
            kernel_b_output="different ULP rounding",
        )
    m_add = re.match(r'^\(\((.+?) \+ \1\) \+ \1\)$', b)
    m_mul = re.match(r'^\(3\.0 \* (.+)\)$', a)
    if m_add and m_mul and m_add.group(1) == m_mul.group(1):
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.FP_ASSOCIATIVITY,
            input_stratum=InputStratum.PRECISION_BOUNDARY,
            description="a + a + a ≠ 3*a due to different intermediate rounding",
            trigger_values={"a": "large odd value near 2^53"},
            kernel_a_output="different ULP rounding",
            kernel_b_output="different ULP rounding",
        )
    return None


def _check_square_self_div(a: str, b: str) -> Optional[EdgeCaseCounterexample]:
    """(a*a)/a  vs  a  (a=0 → NaN)."""
    m = re.match(r'^\(\((.+?) \* \1\) / \1\)$', a)
    if m and _is_load(m.group(1)) and _is_load(b) and m.group(1) == b:
        var = _load_name(m.group(1))
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.DIVISION_HAZARD,
            input_stratum=InputStratum.ZERO,
            description=f"({var}*{var})/{var} ≠ {var} when {var}=0 (0/0=NaN)",
            trigger_values={var: "0.0"},
            kernel_a_output="NaN",
            kernel_b_output="0.0",
        )
    m = re.match(r'^\(\((.+?) \* \1\) / \1\)$', b)
    if m and _is_load(m.group(1)) and _is_load(a) and m.group(1) == a:
        var = _load_name(m.group(1))
        return EdgeCaseCounterexample(
            category=EdgeCaseCategory.DIVISION_HAZARD,
            input_stratum=InputStratum.ZERO,
            description=f"({var}*{var})/{var} ≠ {var} when {var}=0 (0/0=NaN)",
            trigger_values={var: "0.0"},
            kernel_a_output="0.0",
            kernel_b_output="NaN",
        )
    return None


# ── Reduction-level analysis ─────────────────────────────────────────────


def _check_reduction_differences(
    ext_a: _ExprExtractor,
    ext_b: _ExprExtractor,
    resolved_a: List[str],
    resolved_b: List[str],
) -> List[EdgeCaseCounterexample]:
    """Detect semantic differences in reduction expressions."""
    results: List[EdgeCaseCounterexample] = []

    # Check if one kernel sums then divides, other divides then sums
    for ra, rb in zip(resolved_a, resolved_b):
        has_sum_div_a = re.search(r'tl\.sum\(.*\).*/', ra)
        has_div_sum_b = re.search(r'tl\.sum\(.*[*/]', rb)
        if has_sum_div_a and has_div_sum_b:
            results.append(EdgeCaseCounterexample(
                category=EdgeCaseCategory.REDUCTION_ORDER,
                input_stratum=InputStratum.PRECISION_BOUNDARY,
                description="sum(x)/N ≠ sum(x/N): different intermediate precision",
                trigger_values={"x_i": "values with large magnitude spread"},
                kernel_a_output="sum-then-divide precision",
                kernel_b_output="divide-then-sum precision",
            ))

    return results


# ── Raw source-level pattern checks ─────────────────────────────────────

def _check_source_patterns(
    source_a: str, source_b: str,
) -> List[EdgeCaseCounterexample]:
    """Check source-level patterns that may not survive expression resolution."""
    results: List[EdgeCaseCounterexample] = []

    src_a = textwrap.dedent(source_a)
    src_b = textwrap.dedent(source_b)

    # tl.where vs tl.maximum/tl.minimum
    if ('tl.maximum' in src_a or 'tl.minimum' in src_a) and 'tl.where' in src_b:
        results.append(EdgeCaseCounterexample(
            category=EdgeCaseCategory.NAN_PROPAGATION,
            input_stratum=InputStratum.NAN,
            description="tl.maximum/minimum propagates NaN; tl.where may not",
            trigger_values={"x": "float('nan')"},
            kernel_a_output="NaN (max/min propagation)",
            kernel_b_output="depends on condition (NaN comparison is False)",
        ))
    elif ('tl.maximum' in src_b or 'tl.minimum' in src_b) and 'tl.where' in src_a:
        results.append(EdgeCaseCounterexample(
            category=EdgeCaseCategory.NAN_PROPAGATION,
            input_stratum=InputStratum.NAN,
            description="tl.maximum/minimum propagates NaN; tl.where may not",
            trigger_values={"x": "float('nan')"},
            kernel_a_output="depends on condition",
            kernel_b_output="NaN (max/min propagation)",
        ))

    # Different nesting order of tl.minimum/tl.maximum (clamp order)
    min_max_a = re.search(r'tl\.minimum\(tl\.maximum\(', src_a)
    max_min_a = re.search(r'tl\.maximum\(tl\.minimum\(', src_a)
    min_max_b = re.search(r'tl\.minimum\(tl\.maximum\(', src_b)
    max_min_b = re.search(r'tl\.maximum\(tl\.minimum\(', src_b)
    if (min_max_a and max_min_b) or (max_min_a and min_max_b):
        results.append(EdgeCaseCounterexample(
            category=EdgeCaseCategory.NAN_PROPAGATION,
            input_stratum=InputStratum.NAN,
            description=(
                "min(max(x, lo), hi) ≠ max(min(x, hi), lo) for NaN: "
                "NaN propagates through inner op, outer op may clamp differently"
            ),
            trigger_values={"x": "float('nan')"},
            kernel_a_output="NaN (propagates through max, then min)",
            kernel_b_output="NaN (propagates differently through min, then max)",
        ))

    # Softplus: one uses tl.where guard, other doesn't
    has_exp_log_a = 'tl.exp(' in src_a and 'tl.log(' in src_a
    has_exp_log_b = 'tl.exp(' in src_b and 'tl.log(' in src_b
    has_where_guard_a = 'tl.where' in src_a and has_exp_log_a
    has_where_guard_b = 'tl.where' in src_b and has_exp_log_b
    if has_exp_log_a and has_where_guard_b and not has_where_guard_a:
        results.append(EdgeCaseCounterexample(
            category=EdgeCaseCategory.OVERFLOW,
            input_stratum=InputStratum.LARGE_MAGNITUDE,
            description=(
                "Unguarded exp(x) overflows for large x (>~709): "
                "log(1+exp(x)) → log(Inf) = Inf ≠ x. "
                "Guarded version bypasses exp for large x"
            ),
            trigger_values={"x": "1000.0"},
            kernel_a_output="Inf (exp overflow)",
            kernel_b_output="1000.0 (guarded)",
        ))
    elif has_exp_log_b and has_where_guard_a and not has_where_guard_b:
        results.append(EdgeCaseCounterexample(
            category=EdgeCaseCategory.OVERFLOW,
            input_stratum=InputStratum.LARGE_MAGNITUDE,
            description="Unguarded exp(x) overflows for large x; guarded version avoids overflow",
            trigger_values={"x": "1000.0"},
            kernel_a_output="1000.0 (guarded)",
            kernel_b_output="Inf (exp overflow)",
        ))

    # exp(a)*exp(b) vs exp(a+b) at source level
    if re.search(r'tl\.exp\(.+?\)\s*\*\s*tl\.exp\(', src_a):
        if not re.search(r'tl\.exp\(.+?\)\s*\*\s*tl\.exp\(', src_b) and 'tl.exp(' in src_b:
            results.append(EdgeCaseCounterexample(
                category=EdgeCaseCategory.OVERFLOW,
                input_stratum=InputStratum.LARGE_MAGNITUDE,
                description="exp(a)*exp(b) overflows individually even when a+b is moderate",
                trigger_values={"a": "500.0", "b": "-499.0"},
                kernel_a_output="Inf*small = Inf",
                kernel_b_output="exp(1) ≈ 2.718",
            ))
    elif re.search(r'tl\.exp\(.+?\)\s*\*\s*tl\.exp\(', src_b):
        if not re.search(r'tl\.exp\(.+?\)\s*\*\s*tl\.exp\(', src_a) and 'tl.exp(' in src_a:
            results.append(EdgeCaseCounterexample(
                category=EdgeCaseCategory.OVERFLOW,
                input_stratum=InputStratum.LARGE_MAGNITUDE,
                description="exp(a)*exp(b) overflows individually even when a+b is moderate",
                trigger_values={"a": "500.0", "b": "-499.0"},
                kernel_a_output="exp(1) ≈ 2.718",
                kernel_b_output="Inf*small = Inf",
            ))

    # abs() vs manual abs via where/multiplication
    has_abs_a = 'tl.abs(' in src_a or 'tl.math.fabs(' in src_a
    has_abs_b = 'tl.abs(' in src_b or 'tl.math.fabs(' in src_b
    has_manual_abs_a = re.search(r'tl\.where\(.+?>=?\s*0', src_a) and '-' in src_a
    has_manual_abs_b = re.search(r'tl\.where\(.+?>=?\s*0', src_b) and '-' in src_b
    if has_abs_a and has_manual_abs_b and not has_abs_b:
        results.append(EdgeCaseCounterexample(
            category=EdgeCaseCategory.SIGN_LOSS,
            input_stratum=InputStratum.ZERO,
            description="tl.abs(-0.0) may give +0.0; where(x>=0, x, -x) preserves -0.0 sign",
            trigger_values={"x": "-0.0"},
            kernel_a_output="+0.0",
            kernel_b_output="-0.0 or +0.0 depending on condition",
        ))
    if has_abs_b and has_manual_abs_a and not has_abs_a:
        results.append(EdgeCaseCounterexample(
            category=EdgeCaseCategory.SIGN_LOSS,
            input_stratum=InputStratum.ZERO,
            description="tl.abs(-0.0) may give +0.0; where(x>=0, x, -x) preserves -0.0 sign",
            trigger_values={"x": "-0.0"},
            kernel_a_output="-0.0 or +0.0 depending on condition",
            kernel_b_output="+0.0",
        ))

    return results


# ═══════════════════════════════════════════════════════════════════════════════
# Main synthesizer
# ═══════════════════════════════════════════════════════════════════════════════


class CounterexampleSynthesizer:
    """Synthesizes edge-case counterexamples for Triton kernel pairs.

    Given two Triton kernel sources that produce identical results on
    *most* random inputs, this synthesizer identifies boundary strata
    of the IEEE 754 input space where the kernels diverge.

    Sheaf-theoretically, this checks whether the natural transformation
    η : Sem_f ⇒ Sem_g extends from the open interior of the input space
    (where both presheaves agree) to its **compactification** including
    special values (NaN, ±Inf, ±0, denormals) and tiling boundaries.
    """

    def synthesize(
        self,
        source_a: str,
        source_b: str,
    ) -> CounterexampleReport:
        """Synthesize counterexamples for a pair of Triton kernels.

        Returns a report containing all detected edge cases where the
        kernels produce different outputs.
        """
        ext_a = _ExprExtractor()
        ext_b = _ExprExtractor()
        ext_a.extract(source_a)
        ext_b.extract(source_b)

        resolved_a = ext_a.resolved_stores()
        resolved_b = ext_b.resolved_stores()

        report = CounterexampleReport(
            kernel_a_expr="; ".join(resolved_a),
            kernel_b_expr="; ".join(resolved_b),
            n_stores_a=len(resolved_a),
            n_stores_b=len(resolved_b),
            structurally_identical=(resolved_a == resolved_b),
        )

        if resolved_a == resolved_b:
            # Expressions are identical — check parameter-level differences
            report.counterexamples.extend(
                _check_load_other_diff(ext_a, ext_b)
            )
            report.counterexamples.extend(
                _check_mask_presence_diff(ext_a, ext_b)
            )
            return report

        # ── Expression-level pattern matching ────────────────────────────
        all_cex: List[EdgeCaseCounterexample] = []

        for ra, rb in zip(resolved_a, resolved_b):
            # Apply each specific pattern matcher
            matchers = [
                _check_self_cancellation,
                _check_self_division,
                _check_zero_multiply,
                _check_zero_addition,
                _check_multiply_divide_cancel,
                _check_add_subtract_cancel,
                _check_subtract_add_cancel,
                _check_reciprocal_roundtrip,
                _check_associativity,
                _check_mult_associativity,
                _check_distributivity,
                _check_division_chain,
                _check_divide_multiply_roundtrip,
                _check_reciprocal_multiply,
                _check_square_diff_vs_product,
                _check_complex_fraction,
                _check_fraction_addition,
                _check_power_vs_multiply,
                _check_exp_product_vs_exp_sum,
                _check_function_composition_order,
                _check_where_vs_arithmetic,
                _check_max_vs_where,
                _check_sign_function,
                _check_safe_division,
                _check_triple_sum_vs_multiply,
                _check_square_self_div,
            ]
            for matcher in matchers:
                cex = matcher(ra, rb)
                if cex is not None:
                    all_cex.append(cex)

            # Heuristic fallback for unmatched differences
            if not any(matcher(ra, rb) is not None for matcher in matchers):
                all_cex.extend(_heuristic_arithmetic_diff(ra, rb))

        # ── Parameter-level checks ───────────────────────────────────────
        all_cex.extend(_check_load_other_diff(ext_a, ext_b))
        all_cex.extend(_check_mask_presence_diff(ext_a, ext_b))

        # ── Reduction-level checks ───────────────────────────────────────
        all_cex.extend(
            _check_reduction_differences(ext_a, ext_b, resolved_a, resolved_b)
        )

        # ── Source-level pattern checks ──────────────────────────────────
        all_cex.extend(_check_source_patterns(source_a, source_b))

        # Deduplicate by (category, stratum) — keep highest confidence
        seen: Dict[Tuple[EdgeCaseCategory, InputStratum], EdgeCaseCounterexample] = {}
        for cex in all_cex:
            key = (cex.category, cex.input_stratum)
            if key not in seen or cex.confidence > seen[key].confidence:
                seen[key] = cex
        report.counterexamples = list(seen.values())

        return report
