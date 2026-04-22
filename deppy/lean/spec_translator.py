"""
deppy.lean.spec_translator — Python spec → Lean 4 proposition translator.

Translates ``@guarantee`` strings and Python type annotations into Lean 4
propositions, theorem statements, and function signatures.  Pure — no Z3,
no side effects.
"""
from __future__ import annotations

import inspect
import re
import typing
from dataclasses import dataclass, field
from typing import Any, Callable, Optional, get_type_hints


# ═══════════════════════════════════════════════════════════════════
#  §1  Data structures
# ═══════════════════════════════════════════════════════════════════

@dataclass
class LeanTheorem:
    """A Lean 4 theorem statement."""
    name: str                       # theorem name
    params: list[str]               # "(x : T)" strings
    preconditions: list[str]        # "(h : P)" strings
    conclusion: str                 # the Lean proposition
    proof: str = "sorry"            # "by omega" / "by simp" / "sorry" etc.
    comment: str = ""               # original Python spec as comment

    def render(self) -> str:
        """Render as a Lean 4 theorem declaration."""
        lines: list[str] = []
        if self.comment:
            lines.append(f"-- Original: \"{self.comment}\"")

        parts = ["theorem", self.name]
        for p in self.params:
            parts.append(p)
        for h in self.preconditions:
            parts.append(h)
        sig = " ".join(parts)
        sig += f" : {self.conclusion} :="
        lines.append(sig)
        lines.append(f"  {self.proof}")
        return "\n".join(lines)


@dataclass
class LeanFunctionSig:
    """A Lean 4 function signature with associated theorems."""
    name: str
    params: list[str]               # "(x : T)" strings
    return_type: str
    theorems: list[LeanTheorem]
    preconditions: list[str]        # "(h : P)" strings

    def render(self) -> str:
        """Render as Lean 4 def + theorems."""
        lines: list[str] = []
        parts = [f"def {self.name}"]
        for p in self.params:
            parts.append(p)
        for h in self.preconditions:
            parts.append(h)
        sig = " ".join(parts)
        sig += f" : {self.return_type} :="
        lines.append(sig)
        lines.append("  sorry")
        lines.append("")
        for thm in self.theorems:
            lines.append(thm.render())
            lines.append("")
        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
#  §2  Python type → Lean 4 type translation
# ═══════════════════════════════════════════════════════════════════

# Greek letters for bare generics
_GREEK = ["α", "β", "γ", "δ", "ε"]


def translate_python_type(annotation: Any) -> str:
    """Convert a Python type annotation to a Lean 4 type string."""
    if annotation is None:
        return "Unit"

    # Handle string annotations
    if isinstance(annotation, str):
        return _translate_string_annotation(annotation)

    # NoneType
    if annotation is type(None):
        return "Unit"

    # Primitive types
    _primitives: dict[type, str] = {
        int: "Int",
        float: "Float",
        bool: "Bool",
        str: "String",
    }
    if isinstance(annotation, type) and annotation in _primitives:
        return _primitives[annotation]

    # typing module generics (e.g. list[int], Optional[str])
    origin = getattr(annotation, "__origin__", None)
    args = getattr(annotation, "__args__", None) or ()

    # Optional[T] — Union[T, None]
    if origin is typing.Union:
        non_none = [a for a in args if a is not type(None)]
        if len(non_none) == 1 and len(args) == 2:
            return f"Option {_paren_if_needed(translate_python_type(non_none[0]))}"
        # General union — not directly representable, use Sum
        parts = [translate_python_type(a) for a in args]
        return " ⊕ ".join(parts)

    if origin is list:
        if args:
            return f"List {_paren_if_needed(translate_python_type(args[0]))}"
        return "List α"

    if origin is set or origin is frozenset:
        if args:
            return f"Finset {_paren_if_needed(translate_python_type(args[0]))}"
        return "Finset α"

    if origin is dict:
        if args and len(args) == 2:
            k = translate_python_type(args[0])
            v = translate_python_type(args[1])
            return f"{k} → {v}"
        return "α → β"

    if origin is tuple:
        if args:
            parts = [translate_python_type(a) for a in args]
            return " × ".join(parts)
        return "α × β"

    # Callable[[A, B], C]
    if origin is getattr(typing, "Callable", None) or _is_callable_origin(origin):
        if args and len(args) >= 2:
            # Python 3.9+: args is flattened (A, B, ..., Ret)
            # where all but the last are parameter types
            if isinstance(args[0], list):
                # Older style: ([A, B], Ret)
                param_types_list, ret = args
                parts = [translate_python_type(p) for p in param_types_list]
            else:
                # Python 3.10+/3.14: (A, B, ..., Ret) flattened
                parts = [translate_python_type(a) for a in args[:-1]]
                ret = args[-1]
            parts.append(translate_python_type(ret))
            return " → ".join(parts)
        return "α → β"

    # Bare generic types (list, dict, set, tuple without parameters)
    if annotation is list:
        return "List α"
    if annotation is dict:
        return "α → β"
    if annotation is set or annotation is frozenset:
        return "Finset α"
    if annotation is tuple:
        return "α × β"

    # Optional type from typing module
    if hasattr(typing, "Optional") and annotation is typing.Optional:
        return "Option α"

    # Fallback: use the name
    if hasattr(annotation, "__name__"):
        return annotation.__name__
    return str(annotation)


def _is_callable_origin(origin: Any) -> bool:
    """Check if origin matches collections.abc.Callable."""
    if origin is None:
        return False
    try:
        import collections.abc
        return origin is collections.abc.Callable
    except (ImportError, AttributeError):
        return False


def _translate_string_annotation(s: str) -> str:
    """Translate a string type annotation."""
    s = s.strip()
    mapping = {
        "int": "Int",
        "float": "Float",
        "bool": "Bool",
        "str": "String",
        "None": "Unit",
        "NoneType": "Unit",
    }
    if s in mapping:
        return mapping[s]

    # list[T] pattern
    m = re.match(r"list\[(.+)\]$", s, re.IGNORECASE)
    if m:
        inner = _translate_string_annotation(m.group(1))
        return f"List {_paren_if_needed(inner)}"
    if s.lower() == "list":
        return "List α"

    # Optional[T]
    m = re.match(r"Optional\[(.+)\]$", s)
    if m:
        inner = _translate_string_annotation(m.group(1))
        return f"Option {_paren_if_needed(inner)}"

    # set[T]
    m = re.match(r"set\[(.+)\]$", s, re.IGNORECASE)
    if m:
        inner = _translate_string_annotation(m.group(1))
        return f"Finset {_paren_if_needed(inner)}"
    if s.lower() == "set":
        return "Finset α"

    # dict[K,V]
    m = re.match(r"dict\[(.+),\s*(.+)\]$", s, re.IGNORECASE)
    if m:
        k = _translate_string_annotation(m.group(1))
        v = _translate_string_annotation(m.group(2))
        return f"{k} → {v}"
    if s.lower() == "dict":
        return "α → β"

    # tuple[A,B]
    m = re.match(r"tuple\[(.+)\]$", s, re.IGNORECASE)
    if m:
        parts = [_translate_string_annotation(p.strip()) for p in m.group(1).split(",")]
        return " × ".join(parts)
    if s.lower() == "tuple":
        return "α × β"

    return s


def _paren_if_needed(s: str) -> str:
    """Wrap in parens if the type string contains spaces (compound type)."""
    if " " in s and not (s.startswith("(") and s.endswith(")")):
        return f"({s})"
    return s


# ═══════════════════════════════════════════════════════════════════
#  §3  Guarantee → Lean proposition
# ═══════════════════════════════════════════════════════════════════

def _build_app(func_name: str, param_names: list[str]) -> str:
    """Build a Lean function application string: ``f x y z``."""
    if param_names:
        return f"({func_name} {' '.join(param_names)})"
    return f"({func_name})"


# Each pattern: (regex, builder) where builder(match, app, params, ptypes, rtype) → (conclusion, proof)
_GUARANTEE_PATTERNS: list[
    tuple[re.Pattern[str], Callable[..., tuple[str, str]]]
] = []


def _register(pattern: str, flags: int = re.IGNORECASE):
    """Decorator to register a guarantee pattern."""
    def decorator(fn: Callable[..., tuple[str, str]]):
        _GUARANTEE_PATTERNS.append((re.compile(pattern, flags), fn))
        return fn
    return decorator


# ── result >= 0 / result > 0 ──
@_register(r"^result\s*>=\s*0$")
def _geq_zero(m, app, params, ptypes, rtype):
    return f"0 ≤ {app}", "by omega"


@_register(r"^result\s*>\s*0$")
def _gt_zero(m, app, params, ptypes, rtype):
    return f"0 < {app}", "by omega"


@_register(r"^result\s*<=\s*0$")
def _leq_zero(m, app, params, ptypes, rtype):
    return f"{app} ≤ 0", "by omega"


@_register(r"^result\s*<\s*0$")
def _lt_zero(m, app, params, ptypes, rtype):
    return f"{app} < 0", "by omega"


# ── result is sorted ──
@_register(r"^result\s+is\s+sorted$")
def _sorted(m, app, params, ptypes, rtype):
    return f"List.Sorted (· ≤ ·) {app}", "by simp [List.Sorted]"


# ── result has no duplicates ──
@_register(r"^result\s+has\s+no\s+duplicates$")
def _nodup(m, app, params, ptypes, rtype):
    return f"{app}.Nodup", "by simp [List.Nodup]"


# ── result is a permutation of {param} ──
@_register(r"^result\s+is\s+a\s+permutation\s+of\s+(\w+)$")
def _perm(m, app, params, ptypes, rtype):
    param = m.group(1)
    return f"{app}.Perm {param}", "by simp [List.Perm]"


# ── len(result) == len({param}) ──
@_register(r"^len\(result\)\s*==\s*len\((\w+)\)$")
def _len_eq(m, app, params, ptypes, rtype):
    param = m.group(1)
    return f"{app}.length = {param}.length", "by simp [List.length]"


# ── result == {expr} ──
@_register(r"^result\s*==\s*(.+)$")
def _eq_expr(m, app, params, ptypes, rtype):
    expr = m.group(1).strip()
    lean_expr = _python_expr_to_lean(expr, params)
    return f"{app} = {lean_expr}", "by simp"


# ── result is non-empty ──
@_register(r"^result\s+is\s+non[- ]?empty$")
def _nonempty(m, app, params, ptypes, rtype):
    return f"{app} ≠ []", "by simp"


# ── result contains {x} ──
@_register(r"^result\s+contains\s+(\w+)$")
def _contains(m, app, params, ptypes, rtype):
    x = m.group(1)
    return f"{x} ∈ {app}", "by simp [List.mem_iff_get]"


# ── for all x in result, {pred} ──
@_register(r"^for\s+all\s+(\w+)\s+in\s+result\s*,\s*(.+)$")
def _forall(m, app, params, ptypes, rtype):
    var = m.group(1)
    pred = m.group(2).strip()
    lean_pred = _python_pred_to_lean(pred, var, params)
    return f"∀ {var} ∈ {app}, {lean_pred}", "by simp"


# ── all elements of result are positive ──
@_register(r"^all\s+elements?\s+of\s+result\s+are\s+positive$")
def _all_positive(m, app, params, ptypes, rtype):
    return f"∀ x ∈ {app}, 0 < x", "by simp"


# ── all elements of result are non-negative ──
@_register(r"^all\s+elements?\s+of\s+result\s+are\s+non[- ]?negative$")
def _all_nonneg(m, app, params, ptypes, rtype):
    return f"∀ x ∈ {app}, 0 ≤ x", "by simp"


# ── all elements of result are negative ──
@_register(r"^all\s+elements?\s+of\s+result\s+are\s+negative$")
def _all_negative(m, app, params, ptypes, rtype):
    return f"∀ x ∈ {app}, x < 0", "by simp"


# ── all elements of result are {comparison} {value} ──
@_register(r"^all\s+elements?\s+of\s+result\s+are\s+(greater|less|>=?|<=?)\s+(?:than\s+)?(\w+)$")
def _all_cmp(m, app, params, ptypes, rtype):
    cmp = m.group(1)
    val = m.group(2)
    if cmp in ("greater", ">"):
        return f"∀ x ∈ {app}, {val} < x", "by simp"
    if cmp == ">=":
        return f"∀ x ∈ {app}, {val} ≤ x", "by simp"
    if cmp in ("less", "<"):
        return f"∀ x ∈ {app}, x < {val}", "by simp"
    if cmp == "<=":
        return f"∀ x ∈ {app}, x ≤ {val}", "by simp"
    return f"∀ x ∈ {app}, x < {val}", "by simp"


# ── all elements of result are in {param} ──
@_register(r"^all\s+elements?\s+of\s+result\s+are\s+in\s+(\w+)$")
def _all_in(m, app, params, ptypes, rtype):
    s = m.group(1)
    return f"∀ x ∈ {app}, x ∈ {s}", "by simp"


# ── result is a subset of {s} ──
@_register(r"^result\s+is\s+a\s+subset\s+of\s+(\w+)$")
def _subset(m, app, params, ptypes, rtype):
    s = m.group(1)
    return f"{app} ⊆ {s}", "by simp [List.Subset]"


# ── result >= {param} ──
@_register(r"^result\s*>=\s*(\w+)$")
def _geq_param(m, app, params, ptypes, rtype):
    param = m.group(1)
    return f"{param} ≤ {app}", "by omega"


# ── result > {param} ──
@_register(r"^result\s*>\s*(\w+)$")
def _gt_param(m, app, params, ptypes, rtype):
    param = m.group(1)
    return f"{param} < {app}", "by omega"


# ── result <= {param} ──
@_register(r"^result\s*<=\s*(\w+)$")
def _leq_param(m, app, params, ptypes, rtype):
    param = m.group(1)
    return f"{app} ≤ {param}", "by omega"


# ── result < {param} ──
@_register(r"^result\s*<\s*(\w+)$")
def _lt_param(m, app, params, ptypes, rtype):
    param = m.group(1)
    return f"{app} < {param}", "by omega"


def translate_guarantee(
    spec_str: str,
    func_name: str,
    param_names: list[str],
    param_types: dict[str, Any],
    return_type: Any = None,
) -> LeanTheorem:
    """Translate a ``@guarantee`` string into a ``LeanTheorem``.

    Tries each registered pattern in order; falls back to ``sorry``
    with the original spec as a comment.
    """
    spec_str_stripped = spec_str.strip()
    app = _build_app(func_name, param_names)

    lean_params = _make_lean_params(param_names, param_types)
    lean_ret = translate_python_type(return_type) if return_type else "α"

    for pattern, builder in _GUARANTEE_PATTERNS:
        m = pattern.match(spec_str_stripped)
        if m:
            conclusion, proof = builder(m, app, param_names, param_types, return_type)
            return LeanTheorem(
                name=f"{func_name}_spec",
                params=lean_params,
                preconditions=[],
                conclusion=conclusion,
                proof=proof,
                comment=spec_str,
            )

    # Fallback: unparseable guarantee → sorry with comment
    return LeanTheorem(
        name=f"{func_name}_spec",
        params=lean_params,
        preconditions=[],
        conclusion=f"sorry /- {spec_str} -/",
        proof="sorry",
        comment=spec_str,
    )


# ═══════════════════════════════════════════════════════════════════
#  §4  Precondition → Lean hypothesis
# ═══════════════════════════════════════════════════════════════════

# (regex, builder) → hypothesis string
_REQUIRES_PATTERNS: list[
    tuple[re.Pattern[str], Callable[..., str]]
] = []


def _register_req(pattern: str, flags: int = re.IGNORECASE):
    """Decorator to register a requires pattern."""
    def decorator(fn: Callable[..., str]):
        _REQUIRES_PATTERNS.append((re.compile(pattern, flags), fn))
        return fn
    return decorator


# ── n > 0 / n >= 0 ──
@_register_req(r"^(\w+)\s*>\s*0$")
def _req_gt_zero(m, params, ptypes):
    v = m.group(1)
    return f"(h : 0 < {v})"


@_register_req(r"^(\w+)\s*>=\s*0$")
def _req_geq_zero(m, params, ptypes):
    v = m.group(1)
    return f"(h : 0 ≤ {v})"


@_register_req(r"^(\w+)\s*<\s*0$")
def _req_lt_zero(m, params, ptypes):
    v = m.group(1)
    return f"(h : {v} < 0)"


@_register_req(r"^(\w+)\s*<=\s*0$")
def _req_leq_zero(m, params, ptypes):
    v = m.group(1)
    return f"(h : {v} ≤ 0)"


# ── n > m / n >= m ──
@_register_req(r"^(\w+)\s*>\s*(\w+)$")
def _req_gt(m, params, ptypes):
    a, b = m.group(1), m.group(2)
    return f"(h : {b} < {a})"


@_register_req(r"^(\w+)\s*>=\s*(\w+)$")
def _req_geq(m, params, ptypes):
    a, b = m.group(1), m.group(2)
    return f"(h : {b} ≤ {a})"


@_register_req(r"^(\w+)\s*<\s*(\w+)$")
def _req_lt(m, params, ptypes):
    a, b = m.group(1), m.group(2)
    return f"(h : {a} < {b})"


@_register_req(r"^(\w+)\s*<=\s*(\w+)$")
def _req_leq(m, params, ptypes):
    a, b = m.group(1), m.group(2)
    return f"(h : {a} ≤ {b})"


# ── xs is non-empty ──
@_register_req(r"^(\w+)\s+is\s+non[- ]?empty$")
def _req_nonempty(m, params, ptypes):
    v = m.group(1)
    return f"(h : {v} ≠ [])"


# ── x in xs ──
@_register_req(r"^(\w+)\s+in\s+(\w+)$")
def _req_in(m, params, ptypes):
    x, xs = m.group(1), m.group(2)
    return f"(h : {x} ∈ {xs})"


# ── len(xs) > 0 ──
@_register_req(r"^len\((\w+)\)\s*>\s*0$")
def _req_len_gt_zero(m, params, ptypes):
    v = m.group(1)
    return f"(h : 0 < {v}.length)"


# ── len(xs) == n ──
@_register_req(r"^len\((\w+)\)\s*==\s*(\w+)$")
def _req_len_eq(m, params, ptypes):
    v, n = m.group(1), m.group(2)
    return f"(h : {v}.length = {n})"


def translate_requires(
    spec_str: str,
    param_names: list[str],
    param_types: dict[str, Any],
) -> str:
    """Translate a precondition string into a Lean hypothesis string.

    Returns e.g. ``"(h : 0 < n)"``.
    """
    spec_str_stripped = spec_str.strip()

    for pattern, builder in _REQUIRES_PATTERNS:
        m = pattern.match(spec_str_stripped)
        if m:
            return builder(m, param_names, param_types)

    # Fallback
    return f"(h : sorry /- {spec_str} -/)"


# ═══════════════════════════════════════════════════════════════════
#  §5  Full function signature translation
# ═══════════════════════════════════════════════════════════════════

def translate_function_sig(
    fn: Callable[..., Any],
    spec_metadata: Any = None,
) -> LeanFunctionSig:
    """Translate a Python function + spec metadata to a Lean 4 function sig.

    *spec_metadata* should have:
      - ``.guarantees`` : list[str]
      - ``.preconditions`` : list[Callable | str]

    If *spec_metadata* is ``None``, we try to read ``fn._deppy_spec``.
    """
    sig = inspect.signature(fn)

    # Get type hints, falling back gracefully
    try:
        hints = get_type_hints(fn)
    except Exception:
        hints = {}

    param_names: list[str] = []
    param_types: dict[str, Any] = {}
    for pname, p in sig.parameters.items():
        param_names.append(pname)
        ann = hints.get(pname, p.annotation)
        if ann is inspect.Parameter.empty:
            ann = None
        param_types[pname] = ann

    return_type = hints.get("return", sig.return_annotation)
    if return_type is inspect.Signature.empty:
        return_type = None

    lean_params = _make_lean_params(param_names, param_types)
    lean_ret = translate_python_type(return_type) if return_type else "α"

    # Extract spec metadata
    if spec_metadata is None:
        spec_metadata = getattr(fn, "_deppy_spec", None)

    guarantees: list[str] = []
    precondition_strs: list[str] = []

    if spec_metadata is not None:
        guarantees = list(getattr(spec_metadata, "guarantees", []))
        # Extract string preconditions
        for pre in getattr(spec_metadata, "preconditions", []):
            if isinstance(pre, str):
                precondition_strs.append(pre)
            elif callable(pre):
                # Try to get the source of the lambda
                try:
                    src = inspect.getsource(pre).strip()
                    # Extract from lambda: e.g. "lambda xs: len(xs) > 0"
                    lm = re.search(r"lambda\s+\w+\s*:\s*(.+)", src)
                    if lm:
                        precondition_strs.append(lm.group(1).strip().rstrip(",)"))
                except (OSError, TypeError):
                    pass

    # Build precondition hypotheses
    lean_preconds: list[str] = []
    for i, ps in enumerate(precondition_strs):
        hyp = translate_requires(ps, param_names, param_types)
        # Make hypothesis names unique if multiple
        if i > 0:
            hyp = hyp.replace("(h :", f"(h{i} :", 1)
        lean_preconds.append(hyp)

    # Build theorems (one per guarantee)
    func_name = fn.__name__
    theorems: list[LeanTheorem] = []
    for i, g in enumerate(guarantees):
        thm = translate_guarantee(g, func_name, param_names, param_types, return_type)
        # Ensure unique theorem names
        if i > 0:
            thm.name = f"{func_name}_spec_{i}"
        thm.preconditions = list(lean_preconds)
        theorems.append(thm)

    return LeanFunctionSig(
        name=func_name,
        params=lean_params,
        return_type=lean_ret,
        theorems=theorems,
        preconditions=lean_preconds,
    )


# ═══════════════════════════════════════════════════════════════════
#  §6  Helpers
# ═══════════════════════════════════════════════════════════════════

def _make_lean_params(
    param_names: list[str], param_types: dict[str, Any]
) -> list[str]:
    """Build ``["(x : Int)", "(y : Float)"]`` from names + types."""
    result: list[str] = []
    greek_idx = 0
    for name in param_names:
        ann = param_types.get(name)
        if ann is not None:
            lean_t = translate_python_type(ann)
        else:
            # Use a Greek letter for untyped params
            lean_t = _GREEK[greek_idx % len(_GREEK)]
            greek_idx += 1
        result.append(f"({name} : {lean_t})")
    return result


def _python_expr_to_lean(expr: str, params: list[str]) -> str:
    """Best-effort translation of a simple Python expression to Lean.

    Handles arithmetic operators and simple function calls.
    """
    expr = expr.strip()
    # len(x) → x.length
    expr = re.sub(r"len\((\w+)\)", r"\1.length", expr)
    # ** → ^
    expr = expr.replace("**", "^")
    # // → /  (integer division in Lean Int is just /)
    expr = expr.replace("//", "/")
    # != → ≠
    expr = expr.replace("!=", "≠")
    # == → =
    expr = expr.replace("==", "=")
    # abs(x) → Int.natAbs x  (rough approximation)
    expr = re.sub(r"abs\((\w+)\)", r"Int.natAbs \1", expr)
    # max(a, b) → max a b
    expr = re.sub(r"max\((\w+),\s*(\w+)\)", r"max \1 \2", expr)
    # min(a, b) → min a b
    expr = re.sub(r"min\((\w+),\s*(\w+)\)", r"min \1 \2", expr)
    return expr


def _python_pred_to_lean(pred: str, var: str, params: list[str]) -> str:
    """Translate a simple predicate (within ``for all x in result, ...``)."""
    pred = pred.strip()
    # x > 0
    m = re.match(r"^" + re.escape(var) + r"\s*>\s*0$", pred)
    if m:
        return f"0 < {var}"
    m = re.match(r"^" + re.escape(var) + r"\s*>=\s*0$", pred)
    if m:
        return f"0 ≤ {var}"
    m = re.match(r"^" + re.escape(var) + r"\s*<\s*(\w+)$", pred)
    if m:
        return f"{var} < {m.group(1)}"
    m = re.match(r"^" + re.escape(var) + r"\s*<=\s*(\w+)$", pred)
    if m:
        return f"{var} ≤ {m.group(1)}"
    m = re.match(r"^" + re.escape(var) + r"\s*>\s*(\w+)$", pred)
    if m:
        return f"{m.group(1)} < {var}"
    m = re.match(r"^" + re.escape(var) + r"\s*>=\s*(\w+)$", pred)
    if m:
        return f"{m.group(1)} ≤ {var}"
    # x in S
    m = re.match(r"^" + re.escape(var) + r"\s+in\s+(\w+)$", pred)
    if m:
        return f"{var} ∈ {m.group(1)}"
    # fallback: return as-is with simple substitutions
    return _python_expr_to_lean(pred, params)
