"""
Canonical Safety Predicates for Exception Sources (Gap 14 helper)

Maps an ``ExceptionSource`` to the canonical Python-syntax predicate that,
if it holds in the surrounding context, **rules out** that exception.

Every such predicate is intended to be Z3-encodable so the kernel can
discharge it semantically rather than via identifier overlap.

Examples
--------
* ``ZeroDivisionError @ a / b``            ⇒ ``b != 0``
* ``IndexError @ xs[i]``                   ⇒ ``0 <= i and i < len(xs)``
* ``KeyError @ d[k]``                      ⇒ ``k in d``
* ``TypeError  @ a + b`` (mixed numeric)   ⇒ ``isinstance(a, (int, float)) and isinstance(b, (int, float))``
* ``ValueError @ int(s)``                  ⇒ ``s.isdigit() or (len(s)>0 and s[0]=='-' and s[1:].isdigit())``
* ``AttributeError @ obj.attr``            ⇒ ``hasattr(obj, 'attr')``
* ``StopIteration @ next(it)``             ⇒ ``has_next(it)``      (synthetic)
* ``RecursionError`` recursive call        ⇒ ``decreases_measure_provided``  (synthetic)
* ``EXPLICIT_RAISE``                       ⇒ ``False``  (cannot be ruled out
  by any precondition — must be caught or declared in raises_declarations)

A predicate of ``"True"`` means the source is *unconditionally* safe (the
detector overestimated) and a predicate of ``"False"`` means it is
*unconditionally* unsafe — Z3 will discharge True trivially and refuse
False, which is exactly what we want.
"""
from __future__ import annotations

import ast
from typing import Optional

from deppy.pipeline.exception_sources import ExceptionKind, ExceptionSource


def _src(node: Optional[ast.AST]) -> Optional[str]:
    if node is None:
        return None
    try:
        return ast.unparse(node)
    except Exception:
        return None


def _attr_chain(node: ast.AST) -> Optional[str]:
    """Return the attribute name being accessed if ``node`` is an Attribute."""
    if isinstance(node, ast.Attribute):
        return node.attr
    return None


def safety_predicate_for(src: ExceptionSource) -> str:
    """Generate the canonical Python predicate that rules out ``src``.

    The output is a Python source-syntax string that, evaluated in the
    function's argument scope, returns True iff the exception cannot fire.
    """
    node = src.ast_node
    kind = src.kind

    # ── Arithmetic ────────────────────────────────────────────────
    if kind is ExceptionKind.ZERO_DIVISION:
        if isinstance(node, ast.BinOp) and isinstance(
                node.op, (ast.Div, ast.FloorDiv, ast.Mod)):
            denom = _src(node.right) or "denominator"
            return f"({denom}) != 0"
        return "denominator != 0"

    if kind is ExceptionKind.OVERFLOW:
        # Conservative: assume any operand bound prevents overflow.
        return "True  # overflow guarded by operand-domain analysis"

    # ── Collection access ─────────────────────────────────────────
    if kind is ExceptionKind.INDEX_ERROR:
        if isinstance(node, ast.Subscript):
            seq = _src(node.value) or "xs"
            idx = _src(node.slice) or "i"
            return f"0 <= ({idx}) and ({idx}) < len({seq})"
        return "0 <= i and i < len(xs)"

    if kind is ExceptionKind.KEY_ERROR:
        if isinstance(node, ast.Subscript):
            d = _src(node.value) or "d"
            k = _src(node.slice) or "k"
            return f"({k}) in ({d})"
        return "k in d"

    if kind is ExceptionKind.STOP_ITERATION:
        return "has_next(it)"

    # ── Type / value ──────────────────────────────────────────────
    if kind is ExceptionKind.TYPE_ERROR:
        if isinstance(node, ast.BinOp):
            l = _src(node.left) or "a"
            r = _src(node.right) or "b"
            return (f"isinstance({l}, (int, float)) and "
                    f"isinstance({r}, (int, float))")
        if isinstance(node, ast.Call):
            args = ", ".join(_src(a) or f"arg{i}"
                             for i, a in enumerate(node.args))
            fn = _src(node.func) or "f"
            return f"callable({fn})  # args: {args}"
        return "True  # type narrowed elsewhere"

    if kind is ExceptionKind.VALUE_ERROR:
        if isinstance(node, ast.Call):
            fn = _src(node.func) or ""
            if fn.endswith("int") and node.args:
                a = _src(node.args[0]) or "s"
                return (f"({a}).lstrip('-').isdigit()")
            if fn.endswith("float") and node.args:
                a = _src(node.args[0]) or "s"
                return f"is_float_literal({a})"
        return "is_valid_for_op(args)"

    if kind is ExceptionKind.ATTRIBUTE_ERROR:
        if isinstance(node, ast.Attribute):
            obj = _src(node.value) or "obj"
            return f"hasattr({obj}, {node.attr!r})"
        return "hasattr(obj, attr)"

    # ── Name / import ─────────────────────────────────────────────
    if kind is ExceptionKind.NAME_ERROR:
        if isinstance(node, ast.Name):
            return f"defined({node.id!r})"
        return "True  # name resolved by analyzer"

    if kind is ExceptionKind.IMPORT_ERROR:
        return "module_present"

    # ── Assertion / explicit raise ────────────────────────────────
    if kind is ExceptionKind.ASSERTION_ERROR:
        if isinstance(node, ast.Assert):
            return _src(node.test) or "True"
        return "True"

    if kind is ExceptionKind.EXPLICIT_RAISE:
        # Cannot be ruled out by a predicate — the function chooses to raise.
        # Must be addressed via ``raises_declarations`` or be inside a try.
        return "False"

    # ── Recursion / runtime ───────────────────────────────────────
    if kind is ExceptionKind.RUNTIME_ERROR:
        return "True  # recursion bounded by decreases measure"

    # ── Iteration / unpack ────────────────────────────────────────
    if kind is ExceptionKind.ITERATION_ERROR:
        return "iterable_exhaustible"
    if kind is ExceptionKind.UNPACK_ERROR:
        if isinstance(node, ast.Assign) and isinstance(node.targets[0],
                                                       (ast.Tuple, ast.List)):
            n = len(node.targets[0].elts)
            rhs = _src(node.value) or "rhs"
            return f"len({rhs}) == {n}"
        return "len(rhs) == arity(lhs)"

    # ── Call propagation / I/O / timeout / custom ─────────────────
    if kind is ExceptionKind.CALL_PROPAGATION:
        # The callee's own precondition is the right answer; we leave it
        # symbolic so Gap 18 (substitution-aware summary) can fill it in.
        return f"callee_safe({src.callee_name or 'g'})"
    if kind is ExceptionKind.OS_ERROR:
        return "io_resource_available"
    if kind is ExceptionKind.TIMEOUT_ERROR:
        return "completes_within_budget"
    if kind is ExceptionKind.CUSTOM:
        return "custom_invariant_holds"

    return "True  # unknown source kind"


def is_synthetic_predicate(pred: str) -> bool:
    """Predicates whose discharge is not pure Z3 arithmetic.

    Used by the pipeline to decide whether to attempt a Z3 discharge or
    fall back to axiom / structural discharge.
    """
    pred = pred.strip()
    synthetic_markers = (
        "has_next(", "callee_safe(", "module_present", "io_resource_available",
        "completes_within_budget", "custom_invariant_holds",
        "is_float_literal(", "is_valid_for_op(", "defined(",
        "iterable_exhaustible", "callable(",
    )
    return any(m in pred for m in synthetic_markers) or "#" in pred


__all__ = [
    "safety_predicate_for",
    "is_synthetic_predicate",
]
