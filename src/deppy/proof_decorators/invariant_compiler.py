from __future__ import annotations

import ast
import inspect
import textwrap
from dataclasses import dataclass
from typing import Callable, Tuple

from deppy.predicates import (
    And,
    BinOp,
    BoolLit,
    Call,
    Comparison,
    FloatLit,
    IntLit,
    IsNone,
    IsNotNone,
    NoneLit,
    Not,
    Or,
    StrLit,
    Var,
)
from deppy.proof_decorators.models import ProofDecoratorConfigurationError


@dataclass(frozen=True)
class CompiledInvariant:
    phase: str
    source: str
    predicate: object
    free_variables: Tuple[str, ...]


_ALLOWED_BINOPS = {
    ast.Add: "+",
    ast.Sub: "-",
    ast.Mult: "*",
    ast.FloorDiv: "//",
    ast.Mod: "%",
}
_ALLOWED_CMPS = {
    ast.Gt: ">",
    ast.GtE: ">=",
    ast.Lt: "<",
    ast.LtE: "<=",
    ast.Eq: "==",
    ast.NotEq: "!=",
}


def compile_invariant(invariant: object, *, phase: str = "auto") -> CompiledInvariant:
    if isinstance(invariant, str):
        source = invariant.strip()
        expr = ast.parse(source, mode="eval").body
    elif callable(invariant):
        source, expr = _callable_source_and_expr(invariant)
    else:
        raise ProofDecoratorConfigurationError("Invariants must be strings or callables")

    predicate = _predicate_from_expr(expr)
    detected_phase = _detect_phase(phase, predicate)
    free_vars = tuple(sorted(predicate.free_variables()))
    return CompiledInvariant(
        phase=detected_phase,
        source=source,
        predicate=predicate,
        free_variables=free_vars,
    )


def _callable_source_and_expr(invariant: Callable[..., object]) -> Tuple[str, ast.AST]:
    try:
        source = textwrap.dedent(inspect.getsource(invariant)).strip()
    except (OSError, IOError) as exc:
        raise ProofDecoratorConfigurationError(
            f"Could not recover invariant source: {exc}"
        ) from exc

    module = ast.parse(source)
    node = module.body[0]
    if isinstance(node, ast.Expr) and isinstance(node.value, ast.Lambda):
        return source, node.value.body
    if isinstance(node, ast.Assign) and isinstance(node.value, ast.Lambda):
        return source, node.value.body
    if isinstance(node, ast.FunctionDef):
        for stmt in node.body:
            if isinstance(stmt, ast.Return):
                return source, stmt.value
    raise ProofDecoratorConfigurationError(
        "Only lambda or single-return invariants are supported"
    )


def _detect_phase(requested: str, predicate: object) -> str:
    if requested in {"pre", "post"}:
        return requested
    free_vars = predicate.free_variables()
    return "post" if "result" in free_vars else "pre"


def _predicate_from_expr(expr: ast.AST) -> object:
    if isinstance(expr, ast.BoolOp):
        values = [_predicate_from_expr(value) for value in expr.values]
        if isinstance(expr.op, ast.And):
            return And(values)
        if isinstance(expr.op, ast.Or):
            return Or(values)
    if isinstance(expr, ast.UnaryOp) and isinstance(expr.op, ast.Not):
        return Not(_predicate_from_expr(expr.operand))
    if isinstance(expr, ast.Compare):
        if len(expr.ops) != 1 or len(expr.comparators) != 1:
            raise ProofDecoratorConfigurationError("Chained comparisons are not supported")
        left = expr.left
        right = expr.comparators[0]
        op = expr.ops[0]
        if isinstance(op, ast.Is):
            if not isinstance(right, ast.Constant) or right.value is not None:
                raise ProofDecoratorConfigurationError("Only 'is None' comparisons are supported")
            return IsNone(_term_from_expr(left))
        if isinstance(op, ast.IsNot):
            if not isinstance(right, ast.Constant) or right.value is not None:
                raise ProofDecoratorConfigurationError(
                    "Only 'is not None' comparisons are supported"
                )
            return IsNotNone(_term_from_expr(left))
        cmp_op = _ALLOWED_CMPS.get(type(op))
        if cmp_op is None:
            raise ProofDecoratorConfigurationError(
                f"Unsupported comparison operator: {type(op).__name__}"
            )
        return Comparison(cmp_op, _term_from_expr(left), _term_from_expr(right))
    raise ProofDecoratorConfigurationError(
        f"Unsupported invariant expression: {ast.dump(expr, include_attributes=False)}"
    )


def _term_from_expr(expr: ast.AST) -> object:
    if isinstance(expr, ast.Name):
        return Var(expr.id)
    if isinstance(expr, ast.Constant):
        if expr.value is None:
            return NoneLit()
        if isinstance(expr.value, bool):
            return BoolLit(expr.value)
        if isinstance(expr.value, int):
            return IntLit(expr.value)
        if isinstance(expr.value, float):
            return FloatLit(expr.value)
        if isinstance(expr.value, str):
            return StrLit(expr.value)
        raise ProofDecoratorConfigurationError(
            f"Unsupported literal invariant value: {expr.value!r}"
        )
    if (
        isinstance(expr, ast.Call)
        and isinstance(expr.func, ast.Name)
        and expr.func.id == "len"
        and len(expr.args) == 1
    ):
        return Call("len", [_term_from_expr(expr.args[0])])
    if isinstance(expr, ast.BinOp):
        op = _ALLOWED_BINOPS.get(type(expr.op))
        if op is None:
            raise ProofDecoratorConfigurationError(
                f"Unsupported binary operator: {type(expr.op).__name__}"
            )
        return BinOp(op, _term_from_expr(expr.left), _term_from_expr(expr.right))
    raise ProofDecoratorConfigurationError(
        f"Unsupported invariant term: {ast.dump(expr, include_attributes=False)}"
    )
