"""
Deppy Effect System — Interprocedural Effect Composition (Gap 4)

Builds a call graph for a Python module and composes effects across
function calls.  When a callee declares ``exception_free_when=[cond]``
in its sidecar, and the caller has established that ``cond`` holds at
the call site, the EXCEPTION effect is *not* propagated.

This module strictly extends the per-function effect inference in
``effect_types.py`` — it does not replace it.

Public entry point:
    propagate_effects(module_ast, sidecar_specs=None) -> ModuleEffectGraph

The result records, for each function in the module:
    * its intrinsic conditional exceptions (from EffectAnalyzer)
    * the list of intra-module callees
    * conditional exceptions inherited from callees (with discharge status)
    * a final list of exceptions that can escape the function

Usage::

    import ast
    from deppy.effects.effect_propagation import propagate_effects
    from deppy.proofs.sidecar import SidecarModule

    tree = ast.parse(source)
    sidecar = SidecarModule.from_deppy_file("mymod.deppy")
    graph = propagate_effects(tree, sidecar_specs=sidecar.specs)
    for name, summary in graph.summaries.items():
        print(name, summary.escapes)
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import Optional

from deppy.effects.effect_types import (
    EffectAnalyzer,
    FunctionEffect,
    ConditionalException,
)


@dataclass
class CallSite:
    """A single call from caller to callee found in the module AST."""

    caller: str
    callee: str
    lineno: int
    # Local guards in scope at this call site (extracted from enclosing
    # ``if`` conditions).  Used to discharge callee preconditions.
    local_guards: list[str] = field(default_factory=list)
    # Mapping from callee parameter names to actual argument expressions
    # at the call site, e.g. {"b": "y + 1"} for divide(x, y + 1).
    arg_bindings: dict[str, str] = field(default_factory=dict)


@dataclass
class FunctionSummary:
    """Composed effect summary for one function in the module."""

    name: str
    intrinsic: FunctionEffect
    callees: list[str] = field(default_factory=list)
    inherited: list[ConditionalException] = field(default_factory=list)
    discharged: list[ConditionalException] = field(default_factory=list)
    escapes: list[ConditionalException] = field(default_factory=list)

    @property
    def is_exception_free(self) -> bool:
        return not self.escapes


@dataclass
class ModuleEffectGraph:
    """Module-wide composed effect graph."""

    summaries: dict[str, FunctionSummary] = field(default_factory=dict)
    call_sites: list[CallSite] = field(default_factory=list)

    def exception_free_functions(self) -> list[str]:
        return sorted(n for n, s in self.summaries.items() if s.is_exception_free)

    def unsafe_functions(self) -> list[str]:
        return sorted(n for n, s in self.summaries.items() if not s.is_exception_free)


# ───────────────────────── Helpers ─────────────────────────────────


def _collect_local_guards(parents: list[ast.AST]) -> list[str]:
    """Walk enclosing ``if`` nodes; return their test expressions (best effort).

    A condition is included only if the call site is in the *true* branch.
    """
    guards: list[str] = []
    for i, p in enumerate(parents[:-1]):
        if isinstance(p, ast.If):
            child = parents[i + 1]
            if any(child is c for c in p.body):
                try:
                    guards.append(ast.unparse(p.test))
                except Exception:
                    pass
    return guards


def _call_name(call: ast.Call) -> Optional[str]:
    func = call.func
    if isinstance(func, ast.Name):
        return func.id
    if isinstance(func, ast.Attribute):
        try:
            return ast.unparse(func)
        except Exception:
            return None
    return None


def _find_call_sites(
    func_node: ast.FunctionDef | ast.AsyncFunctionDef,
    module_funcs: set[str],
    func_defs: dict[str, ast.FunctionDef | ast.AsyncFunctionDef],
) -> list[CallSite]:
    """Find calls to other module-local functions inside ``func_node``."""
    sites: list[CallSite] = []
    parent_stack: list[ast.AST] = [func_node]

    class _Visitor(ast.NodeVisitor):
        def generic_visit(self, node: ast.AST) -> None:
            parent_stack.append(node)
            super().generic_visit(node)
            parent_stack.pop()

        def visit_Call(self, node: ast.Call) -> None:
            qual = _qualified_name(node)
            if qual:
                # Match either the qualified name or its last segment
                # (covers ``self.helper()`` and ``mod.helper()``).
                short = _short_name(qual)
                callee = (qual if qual in module_funcs
                          else short if short in module_funcs else None)
                if callee:
                    sites.append(CallSite(
                        caller=func_node.name,
                        callee=callee,
                        lineno=getattr(node, "lineno", 0),
                        local_guards=_collect_local_guards(parent_stack + [node]),
                        arg_bindings=_bind_call_arguments(node, func_defs[callee]),
                    ))
            self.generic_visit(node)

    _Visitor().visit(func_node)
    return sites


def _condition_discharged(cond: str, guards: list[str]) -> bool:
    """Discharge callee precondition against in-scope guards.

    Tries:
      1. Syntactic equality (normalised).
      2. Z3 semantic implication: ``(g1 ∧ … ∧ gN) → cond`` is valid.
    """
    if not cond:
        return False
    norm = cond.replace(" ", "")
    if any(g.replace(" ", "") == norm for g in guards):
        return True
    return _z3_implies(guards, cond)


def _z3_implies(hypotheses: list[str], conclusion: str) -> bool:
    """Best-effort Z3 check that ``∧ hypotheses → conclusion`` is valid.

    Returns False on any failure (Z3 absent, parse failure, unknown).
    """
    if not hypotheses:
        return False
    try:
        from z3 import Solver, Real, Bool, Not, And, sat, unsat  # type: ignore
    except Exception:
        return False
    import re as _re
    idents: set[str] = set()
    for src in [conclusion, *hypotheses]:
        idents.update(_re.findall(r"\b([a-zA-Z_]\w*)\b", src))
    reserved = {
        "True", "False", "None", "and", "or", "not", "if", "else",
        "for", "in", "is", "when",
    }
    names = sorted(idents - reserved)
    z3_env: dict[str, object] = {n: Real(n) for n in names}
    z3_env.update({"True": True, "False": False})

    def _enc(src: str):
        try:
            return eval(src, {"__builtins__": {}}, z3_env)
        except Exception:
            return None

    h_exprs = [_enc(h) for h in hypotheses]
    c_expr = _enc(conclusion)
    if c_expr is None or any(h is None for h in h_exprs):
        return False
    try:
        s = Solver()
        s.add(And(*h_exprs))
        s.add(Not(c_expr))
        return s.check() == unsat
    except Exception:
        return False


def _qualified_name(call: ast.Call) -> Optional[str]:
    """Best-effort name for both ``f()`` and ``self.f()`` / ``mod.f()``."""
    func = call.func
    if isinstance(func, ast.Name):
        return func.id
    if isinstance(func, ast.Attribute):
        try:
            return ast.unparse(func)
        except Exception:
            return None
    return None


def _short_name(qualified: str) -> str:
    """Last segment of ``a.b.c`` style names."""
    return qualified.rsplit(".", 1)[-1]


def _bind_call_arguments(
    call: ast.Call,
    callee_def: ast.FunctionDef | ast.AsyncFunctionDef,
) -> dict[str, str]:
    """Best-effort parameter → actual-expression binding for a call site."""
    params = [a.arg for a in callee_def.args.args]
    bindings: dict[str, str] = {}
    for param, arg in zip(params, call.args):
        try:
            bindings[param] = ast.unparse(arg)
        except Exception:
            pass
    for kw in call.keywords:
        if kw.arg is None:
            continue
        try:
            bindings[kw.arg] = ast.unparse(kw.value)
        except Exception:
            pass
    return bindings


def _substitute_precondition(cond: str, bindings: dict[str, str]) -> str:
    """Substitute actual argument expressions for callee parameter names."""
    import re as _re
    out = cond
    for name in sorted(bindings, key=len, reverse=True):
        expr = bindings[name]
        out = _re.sub(rf"\b{_re.escape(name)}\b", f"({expr})", out)
    return out


# ───────────────────────── Public API ──────────────────────────────


def propagate_effects(
    module_ast: ast.Module,
    sidecar_specs: Optional[dict] = None,
    max_iterations: int = 10,
) -> ModuleEffectGraph:
    """Compose effects across all functions in ``module_ast``.

    Args:
        module_ast: A parsed Python module (from ``ast.parse``).
        sidecar_specs: Optional ``dict[str, ExternalSpec]`` providing
            sidecar declarations (notably ``exception_free_when``) for
            functions defined in this module.
        max_iterations: Worklist iteration cap (cycles converge faster).

    Returns:
        A ``ModuleEffectGraph`` summarising each function's composed effects.
    """
    analyzer = EffectAnalyzer()

    # Pass 1: collect function definitions and intrinsic effects.
    funcs: dict[str, ast.FunctionDef | ast.AsyncFunctionDef] = {}
    intrinsic: dict[str, FunctionEffect] = {}
    for node in module_ast.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            funcs[node.name] = node
            intrinsic[node.name] = analyzer.analyze_function(node)

    module_func_names = set(funcs)

    # Pass 2: collect call sites within each function.
    all_sites: list[CallSite] = []
    sites_by_caller: dict[str, list[CallSite]] = {}
    for name, node in funcs.items():
        sites = _find_call_sites(node, module_func_names, funcs)
        sites_by_caller[name] = sites
        all_sites.extend(sites)

    # Pass 3: initialise summaries.
    summaries: dict[str, FunctionSummary] = {}
    for name, fe in intrinsic.items():
        summaries[name] = FunctionSummary(
            name=name,
            intrinsic=fe,
            callees=sorted({s.callee for s in sites_by_caller[name]}),
            escapes=list(fe.uncaught_exceptions),
        )

    # Pass 4: fixed-point propagation across the call graph.
    for _ in range(max_iterations):
        changed = False
        for name, summary in summaries.items():
            new_inherited: list[ConditionalException] = []
            new_discharged: list[ConditionalException] = []

            for site in sites_by_caller[name]:
                callee_summary = summaries[site.callee]
                # Sidecar precondition for callee, if any.
                pre = []
                if sidecar_specs and site.callee in sidecar_specs:
                    pre = list(getattr(sidecar_specs[site.callee],
                                       "exception_free_when", []) or [])

                pre_satisfied = bool(pre) and all(
                    _condition_discharged(
                        _substitute_precondition(p, site.arg_bindings),
                        site.local_guards,
                    )
                    for p in pre
                )

                for ce in callee_summary.escapes:
                    inherited_ce = ConditionalException(
                        exception_type=ce.exception_type,
                        trigger_condition=ce.trigger_condition,
                        lineno=site.lineno,
                        description=f"via call to {site.callee}: {ce.description}",
                        is_explicit=False,
                        caught=False,
                    )
                    if pre_satisfied:
                        new_discharged.append(inherited_ce)
                    else:
                        new_inherited.append(inherited_ce)

            old_escape_count = len(summary.escapes)
            base = list(summary.intrinsic.uncaught_exceptions)
            summary.inherited = new_inherited
            summary.discharged = new_discharged
            summary.escapes = base + new_inherited

            if len(summary.escapes) != old_escape_count:
                changed = True

        if not changed:
            break

    return ModuleEffectGraph(summaries=summaries, call_sites=all_sites)


__all__ = [
    "CallSite",
    "FunctionSummary",
    "ModuleEffectGraph",
    "propagate_effects",
]
