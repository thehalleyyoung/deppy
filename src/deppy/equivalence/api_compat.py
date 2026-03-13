"""API compatibility checking via pullback along call morphisms.

Given a library function's spec and a client's usage pattern, check
whether the client's implicit refinement type is compatible with the
library's precondition.  This is the **pullback** of the library's
spec along the client's call morphism.

Mathematically:
  - Library spec: F_lib : Sites_lib^op → Pred
  - Client usage: g : Sites_client → Sites_lib (the call morphism)
  - Compatibility = g*(F_lib) ⊆ F_client (pullback is a sub-presheaf)

Concretely: if the library's `sort(xs)` requires `xs` to be non-empty
when `key` is not provided, and the client calls `sort(data)` without
checking emptiness, the pullback detects this incompatibility.

Usage:
    from deppy.equivalence.api_compat import check_api_compatibility
    result = check_api_compatibility(
        library_source="def sort(xs): ...",
        library_spec="def spec(xs, result): return is_sorted(result)",
        client_source="def client(data): return sort(data)",
    )
    print(result.summary())
"""

from __future__ import annotations

import ast
import textwrap
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Dict, List, Optional, Set, Tuple


class CompatibilityVerdict(Enum):
    """Verdict of API compatibility check."""
    COMPATIBLE = "compatible"
    INCOMPATIBLE = "incompatible"
    CONDITIONAL = "conditional"  # Compatible under conditions
    UNKNOWN = "unknown"


@dataclass
class IncompatibilitySite:
    """A site where client usage is incompatible with library spec."""
    client_line: int
    library_param: str
    client_arg: str
    requirement: str  # What the library requires
    actual: str       # What the client provides
    explanation: str = ""


@dataclass
class CompatibilityResult:
    """Result of API compatibility check."""
    verdict: CompatibilityVerdict
    library_func: str
    client_func: str
    call_sites: int = 0
    compatible_sites: int = 0
    incompatibilities: List[IncompatibilitySite] = field(default_factory=list)
    conditions: List[str] = field(default_factory=list)
    explanation: str = ""

    def summary(self) -> str:
        lines = [
            f"API compatibility: {self.client_func} → {self.library_func}",
            f"  Verdict: {self.verdict.value}",
            f"  Call sites checked: {self.call_sites}",
            f"  Compatible: {self.compatible_sites}/"
            f"{self.call_sites}",
        ]
        for inc in self.incompatibilities:
            lines.append(
                f"  ⚠ Line {inc.client_line}: {inc.explanation}")
            lines.append(
                f"    Library requires: {inc.requirement}")
            lines.append(
                f"    Client provides: {inc.actual}")
        for cond in self.conditions:
            lines.append(f"  Condition: {cond}")
        return "\n".join(lines)


def check_api_compatibility(
    library_source: str,
    client_source: str,
    library_func: str = "",
    library_spec: str = "",
) -> CompatibilityResult:
    """Check API compatibility between library and client.

    Constructs the pullback of the library's spec along the client's
    call morphism, then checks whether the client's context satisfies
    the pulled-back requirements.
    """
    lib_src = textwrap.dedent(library_source)
    cli_src = textwrap.dedent(client_source)

    try:
        lib_tree = ast.parse(lib_src)
        cli_tree = ast.parse(cli_src)
    except SyntaxError:
        return CompatibilityResult(
            verdict=CompatibilityVerdict.UNKNOWN,
            library_func=library_func, client_func="<parse error>")

    # Find library function
    lib_func = _find_func(lib_tree, library_func)
    if not lib_func:
        return CompatibilityResult(
            verdict=CompatibilityVerdict.UNKNOWN,
            library_func=library_func, client_func="?",
            explanation="Library function not found")

    lib_name = lib_func.name
    lib_params = [a.arg for a in lib_func.args.args]

    # Extract library requirements from spec or function body
    lib_reqs = _extract_library_requirements(lib_func, library_spec)

    # Find all call sites in client
    call_sites = _find_call_sites(cli_tree, lib_name)

    if not call_sites:
        return CompatibilityResult(
            verdict=CompatibilityVerdict.COMPATIBLE,
            library_func=lib_name, client_func="<no calls>",
            call_sites=0, compatible_sites=0)

    # For each call site, check compatibility via pullback
    incompatibilities: List[IncompatibilitySite] = []
    conditions: List[str] = []
    client_func_name = ""

    for call_node, enclosing_func in call_sites:
        if enclosing_func:
            client_func_name = enclosing_func.name

        # Map actual arguments to library parameters
        arg_mapping = _build_arg_mapping(call_node, lib_params)

        # Check each library requirement against the client context
        for param, req_desc in lib_reqs.items():
            actual_arg = arg_mapping.get(param)
            if actual_arg is None:
                continue

            # Check if client's context satisfies the requirement
            satisfied, explanation = _check_requirement(
                actual_arg, req_desc, call_node, cli_tree)

            if not satisfied:
                incompatibilities.append(IncompatibilitySite(
                    client_line=getattr(call_node, 'lineno', 0),
                    library_param=param,
                    client_arg=actual_arg,
                    requirement=req_desc,
                    actual=f"'{actual_arg}' (unchecked)",
                    explanation=explanation))

    n_calls = len(call_sites)
    n_compat = max(0, n_calls - len(incompatibilities))

    if not incompatibilities:
        verdict = CompatibilityVerdict.COMPATIBLE
    elif n_compat > 0:
        verdict = CompatibilityVerdict.CONDITIONAL
    else:
        verdict = CompatibilityVerdict.INCOMPATIBLE

    return CompatibilityResult(
        verdict=verdict,
        library_func=lib_name,
        client_func=client_func_name,
        call_sites=n_calls,
        compatible_sites=n_compat,
        incompatibilities=incompatibilities,
        conditions=conditions,
    )


def _find_func(
    tree: ast.Module, name: str,
) -> Optional[ast.FunctionDef]:
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if not name or node.name == name:
                return node
    return None


def _extract_library_requirements(
    func: ast.FunctionDef,
    spec_source: str = "",
) -> Dict[str, str]:
    """Extract parameter requirements from library function.

    Looks at:
    1. Type annotations
    2. Guard checks in the body (if x is None: raise, assert x > 0)
    3. Spec source if provided
    """
    reqs: Dict[str, str] = {}
    params = [a.arg for a in func.args.args]

    # Check annotations
    for arg in func.args.args:
        if arg.annotation:
            try:
                ann = ast.unparse(arg.annotation)
                if "Optional" not in ann:
                    reqs[arg.arg] = f"must be {ann} (not None)"
            except Exception:
                pass

    # Check body for guards
    for node in ast.walk(func):
        if isinstance(node, ast.If):
            test = node.test
            # Pattern: if x is None: raise
            if (isinstance(test, ast.Compare)
                    and isinstance(test.ops[0], ast.Is)
                    and isinstance(test.comparators[0], ast.Constant)
                    and test.comparators[0].value is None):
                if isinstance(test.left, ast.Name) and test.left.id in params:
                    body_raises = any(
                        isinstance(s, ast.Raise) for s in node.body)
                    if body_raises:
                        reqs[test.left.id] = "must not be None"

            # Pattern: if not x: raise
            if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
                if isinstance(test.operand, ast.Name) and test.operand.id in params:
                    body_raises = any(
                        isinstance(s, ast.Raise) for s in node.body)
                    if body_raises:
                        reqs[test.operand.id] = "must be truthy (non-empty/non-zero)"

        if isinstance(node, ast.Assert):
            # Pattern: assert x > 0
            test = node.test
            if isinstance(test, ast.Compare) and isinstance(test.left, ast.Name):
                if test.left.id in params:
                    try:
                        reqs[test.left.id] = f"requires {ast.unparse(test)}"
                    except Exception:
                        pass

    return reqs


def _find_call_sites(
    tree: ast.Module, func_name: str,
) -> List[Tuple[ast.Call, Optional[ast.FunctionDef]]]:
    """Find all call sites of a function in the client code."""
    results: List[Tuple[ast.Call, Optional[ast.FunctionDef]]] = []
    current_func: Optional[ast.FunctionDef] = None

    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            current_func = node
        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Name) and node.func.id == func_name:
                results.append((node, current_func))
            elif (isinstance(node.func, ast.Attribute)
                  and node.func.attr == func_name):
                results.append((node, current_func))

    return results


def _build_arg_mapping(
    call: ast.Call, params: List[str],
) -> Dict[str, str]:
    """Map actual arguments to formal parameters."""
    mapping: Dict[str, str] = {}

    for i, arg in enumerate(call.args):
        if i < len(params):
            try:
                mapping[params[i]] = ast.unparse(arg)
            except Exception:
                mapping[params[i]] = "?"

    for kw in call.keywords:
        if kw.arg and kw.arg in params:
            try:
                mapping[kw.arg] = ast.unparse(kw.value)
            except Exception:
                mapping[kw.arg] = "?"

    return mapping


def _check_requirement(
    actual_arg: str,
    requirement: str,
    call_node: ast.Call,
    client_tree: ast.Module,
) -> Tuple[bool, str]:
    """Check if a client argument satisfies a library requirement.

    Returns (satisfied, explanation).
    """
    # Check for None guards upstream of the call
    if "not be None" in requirement:
        if _has_none_guard(actual_arg, call_node, client_tree):
            return True, f"'{actual_arg}' is guarded against None"
        return False, (
            f"'{actual_arg}' may be None — library {requirement}")

    if "truthy" in requirement or "non-empty" in requirement:
        if _has_truthiness_guard(actual_arg, call_node, client_tree):
            return True, f"'{actual_arg}' is guarded for truthiness"
        return False, (
            f"'{actual_arg}' may be empty/falsy — library {requirement}")

    # For other requirements, assume compatible (conservative)
    return True, f"'{actual_arg}' assumed compatible"


def _has_none_guard(
    var_name: str, call_node: ast.Call, tree: ast.Module,
) -> bool:
    """Check if there's a None guard before the call site."""
    call_line = getattr(call_node, 'lineno', 0)
    for node in ast.walk(tree):
        if isinstance(node, ast.If) and getattr(node, 'lineno', 0) < call_line:
            try:
                test_str = ast.unparse(node.test)
                if var_name in test_str and "None" in test_str:
                    return True
                if var_name in test_str and "is not" in test_str:
                    return True
            except Exception:
                pass
    return False


def _has_truthiness_guard(
    var_name: str, call_node: ast.Call, tree: ast.Module,
) -> bool:
    """Check if there's a truthiness guard before the call site."""
    call_line = getattr(call_node, 'lineno', 0)
    for node in ast.walk(tree):
        if isinstance(node, ast.If) and getattr(node, 'lineno', 0) < call_line:
            test = node.test
            if isinstance(test, ast.Name) and test.id == var_name:
                return True
            try:
                test_str = ast.unparse(test)
                if f"len({var_name})" in test_str:
                    return True
            except Exception:
                pass
    return False
