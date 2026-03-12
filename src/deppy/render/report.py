"""Human-readable analysis report from deppy's sheaf-descent engine.

This module translates the internal analysis (sites, sections, obstructions)
into plain-English output that describes:
- What errors the code might raise and where
- What preconditions would prevent those errors
- What the function's inferred contract is
- What guards the code already has

Usage::

    from deppy.render.report import analyze

    report = analyze('''
    def binary_search(arr, target):
        lo, hi = 0, len(arr) - 1
        while lo <= hi:
            mid = (lo + hi) // 2
            if arr[mid] == target:
                return mid
            elif arr[mid] < target:
                lo = mid + 1
            else:
                hi = mid - 1
        return -1
    ''')

    print(report)
"""

from __future__ import annotations

import ast
import textwrap
from collections import Counter
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

from deppy.core._protocols import (
    Cover,
    LocalSection,
    ObstructionData,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site_cover import SiteCoverSynthesizer
from deppy.kernel.fixed_point import ConvergenceStatus, FixedPointEngine, FixedPointResult
from deppy.library_theories.arithmetic_theory import ArithmeticTheoryPack
from deppy.library_theories.sequence_collection_theory import SequenceCollectionTheoryPack
from deppy.library_theories.nullability_theory import NullabilityTheoryPack


# ---------------------------------------------------------------------------
# Data classes for the report
# ---------------------------------------------------------------------------

@dataclass
class ErrorFinding:
    """A potential runtime error found in the code."""
    error_type: str          # e.g. "IndexError"
    source_expr: str         # e.g. "arr[mid]"
    description: str         # e.g. "arr[mid] may raise IndexError if mid is out of bounds"
    is_guarded: bool         # whether existing code guards against it
    guard_condition: str     # e.g. "lo <= hi" if guarded

@dataclass
class InferredPrecondition:
    """A precondition inferred by backward synthesis."""
    parameter: str           # e.g. "arr"
    condition: str           # e.g. "isinstance(arr, Sequence)"
    reason: str              # e.g. "needed because arr is indexed with arr[mid]"

@dataclass
class InferredPostcondition:
    """A postcondition inferred by forward synthesis."""
    description: str         # e.g. "returns int"
    condition: str           # e.g. "return >= -1"

@dataclass
class GuardInfo:
    """An existing guard in the code."""
    condition: str           # e.g. "lo <= hi"
    protects: str            # e.g. "loop body indexing"
    branch: str              # "true" or "false"

@dataclass
class LoopInfo:
    """Information about a loop."""
    condition: str           # e.g. "lo <= hi"
    variables: List[str]     # loop variables modified


@dataclass
class AnalysisReport:
    """Complete human-readable analysis report for a function."""
    function_name: str
    parameters: List[str]
    num_sites: int
    num_morphisms: int

    errors: List[ErrorFinding] = field(default_factory=list)
    preconditions: List[InferredPrecondition] = field(default_factory=list)
    postconditions: List[InferredPostcondition] = field(default_factory=list)
    guards: List[GuardInfo] = field(default_factory=list)
    loops: List[LoopInfo] = field(default_factory=list)

    convergence: str = ""
    num_obstructions: int = 0
    elapsed_ms: float = 0.0

    def __str__(self) -> str:
        return format_report(self)


# ---------------------------------------------------------------------------
# Analysis entry point
# ---------------------------------------------------------------------------

def analyze(
    source: str,
    *,
    max_iterations: int = 5,
    extra_packs: Optional[Sequence[Any]] = None,
) -> AnalysisReport:
    """Analyze Python source and produce a human-readable report.

    Args:
        source: Python source code (one or more function definitions).
        max_iterations: Max fixed-point iterations.
        extra_packs: Additional theory packs beyond the defaults.

    Returns:
        An AnalysisReport with findings in plain English.
    """
    # Parse to get function name and params
    tree = ast.parse(textwrap.dedent(source))
    func_name = "<module>"
    param_names: List[str] = []
    all_funcs: List[Tuple[str, List[str]]] = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            fn = node.name
            params = [a.arg for a in node.args.args]
            all_funcs.append((fn, params))
            if not param_names:
                func_name = fn
                param_names = params

    # Cover synthesis analyzes the first function it finds
    # For multi-function analysis, run analyze() on each separately

    # Synthesize cover
    synth = SiteCoverSynthesizer()
    cover = synth.synthesize(source)

    # Run fixed-point engine
    engine = FixedPointEngine(max_iterations=max_iterations)
    packs: list = [
        ArithmeticTheoryPack(),
        SequenceCollectionTheoryPack(),
        NullabilityTheoryPack(),
    ]
    if extra_packs:
        packs.extend(extra_packs)
    result = engine.run(cover, theory_packs=packs)

    # Build report from cover + result
    report = _build_report(func_name, param_names, cover, result)
    return report


def analyze_all(
    source: str,
    *,
    max_iterations: int = 5,
    extra_packs: Optional[Sequence[Any]] = None,
) -> str:
    """Analyze all functions in source, returning combined human-readable output."""
    tree = ast.parse(textwrap.dedent(source))
    funcs: List[ast.FunctionDef] = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            funcs.append(node)

    if not funcs:
        return "No functions found in source."

    parts: List[str] = []
    for func in funcs:
        # Extract just this function's source (approximate)
        func_src = ast.get_source_segment(textwrap.dedent(source), func)
        if func_src is None:
            continue
        report = analyze(func_src, max_iterations=max_iterations, extra_packs=extra_packs)
        parts.append(str(report))

    return "\n".join(parts)


# ---------------------------------------------------------------------------
# Report builder — translates sites/sections/obstructions to English
# ---------------------------------------------------------------------------

def _get_meta(site: Any, key: str, default: Any = "") -> Any:
    """Get metadata from a site object."""
    if hasattr(site, 'metadata') and isinstance(site.metadata, dict):
        return site.metadata.get(key, default)
    return default


def _build_report(
    func_name: str,
    param_names: List[str],
    cover: Cover,
    result: FixedPointResult,
) -> AnalysisReport:
    report = AnalysisReport(
        function_name=func_name,
        parameters=param_names,
        num_sites=len(cover.sites),
        num_morphisms=len(cover.morphisms),
        convergence=result.status.value,
        num_obstructions=len(result.obstructions),
        elapsed_ms=result.total_elapsed_ms,
    )

    # Extract error findings from error sites
    _extract_errors(cover, result, report)

    # Extract guards from branch guard sites
    _extract_guards(cover, report)

    # Extract loops from loop header sites
    _extract_loops(cover, report)

    # Infer preconditions from error sites + parameters
    _infer_preconditions(cover, result, report)

    # Consolidate redundant preconditions
    _consolidate_preconditions(report)

    # Infer postconditions from return sites
    _infer_postconditions(cover, result, report)

    return report


def _consolidate_preconditions(report: AnalysisReport) -> None:
    """Remove redundant or overly vague preconditions."""
    # Remove vague "expected_type" preconditions if we have concrete ones
    by_param: Dict[str, List[InferredPrecondition]] = {}
    for pc in report.preconditions:
        by_param.setdefault(pc.parameter, []).append(pc)

    consolidated: List[InferredPrecondition] = []
    for param, pcs in by_param.items():
        concrete = [p for p in pcs if "expected_type" not in p.condition
                    and "expected_attr" not in p.condition]
        vague = [p for p in pcs if "expected_type" in p.condition
                 or "expected_attr" in p.condition]

        # If we have concrete preconditions, drop vague ones
        if concrete:
            # Also deduplicate: isinstance(x, (list, tuple, str)) subsumes
            # hasattr(x, '__len__')
            has_isinstance = any("isinstance" in p.condition for p in concrete)
            if has_isinstance:
                concrete = [p for p in concrete
                            if "hasattr" not in p.condition or "__getitem__" in p.condition]

            # Prefer the most specific isinstance check
            # isinstance(x, (list, tuple, str)) is subsumed by len(x) > 0
            has_len = any("len(" in p.condition for p in concrete)
            if has_len:
                # len(x) > 0 implies isinstance(x, sized) so keep both
                pass

            consolidated.extend(concrete)
        else:
            consolidated.extend(vague)

    report.preconditions = consolidated


def _extract_errors(cover: Cover, result: FixedPointResult, report: AnalysisReport) -> None:
    """Extract human-readable error findings from error sites."""
    for sid in cover.error_sites:
        site = cover.sites.get(sid)
        if site is None:
            continue

        error_kind = _get_meta(site, "error_kind", "RuntimeError")
        source_op = _get_meta(site, "source_op", "unknown operation")
        guarded = _get_meta(site, "guarded", False)
        viability = _get_meta(site, "viability", "")

        # Explicit raises (e.g., "raise TypeError(...)") are intentional
        # validation, not accidental bugs
        is_intentional = viability == "explicit raise" or source_op.startswith("raise ")

        # Build human-readable description
        desc = _error_description(error_kind, source_op, is_intentional)

        report.errors.append(ErrorFinding(
            error_type=error_kind,
            source_expr=source_op,
            description=desc,
            is_guarded=guarded or is_intentional,
            guard_condition="intentional raise" if is_intentional else "",
        ))


def _error_description(error_kind: str, source_op: str, is_intentional: bool = False) -> str:
    """Generate a human-readable description of a potential error."""
    if is_intentional:
        return f"`{source_op}` — intentional validation (caller must satisfy precondition)"

    templates = {
        "TypeError": f"`{source_op}` may raise TypeError if operands have incompatible types",
        "IndexError": f"`{source_op}` may raise IndexError if index is out of bounds",
        "KeyError": f"`{source_op}` may raise KeyError if key is not present",
        "ValueError": f"`{source_op}` may raise ValueError if argument is invalid",
        "ZeroDivisionError": f"`{source_op}` may raise ZeroDivisionError if divisor is zero",
        "AttributeError": f"`{source_op}` may raise AttributeError if attribute does not exist",
        "StopIteration": f"`{source_op}` may raise StopIteration when iterator is exhausted",
        "OverflowError": f"`{source_op}` may raise OverflowError on numeric overflow",
    }
    return templates.get(error_kind, f"`{source_op}` may raise {error_kind}")


def _extract_guards(cover: Cover, report: AnalysisReport) -> None:
    """Extract existing guards from branch guard sites."""
    seen_guards: Set[str] = set()
    for sid in cover.sites:
        if sid.kind != SiteKind.BRANCH_GUARD:
            continue
        site = cover.sites[sid]
        condition = _get_meta(site, "condition_text", "")
        is_true = _get_meta(site, "is_true_branch", True)
        guard_id = _get_meta(site, "guard_id", "")

        if not condition or guard_id in seen_guards:
            continue
        seen_guards.add(guard_id)

        report.guards.append(GuardInfo(
            condition=condition,
            protects=_guess_guard_purpose(condition),
            branch="true" if is_true else "false",
        ))


def _guess_guard_purpose(condition: str) -> str:
    """Guess what a guard condition protects."""
    cond_lower = condition.lower()
    if "none" in cond_lower or "is not none" in cond_lower:
        return "null safety"
    if "isinstance" in cond_lower:
        return "type narrowing"
    if "len(" in cond_lower:
        return "bounds checking"
    if "<" in cond_lower or ">" in cond_lower or "<=" in cond_lower or ">=" in cond_lower:
        return "range checking"
    if "==" in cond_lower:
        return "equality check"
    return "conditional logic"


def _extract_loops(cover: Cover, report: AnalysisReport) -> None:
    """Extract loop info from loop header sites."""
    for sid in cover.sites:
        if sid.kind != SiteKind.LOOP_HEADER_INVARIANT:
            continue
        site = cover.sites[sid]
        condition = _get_meta(site, "loop_variable", "")
        report.loops.append(LoopInfo(
            condition=condition,
            variables=[],
        ))


def _infer_preconditions(
    cover: Cover,
    result: FixedPointResult,
    report: AnalysisReport,
) -> None:
    """Infer preconditions from error sites, parameters, and overlap edges.

    For each error site, we trace overlap edges to find which parameters
    are involved, then generate appropriate preconditions.
    """
    param_set = set(report.parameters)

    # Build a map: error_site -> connected SSA/param sites via overlaps
    error_to_params: Dict[SiteId, Set[str]] = {}
    for a, b in cover.overlaps:
        for err_sid, other_sid in [(a, b), (b, a)]:
            if err_sid.kind == SiteKind.ERROR:
                other_site = cover.sites.get(other_sid)
                if other_site is None:
                    continue
                var_name = _get_meta(other_site, "var_name", "")
                param_name = _get_meta(other_site, "param_name", "")
                connected = var_name or param_name
                if connected and connected in param_set:
                    error_to_params.setdefault(err_sid, set()).add(connected)

    # Trace call_result -> error overlaps, then call_result -> ssa_value -> param
    call_to_errors: Dict[SiteId, Set[SiteId]] = {}
    for a, b in cover.overlaps:
        for call_sid, err_sid in [(a, b), (b, a)]:
            if call_sid.kind == SiteKind.CALL_RESULT and err_sid.kind == SiteKind.ERROR:
                call_to_errors.setdefault(call_sid, set()).add(err_sid)

    # Find which SSA/param sites overlap with call_result sites
    call_to_params: Dict[SiteId, Set[str]] = {}
    for a, b in cover.overlaps:
        for call_sid, other_sid in [(a, b), (b, a)]:
            if call_sid.kind == SiteKind.CALL_RESULT:
                other_site = cover.sites.get(other_sid)
                if other_site:
                    vn = _get_meta(other_site, "var_name", "")
                    pn = _get_meta(other_site, "param_name", "")
                    name = vn or pn
                    if name in param_set:
                        call_to_params.setdefault(call_sid, set()).add(name)

    # Propagate: if call_result is connected to error AND to a param,
    # the param is involved in that error
    for call_sid, err_sids in call_to_errors.items():
        params = call_to_params.get(call_sid, set())
        if not params:
            # If no direct SSA overlap, try to find params via SSA lineage
            # SSA vars like lo_0, hi_0 may derive from params
            _trace_ssa_to_params(cover, call_sid, param_set, params)
        for err_sid in err_sids:
            error_to_params.setdefault(err_sid, set()).update(params)

    # Trace SSA sites connected to errors back to parameters
    for err_sid in cover.error_sites:
        if err_sid in error_to_params and error_to_params[err_sid]:
            continue  # already found params
        connected_ssa = set()
        for a, b in cover.overlaps:
            for e, o in [(a, b), (b, a)]:
                if e == err_sid and o.kind == SiteKind.SSA_VALUE:
                    connected_ssa.add(o)
        # Check if any SSA var derives from a parameter
        for ssa_sid in connected_ssa:
            ssa_site = cover.sites.get(ssa_sid)
            if ssa_site:
                vn = _get_meta(ssa_site, "var_name", "")
                if vn in param_set:
                    error_to_params.setdefault(err_sid, set()).add(vn)
                else:
                    # This SSA var derives from a param indirectly
                    # Trace back through lineage overlaps
                    _trace_ssa_to_params(cover, ssa_sid, param_set,
                                        error_to_params.setdefault(err_sid, set()))

    # For unresolved errors with no params, try the function's main params
    for err_sid in cover.error_sites:
        if err_sid not in error_to_params or not error_to_params[err_sid]:
            site = cover.sites.get(err_sid)
            if site:
                callee = ""
                # Check if connected to a call_result
                for call_sid in call_to_errors:
                    if err_sid in call_to_errors[call_sid]:
                        cs = cover.sites.get(call_sid)
                        callee = _get_meta(cs, "callee_name", "") if cs else ""
                if callee in ("len", "sorted", "iter", "sum", "min", "max"):
                    # These functions typically operate on the first collection-like param
                    if param_names := report.parameters:
                        error_to_params.setdefault(err_sid, set()).add(param_names[0])

    # For each error, generate preconditions for connected parameters
    for err in report.errors:
        if err.is_guarded:
            continue

        # Find the error site ID
        err_sid = None
        for sid in cover.error_sites:
            site = cover.sites.get(sid)
            if site and _get_meta(site, "source_op", "") == err.source_expr:
                if _get_meta(site, "error_kind", "") == err.error_type:
                    err_sid = sid
                    break

        # Get connected parameters (from overlaps or from source expression)
        connected_params = set()
        if err_sid and err_sid in error_to_params:
            connected_params = error_to_params[err_sid]
        # Also check if param name appears in source expression
        for p in param_set:
            if p in err.source_expr:
                connected_params.add(p)

        # If no specific param found, use all params for generic errors
        if not connected_params and err.error_type in ("TypeError", "ValueError"):
            connected_params = param_set

        for param in sorted(connected_params):
            cond, reason = _precondition_for_error(
                param, err.error_type, err.source_expr,
            )
            if cond:
                if not any(pc.parameter == param and pc.condition == cond
                           for pc in report.preconditions):
                    report.preconditions.append(InferredPrecondition(
                        parameter=param,
                        condition=cond,
                        reason=reason,
                    ))


def _trace_ssa_to_params(
    cover: Cover,
    start_sid: SiteId,
    param_set: Set[str],
    out: Set[str],
    visited: Optional[Set[SiteId]] = None,
    depth: int = 0,
) -> None:
    """Trace from a site back through overlaps to find connected parameters."""
    if depth > 5:
        return
    if visited is None:
        visited = set()
    if start_sid in visited:
        return
    visited.add(start_sid)

    for a, b in cover.overlaps:
        for src, dst in [(a, b), (b, a)]:
            if src == start_sid and dst not in visited:
                dst_site = cover.sites.get(dst)
                if dst_site:
                    vn = _get_meta(dst_site, "var_name", "")
                    pn = _get_meta(dst_site, "param_name", "")
                    name = vn or pn
                    if name in param_set:
                        out.add(name)
                    elif dst.kind in (SiteKind.SSA_VALUE, SiteKind.ARGUMENT_BOUNDARY):
                        _trace_ssa_to_params(cover, dst, param_set, out, visited, depth + 1)


def _precondition_for_error(param: str, error_type: str, source_expr: str) -> Tuple[str, str]:
    """Generate a precondition that prevents a specific error."""
    if error_type == "TypeError":
        if "len" in source_expr:
            return (
                f"hasattr({param}, '__len__')",
                f"needed because `{source_expr}` calls len() on {param}",
            )
        if "//" in source_expr or "/" in source_expr or "%" in source_expr:
            return (
                f"isinstance({param}, (int, float))",
                f"needed because `{source_expr}` performs arithmetic on {param}",
            )
        if "[" in source_expr:
            return (
                f"isinstance({param}, (list, tuple, str))",
                f"needed because `{source_expr}` indexes into {param}",
            )
        return (
            f"isinstance({param}, expected_type)",
            f"needed because `{source_expr}` requires specific type for {param}",
        )

    if error_type == "IndexError":
        return (
            f"len({param}) > 0",
            f"needed because `{source_expr}` indexes into {param}",
        )

    if error_type == "KeyError":
        # Only suggest key-in-dict if param is the container being accessed
        if "[" in source_expr and param in source_expr.split("[")[0]:
            return (
                f"key in {param}",
                f"needed because `{source_expr}` accesses key in {param}",
            )
        return ("", "")

    if error_type == "ZeroDivisionError":
        return (
            f"{param} != 0",
            f"needed because `{source_expr}` divides by a value derived from {param}",
        )

    if error_type == "ValueError":
        # ValueError from len() means the object doesn't support len
        if "len" in source_expr:
            return (
                f"isinstance({param}, (list, tuple, str, dict, set))",
                f"needed because len({param}) requires a sized collection",
            )
        return ("", "")

    if error_type == "AttributeError":
        return (
            f"hasattr({param}, expected_attr)",
            f"needed because `{source_expr}` accesses attribute on {param}",
        )

    return ("", "")


def _infer_postconditions(
    cover: Cover,
    result: FixedPointResult,
    report: AnalysisReport,
) -> None:
    """Infer postconditions from return sites."""
    return_count = 0
    for sid in cover.sites:
        if sid.kind == SiteKind.RETURN_OUTPUT_BOUNDARY:
            site = cover.sites[sid]
            is_raise = _get_meta(site, "is_raise", False)
            if not is_raise:
                return_count += 1

    if return_count > 0:
        report.postconditions.append(InferredPostcondition(
            description=f"function has {return_count} return path(s)",
            condition=f"{return_count} return statement(s)",
        ))

    # Check if any return is a raise
    for sid in cover.sites:
        if sid.kind == SiteKind.RETURN_OUTPUT_BOUNDARY:
            site = cover.sites[sid]
            if _get_meta(site, "is_raise", False):
                report.postconditions.append(InferredPostcondition(
                    description="function may raise an exception",
                    condition="raises on some code paths",
                ))
                break


# ---------------------------------------------------------------------------
# Report formatter
# ---------------------------------------------------------------------------

def format_report(report: AnalysisReport) -> str:
    """Format an AnalysisReport as a readable string."""
    lines: List[str] = []

    # Header
    params_str = ", ".join(report.parameters)
    lines.append(f"Analysis of `{report.function_name}({params_str})`")
    lines.append("=" * len(lines[0]))
    lines.append("")

    # Summary
    lines.append(
        f"Analyzed {report.num_sites} observation sites "
        f"with {report.num_morphisms} connections "
        f"in {report.elapsed_ms:.1f}ms."
    )
    lines.append("")

    # Potential errors
    if report.errors:
        unguarded = [e for e in report.errors if not e.is_guarded]
        guarded_by_code = [e for e in report.errors if e.is_guarded and e.guard_condition != "intentional raise"]
        intentional = [e for e in report.errors if e.guard_condition == "intentional raise"]

        if unguarded:
            lines.append(f"Potential runtime errors ({len(unguarded)} unguarded):")
            lines.append("-" * 40)
            for i, err in enumerate(unguarded, 1):
                lines.append(f"  {i}. {err.description}")
            lines.append("")

        if intentional:
            lines.append(f"Intentional validation ({len(intentional)} raises):")
            lines.append("-" * 40)
            for err in intentional:
                lines.append(f"  - {err.description}")
            lines.append("")

        if guarded_by_code:
            lines.append(f"Guarded errors ({len(guarded_by_code)} protected):")
            lines.append("-" * 40)
            for err in guarded_by_code:
                lines.append(f"  - {err.description}")
            lines.append("")

    # Existing guards
    if report.guards:
        lines.append(f"Existing guards ({len(report.guards)} found):")
        lines.append("-" * 40)
        for g in report.guards:
            lines.append(f"  - `{g.condition}` ({g.protects})")
        lines.append("")

    # Loops
    if report.loops:
        lines.append(f"Loops ({len(report.loops)} found):")
        lines.append("-" * 40)
        for loop in report.loops:
            lines.append(f"  - while `{loop.condition}`")
        lines.append("")

    # Inferred preconditions
    if report.preconditions:
        lines.append(f"Inferred preconditions:")
        lines.append("-" * 40)
        for pc in report.preconditions:
            lines.append(f"  @requires {pc.condition}")
            lines.append(f"    reason: {pc.reason}")
        lines.append("")

    # Postconditions
    if report.postconditions:
        lines.append(f"Inferred postconditions:")
        lines.append("-" * 40)
        for pc in report.postconditions:
            lines.append(f"  @ensures {pc.condition}")
        lines.append("")

    # Suggested contract
    lines.append("Suggested contract:")
    lines.append("-" * 40)
    params_str = ", ".join(report.parameters)
    lines.append(f"  def {report.function_name}({params_str}):")
    for pc in report.preconditions:
        lines.append(f"      @requires {pc.condition}")
    if not report.preconditions:
        lines.append(f"      # no inferred preconditions")
    unguarded = [e for e in report.errors if not e.is_guarded]
    if unguarded:
        error_types = sorted(set(e.error_type for e in unguarded))
        lines.append(f"      @raises   {', '.join(error_types)}")
    intentional = [e for e in report.errors if e.guard_condition == "intentional raise"]
    if intentional:
        int_types = sorted(set(e.error_type for e in intentional))
        lines.append(f"      @raises   {', '.join(int_types)}  (intentional)")
    lines.append("")

    return "\n".join(lines)
