"""Semantic diff via difference presheaf cohomology.

Given two versions of a function (e.g., from a PR diff), compute the
**semantic difference** rather than the textual difference.

The **difference presheaf** D = Hom(Sem_f, Sem_g) has:
  - D(U) = {local natural transformations f|_U → g|_U at site U}
  - H⁰(D) = sites where behavior is unchanged (sections agree)
  - H¹(D) = sites where behavior genuinely differs (obstructions to
    naturality)

This converts a textual diff into a semantic diff:
  "These 5 lines changed, but the behavioral change is only at 2 sites."

Usage:
    from deppy.equivalence.semantic_diff import semantic_diff
    result = semantic_diff(old_source, new_source)
    print(result.summary())
"""

from __future__ import annotations

import ast
import textwrap
from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Optional, Set, Tuple


class DiffKind(Enum):
    """Classification of semantic differences."""
    UNCHANGED = "unchanged"        # Behaviorally equivalent at this site
    REFINED = "refined"            # New version is strictly more refined
    WEAKENED = "weakened"           # New version is strictly less refined
    DIVERGENT = "divergent"        # Incompatible behavior
    ADDED = "added"                # New code path/site added
    REMOVED = "removed"            # Code path/site removed


@dataclass
class SemanticDiffSite:
    """A single site in the semantic diff."""
    kind: DiffKind
    line_old: Optional[int] = None
    line_new: Optional[int] = None
    description: str = ""
    old_behavior: str = ""
    new_behavior: str = ""
    confidence: float = 1.0


@dataclass
class SemanticDiffResult:
    """Result of semantic diff computation.

    H⁰ = number of unchanged behavioral sites.
    H¹ = number of genuinely different behavioral sites.
    """
    function_name: str
    sites: List[SemanticDiffSite] = field(default_factory=list)
    h0_unchanged: int = 0          # Behaviorally equivalent sites
    h1_changed: int = 0            # Genuinely different sites
    textual_lines_changed: int = 0 # Lines that differ textually
    semantic_sites_changed: int = 0 # Sites that differ semantically

    @property
    def semantic_ratio(self) -> float:
        """Ratio of semantic changes to textual changes.

        < 1.0 means many textual changes are cosmetic (refactoring).
        = 1.0 means every textual change is a semantic change.
        > 1.0 shouldn't happen (but could for non-local effects).
        """
        if self.textual_lines_changed == 0:
            return 0.0
        return self.semantic_sites_changed / self.textual_lines_changed

    def summary(self) -> str:
        lines = [
            f"Semantic diff: {self.function_name}",
            f"  Textual changes: {self.textual_lines_changed} lines",
            f"  H⁰ (unchanged behavior): {self.h0_unchanged} sites",
            f"  H¹ (changed behavior): {self.h1_changed} sites",
            f"  Semantic density: {self.semantic_ratio:.1%} "
            f"of textual changes are semantic",
        ]
        for site in self.sites:
            if site.kind != DiffKind.UNCHANGED:
                loc = f"L{site.line_old or '?'}→L{site.line_new or '?'}"
                lines.append(f"  [{site.kind.value}] {loc}: {site.description}")
        return "\n".join(lines)


def semantic_diff(
    old_source: str,
    new_source: str,
    function_name: str = "",
) -> SemanticDiffResult:
    """Compute the semantic diff between two function versions.

    Decomposes each version into behavioral sites (branches, returns,
    operations), aligns them, and classifies each as unchanged/changed.
    """
    old_source = textwrap.dedent(old_source)
    new_source = textwrap.dedent(new_source)

    try:
        old_tree = ast.parse(old_source)
        new_tree = ast.parse(new_source)
    except SyntaxError:
        return SemanticDiffResult(function_name=function_name or "<unknown>")

    # Extract function nodes
    old_func = _find_function(old_tree, function_name)
    new_func = _find_function(new_tree, function_name)

    if old_func is None and new_func is None:
        return SemanticDiffResult(function_name=function_name or "<unknown>")

    fname = function_name or (
        old_func.name if old_func else new_func.name if new_func else "<unknown>")

    if old_func is None:
        # Entire function added
        sites = [SemanticDiffSite(
            kind=DiffKind.ADDED, line_new=new_func.lineno,
            description=f"New function {fname}")]
        return SemanticDiffResult(
            function_name=fname, sites=sites,
            h0_unchanged=0, h1_changed=1, semantic_sites_changed=1)

    if new_func is None:
        # Entire function removed
        sites = [SemanticDiffSite(
            kind=DiffKind.REMOVED, line_old=old_func.lineno,
            description=f"Removed function {fname}")]
        return SemanticDiffResult(
            function_name=fname, sites=sites,
            h0_unchanged=0, h1_changed=1, semantic_sites_changed=1)

    # Extract behavioral sites from both
    old_sites = _extract_behavioral_sites(old_func)
    new_sites = _extract_behavioral_sites(new_func)

    # Also check function-level properties (signature, decorators)
    sig_diff = _compare_signatures(old_func, new_func)
    deco_diff = _compare_decorators(old_func, new_func)

    # Compute textual diff
    old_lines = old_source.splitlines()
    new_lines = new_source.splitlines()
    textual_changed = _count_changed_lines(old_lines, new_lines)

    # Align and compare sites
    diff_sites, h0, h1 = _align_and_compare(old_sites, new_sites)

    # Add signature and decorator diffs
    if sig_diff:
        diff_sites.append(sig_diff)
        h1 += 1
    if deco_diff:
        diff_sites.append(deco_diff)
        h1 += 1

    return SemanticDiffResult(
        function_name=fname,
        sites=diff_sites,
        h0_unchanged=h0,
        h1_changed=h1,
        textual_lines_changed=textual_changed,
        semantic_sites_changed=h1,
    )


@dataclass
class _BehavioralSite:
    """An extracted behavioral site from a function."""
    kind: str  # "return", "branch", "call", "operation", "loop"
    line: int
    signature: str  # Normalized behavioral signature for comparison
    ast_node: Optional[ast.AST] = None


def _find_function(
    tree: ast.Module, name: str,
) -> Optional[ast.FunctionDef]:
    """Find a function in the AST by name."""
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if not name or node.name == name:
                return node
    return None


def _extract_behavioral_sites(
    func: ast.FunctionDef,
) -> List[_BehavioralSite]:
    """Extract behavioral sites from a function AST.

    Each site represents a point where the function's observable
    behavior can diverge: returns, branches, calls, operations.
    """
    sites: List[_BehavioralSite] = []

    for node in ast.walk(func):
        if isinstance(node, ast.Return):
            sig = _normalize_return(node)
            sites.append(_BehavioralSite(
                kind="return", line=node.lineno,
                signature=sig, ast_node=node))

        elif isinstance(node, ast.If):
            sig = _normalize_test(node.test)
            sites.append(_BehavioralSite(
                kind="branch", line=node.lineno,
                signature=sig, ast_node=node))

        elif isinstance(node, ast.Call):
            sig = _normalize_call(node)
            sites.append(_BehavioralSite(
                kind="call", line=getattr(node, 'lineno', 0),
                signature=sig, ast_node=node))

        elif isinstance(node, (ast.For, ast.While)):
            sig = f"loop_{node.__class__.__name__}"
            if isinstance(node, ast.For) and isinstance(node.iter, ast.Call):
                sig += f"_{_normalize_call(node.iter)}"
            sites.append(_BehavioralSite(
                kind="loop", line=node.lineno,
                signature=sig, ast_node=node))

        elif isinstance(node, ast.BinOp):
            if isinstance(node.op, (ast.Div, ast.FloorDiv, ast.Mod)):
                sig = f"div_{node.op.__class__.__name__}"
                sites.append(_BehavioralSite(
                    kind="operation", line=getattr(node, 'lineno', 0),
                    signature=sig, ast_node=node))

        elif isinstance(node, ast.Subscript):
            sig = "subscript"
            sites.append(_BehavioralSite(
                kind="operation", line=getattr(node, 'lineno', 0),
                signature=sig, ast_node=node))

        elif isinstance(node, ast.Assign):
            try:
                sig = f"assign_{ast.unparse(node.value)}"
            except Exception:
                sig = "assign_?"
            sites.append(_BehavioralSite(
                kind="assign", line=node.lineno,
                signature=sig, ast_node=node))

    return sites


def _normalize_return(node: ast.Return) -> str:
    """Normalize a return statement for behavioral comparison."""
    if node.value is None:
        return "return_none"
    try:
        return f"return_{ast.unparse(node.value)}"
    except Exception:
        return "return_?"


def _normalize_test(node: ast.expr) -> str:
    """Normalize a branch test for behavioral comparison."""
    try:
        return ast.unparse(node)
    except Exception:
        return "test_?"


def _normalize_call(node: ast.Call) -> str:
    """Normalize a call for behavioral comparison."""
    try:
        if isinstance(node.func, ast.Name):
            return f"call_{node.func.id}_{len(node.args)}"
        if isinstance(node.func, ast.Attribute):
            return f"call_.{node.func.attr}_{len(node.args)}"
        return f"call_{ast.unparse(node.func)}"
    except Exception:
        return "call_?"


def _count_changed_lines(old: List[str], new: List[str]) -> int:
    """Count the number of textually changed lines."""
    # Simple line-by-line comparison
    max_len = max(len(old), len(new))
    changed = 0
    for i in range(max_len):
        old_line = old[i].strip() if i < len(old) else ""
        new_line = new[i].strip() if i < len(new) else ""
        if old_line != new_line:
            changed += 1
    return changed


def _align_and_compare(
    old_sites: List[_BehavioralSite],
    new_sites: List[_BehavioralSite],
) -> Tuple[List[SemanticDiffSite], int, int]:
    """Align behavioral sites and compute the difference presheaf.

    Uses signature matching: sites with the same normalized signature
    in both versions are aligned.  Unmatched sites are additions/removals.

    Returns (diff_sites, h0_count, h1_count).
    """
    diff_sites: List[SemanticDiffSite] = []
    h0 = 0
    h1 = 0

    # Build signature index for new sites
    new_by_sig: Dict[str, List[_BehavioralSite]] = {}
    for s in new_sites:
        new_by_sig.setdefault(s.signature, []).append(s)

    matched_new: Set[int] = set()

    for old_s in old_sites:
        candidates = new_by_sig.get(old_s.signature, [])
        found = False
        for ns in candidates:
            ns_id = id(ns)
            if ns_id not in matched_new:
                matched_new.add(ns_id)
                # Same signature = unchanged behavior
                diff_sites.append(SemanticDiffSite(
                    kind=DiffKind.UNCHANGED,
                    line_old=old_s.line, line_new=ns.line,
                    description=f"{old_s.kind}: {old_s.signature}",
                    old_behavior=old_s.signature,
                    new_behavior=ns.signature))
                h0 += 1
                found = True
                break

        if not found:
            # Try to find a site of the same kind nearby (behavioral change)
            kind_candidates = [
                ns for ns in new_sites
                if ns.kind == old_s.kind and id(ns) not in matched_new]
            if kind_candidates:
                ns = kind_candidates[0]
                matched_new.add(id(ns))
                diff_sites.append(SemanticDiffSite(
                    kind=DiffKind.DIVERGENT,
                    line_old=old_s.line, line_new=ns.line,
                    description=f"{old_s.kind} changed: "
                                f"{old_s.signature} → {ns.signature}",
                    old_behavior=old_s.signature,
                    new_behavior=ns.signature))
                h1 += 1
            else:
                diff_sites.append(SemanticDiffSite(
                    kind=DiffKind.REMOVED,
                    line_old=old_s.line,
                    description=f"Removed {old_s.kind}: {old_s.signature}",
                    old_behavior=old_s.signature))
                h1 += 1

    # Unmatched new sites are additions
    for ns in new_sites:
        if id(ns) not in matched_new:
            diff_sites.append(SemanticDiffSite(
                kind=DiffKind.ADDED,
                line_new=ns.line,
                description=f"Added {ns.kind}: {ns.signature}",
                new_behavior=ns.signature))
            h1 += 1

    return diff_sites, h0, h1


def _compare_signatures(
    old_func: ast.FunctionDef, new_func: ast.FunctionDef,
) -> Optional[SemanticDiffSite]:
    """Compare function signatures (params, defaults, annotations)."""
    try:
        old_sig = ast.unparse(old_func.args)
        new_sig = ast.unparse(new_func.args)
    except Exception:
        old_sig = str(len(old_func.args.args))
        new_sig = str(len(new_func.args.args))

    if old_sig != new_sig:
        return SemanticDiffSite(
            kind=DiffKind.DIVERGENT,
            line_old=old_func.lineno,
            line_new=new_func.lineno,
            description="Signature changed",
            old_behavior=old_sig,
            new_behavior=new_sig,
        )
    return None


def _compare_decorators(
    old_func: ast.FunctionDef, new_func: ast.FunctionDef,
) -> Optional[SemanticDiffSite]:
    """Compare decorator lists."""
    try:
        old_decos = [ast.unparse(d) for d in old_func.decorator_list]
        new_decos = [ast.unparse(d) for d in new_func.decorator_list]
    except Exception:
        old_decos = [str(d) for d in old_func.decorator_list]
        new_decos = [str(d) for d in new_func.decorator_list]

    if old_decos != new_decos:
        return SemanticDiffSite(
            kind=DiffKind.DIVERGENT,
            line_old=old_func.lineno,
            line_new=new_func.lineno,
            description="Decorators changed",
            old_behavior=str(old_decos),
            new_behavior=str(new_decos),
        )
    return None
